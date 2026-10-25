// SPDX-License-Identifier: Apache-2.0
//! The graph: a table of slots, one per output bit, and the instances that own them.
//!
//! Ids are handed out by a bump allocator, so an instance's id is the table size when it was
//! added; slots 0, 1 and 2 hold the three tie cells (the constants). Iteration is in slot order.

use std::collections::HashSet;

use super::instance::{Instance, Kind, Pin};
use super::net::{consecutive, Bundle, ControlNet, Net};

pub type InstId = u32;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Slot {
    Void,
    /// Output bit `offset` of instance `inst`.
    Ref(InstId, u32),
}

#[derive(Clone, Debug)]
pub struct Graph {
    table: Vec<Slot>,
    insts: Vec<Option<Instance>>,
    normalized: bool,
    pub name: String,
}

impl Default for Graph {
    fn default() -> Self {
        Self::new()
    }
}

/// How a replacement must agree with what it replaces (the check itself is a debug aid that
/// never changes the graph, so only the replacement is carried out here).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Equivalence {
    Full,
    Refinement,
    TwoValued,
}

/// A walk over the instances in slot order. The range is the table size when the walk starts:
/// instances added during the walk are not visited; changes to slots not yet reached are seen.
pub struct Instances {
    pos: u32,
    end: u32,
}

impl Instances {
    pub fn next(&mut self, g: &Graph) -> Option<InstId> {
        while self.pos < self.end {
            match g.table[self.pos as usize] {
                Slot::Void => self.pos += 1,
                Slot::Ref(i, 0) => {
                    let inst = g.inst(i);
                    // A heap cell's later slots are skipped as one; an inline cell's are
                    // references at non-zero offsets and pass one by one.
                    self.pos += if inst.inline { 1 } else { inst.slots() };
                    return Some(i);
                }
                Slot::Ref(..) => self.pos += 1,
            }
        }
        None
    }
}

impl Graph {
    pub fn new() -> Self {
        let mut g = Graph { table: Vec::new(), insts: Vec::new(), normalized: false, name: String::new() };
        g.add(Kind::TieLow);
        g.add(Kind::TieHigh);
        g.add(Kind::TieX);
        g
    }

    pub fn table_size(&self) -> u32 {
        self.table.len() as u32
    }

    pub fn inst(&self, id: InstId) -> &Instance {
        self.insts[id as usize].as_ref().expect("a live instance")
    }

    pub fn inst_mut(&mut self, id: InstId) -> &mut Instance {
        self.insts[id as usize].as_mut().expect("a live instance")
    }

    fn alloc(&mut self, count: u32) -> u32 {
        let first = self.table.len() as u32;
        self.table.extend((0..count).map(|_| Slot::Void));
        first
    }

    fn push(&mut self, inst: Instance) -> InstId {
        self.insts.push(Some(inst));
        (self.insts.len() - 1) as InstId
    }

    /// Add an instance; its output nets (one net even for a zero-width cell).
    pub fn add(&mut self, kind: Kind) -> Bundle {
        let inline = kind.fits_inline();
        let id = self.add_as(kind, inline);
        let inst = self.inst(id);
        consecutive(Net(inst.base), inst.slots())
    }

    fn add_as(&mut self, kind: Kind, inline: bool) -> InstId {
        self.normalized = false;
        let slots = kind.output_width().max(1);
        let base = self.alloc(slots);
        let id = self.push(Instance { kind, base, inline, metadata: 0 });
        for i in 0..slots {
            self.table[(base + i) as usize] = Slot::Ref(id, i);
        }
        id
    }

    /// The instance driving `net` and the bit of its output.
    pub fn resolve(&self, net: Net) -> (InstId, u32) {
        match self.table[net.0 as usize] {
            Slot::Ref(i, off) => (i, off),
            Slot::Void => panic!("net %{} has no driver", net.0),
        }
    }

    pub fn base_id(&self, id: InstId) -> u32 {
        self.inst(id).base
    }

    /// The instance's output nets.
    pub fn output(&self, id: InstId) -> Bundle {
        let inst = self.inst(id);
        consecutive(Net(inst.base), inst.output_width())
    }

    /// Pad with empty slots so the next id is `target` (the parser honours declared ids).
    pub fn pad_table_to(&mut self, target: u32) {
        if self.table_size() < target {
            self.alloc(target - self.table_size());
        }
    }

    pub fn instances(&self) -> Instances {
        Instances { pos: 0, end: self.table_size() }
    }

    /// Every instance in slot order, as a list (for walks that do not change the graph).
    pub fn instance_list(&self) -> Vec<InstId> {
        let mut it = self.instances();
        let mut v = Vec::new();
        while let Some(i) = it.next(self) {
            v.push(i);
        }
        v
    }

    /// The same order reversed: the first slot of each instance, last to first.
    pub fn instance_list_reversed(&self) -> Vec<InstId> {
        let mut v = Vec::new();
        for s in self.table.iter().rev() {
            if let Slot::Ref(i, 0) = *s {
                v.push(i);
            }
        }
        v
    }

    /// Move a heap instance to fresh slots and leave a buffer forwarding to them at the old ones.
    fn buffer_heap_output(&mut self, id: InstId) -> InstId {
        assert!(!self.inst(id).inline);
        let old_base = self.inst(id).base;
        let slots = self.inst(id).slots();
        let new_base = self.alloc(slots);
        for i in 0..slots {
            self.table[(new_base + i) as usize] = Slot::Ref(id, i);
        }
        self.inst_mut(id).base = new_base;
        // Built as the wide form whatever its width: a heap cell.
        let buf = self.push(Instance { kind: Kind::Buffer(consecutive(Net(new_base), slots)), base: old_base, inline: false, metadata: 0 });
        for i in 0..slots {
            self.table[(old_base + i) as usize] = Slot::Ref(buf, i);
        }
        buf
    }

    pub fn remove_instance(&mut self, id: InstId) {
        assert!(!self.inst(id).inline);
        let base = self.inst(id).base;
        for i in 0..self.inst(id).slots() {
            self.table[(base + i) as usize] = Slot::Void;
        }
        self.insts[id as usize] = None;
        self.normalized = false;
    }

    /// Make each target bit a buffer of the replacement bit: a buffer's input is rewired, an
    /// inline cell is overwritten in place, a heap cell is relocated behind a forwarding buffer.
    pub fn force_replace(&mut self, target: &[Net], replacement: &[Net]) {
        assert_eq!(target.len(), replacement.len());
        for (&t, &r) in target.iter().zip(replacement) {
            if t == r {
                continue;
            }
            let (id, offset) = self.resolve(t);
            if matches!(self.inst(id).kind, Kind::Buffer(_)) {
                self.inst_mut(id).kind.set(Pin::V(offset), r);
            } else if self.inst(id).inline {
                if offset == 0 {
                    // The slot keeps its instance identity; only its contents change.
                    self.inst_mut(id).kind = Kind::Buffer(vec![r]);
                } else {
                    // A later bit of a wide inline cell: that slot alone becomes a buffer.
                    let buf = self.push(Instance { kind: Kind::Buffer(vec![r]), base: t.0, inline: true, metadata: 0 });
                    self.table[t.0 as usize] = Slot::Ref(buf, 0);
                }
            } else {
                let buf = self.buffer_heap_output(id);
                self.inst_mut(buf).kind.set(Pin::V(offset), r);
            }
            self.normalized = false;
        }
    }

    pub fn replace(&mut self, target: &[Net], replacement: &[Net], _type: Equivalence, _support: &[Net]) {
        self.force_replace(target, replacement);
    }

    pub fn make_names_tentative(&mut self) {
        for id in self.instance_list() {
            if let Kind::Name(n) = &mut self.inst_mut(id).kind {
                n.tentative = true;
            }
        }
    }

    /// A negative control becomes an inverter; a positive one is its net.
    pub fn emit_control(&mut self, cn: ControlNet) -> Net {
        if cn.positive {
            cn.net
        } else {
            self.add(Kind::Not(vec![cn.net]))[0]
        }
    }

    /// Every heap instance owns its slots, every reference has an owner.
    pub fn check_consistency(&self) {
        for (id, inst) in self.insts.iter().enumerate() {
            let Some(inst) = inst else { continue };
            for i in 0..inst.slots() {
                let s = inst.base + i;
                assert!((s as usize) < self.table.len(), "checkConsistency: {} base {} slot {s} out of bounds", inst.kind.keyword(), inst.base);
                assert_eq!(self.table[s as usize], Slot::Ref(id as InstId, i), "checkConsistency: {} base {} slot {s}", inst.kind.keyword(), inst.base);
            }
        }
        for (s, slot) in self.table.iter().enumerate() {
            if let Slot::Ref(i, off) = *slot {
                assert!(self.insts[i as usize].as_ref().is_some_and(|inst| inst.base + off == s as u32), "checkConsistency: orphan reference at {s}");
            }
        }
    }

    /// Topological order: every combinational cell's inputs precede it.
    pub fn check_normalization(&self) {
        for id in self.instance_list() {
            let inst = self.inst(id);
            if matches!(inst.kind, Kind::Output(..) | Kind::LoopBreaker(_)) || inst.kind.has_state() || inst.kind.has_effects() {
                continue;
            }
            for n in inst.kind.inputs() {
                if !n.is_const() && n.0 >= inst.base {
                    panic!("checkNormalization: not in topological order: %{} reads %{}", inst.base, n.0);
                }
            }
        }
    }

    /// Topologically sort the combinational network into a fresh table and drop what nothing
    /// observable reads. Bitwise cells are kept only over their live bit ranges; combinational
    /// loops get a loop breaker. Tentative names survive over the bits that stay live.
    pub fn normalize(&mut self) {
        if self.normalized {
            return;
        }
        self.check_consistency();
        let (live, tentative) = self.liveness();
        let mut n = Normalize::new(self, live);
        n.emit_roots();
        n.dfs_from_effects();
        n.dfs_deferred_stateful();
        n.dfs_remaining_live();
        n.finish(tentative);
        self.check_normalization();
        self.normalized = true;
    }

    /// Liveness from the observable cells and inputs, and the tentative names (which do not keep
    /// anything live by themselves, except an inverter that names a live net's complement).
    fn liveness(&self) -> (Vec<bool>, Vec<Tentative>) {
        let size = self.table.len();
        let mut live = vec![false; size];
        live[..3].fill(true);
        let mut tentative = Vec::new();
        let mut queue: Vec<u32> = Vec::new();
        let mark = |live: &mut Vec<bool>, queue: &mut Vec<u32>, net: Net| {
            if net.is_const() {
                return;
            }
            assert!(!net.is_sentinel());
            if !live[net.0 as usize] {
                live[net.0 as usize] = true;
                queue.push(net.0);
            }
        };
        for id in self.instance_list() {
            let inst = self.inst(id);
            if let Kind::Name(nm) = &inst.kind {
                if nm.tentative {
                    tentative.push(Tentative { name: nm.name.clone(), value: nm.value.clone(), from: nm.from, is_vector: nm.is_vector });
                    continue;
                }
            }
            if inst.kind.has_effects() || matches!(inst.kind, Kind::Input(..)) {
                for bit in self.output(id) {
                    live[bit.0 as usize] = true;
                }
                for net in inst.kind.inputs() {
                    mark(&mut live, &mut queue, net);
                }
            }
        }
        let drain = |live: &mut Vec<bool>, queue: &mut Vec<u32>| {
            while let Some(slot) = queue.pop() {
                let (id, off) = self.resolve(Net(slot));
                let kind = &self.inst(id).kind;
                for p in kind.slice_pins(off) {
                    mark(live, queue, kind.get(p));
                }
            }
        };
        drain(&mut live, &mut queue);
        // A tentative name on a dead net: strip buffers and inverters back to a live net; keep the
        // last inverter on the way when the polarity is negative, so the name stays valid.
        for tn in &mut tentative {
            for i in 0..tn.value.len() {
                let net = tn.value[i];
                if net.is_const() || live[net.0 as usize] {
                    continue;
                }
                let mut cnet = ControlNet::pos(net);
                let mut last_inverter = Net::SENTINEL;
                loop {
                    let (id, off) = self.resolve(cnet.net);
                    let inst = self.inst(id);
                    match &inst.kind {
                        Kind::Not(a) => {
                            last_inverter = Net(inst.base + off);
                            cnet = ControlNet::with_polarity(a[off as usize], !cnet.positive);
                        }
                        Kind::Buffer(a) => cnet = ControlNet::with_polarity(a[off as usize], cnet.positive),
                        _ => break,
                    }
                }
                if live[cnet.net.0 as usize] {
                    if cnet.positive {
                        tn.value[i] = cnet.net;
                    } else {
                        mark(&mut live, &mut queue, last_inverter);
                        if last_inverter != net {
                            tn.value[i] = last_inverter;
                        }
                    }
                }
            }
        }
        drain(&mut live, &mut queue);
        (live, tentative)
    }
}

struct Tentative {
    name: String,
    value: Bundle,
    from: u32,
    is_vector: bool,
}

const UNMAPPED: u32 = u32::MAX;

/// The state of one `normalize`: the new table being filled, and the old-to-new net map.
struct Normalize<'g> {
    g: &'g mut Graph,
    live: Vec<bool>,
    table: Vec<Slot>,
    insts: Vec<Option<Instance>>,
    net_map: Vec<u32>,
    /// Heap instances carried over: old id, new id. They move when the walk is done, so the walk
    /// keeps reading (and patching) them in the old graph, as one object.
    heap: Vec<(InstId, InstId)>,
    emitted: HashSet<InstId>,
    stack: HashSet<u32>,
    visited: HashSet<u32>,
    deferred_stateful: Vec<InstId>,
}

impl<'g> Normalize<'g> {
    fn new(g: &'g mut Graph, live: Vec<bool>) -> Self {
        let old_size = g.table.len();
        let mut n = Normalize {
            g,
            live,
            table: Vec::new(),
            insts: Vec::new(),
            net_map: vec![UNMAPPED; old_size],
            heap: Vec::new(),
            emitted: HashSet::new(),
            stack: HashSet::new(),
            visited: HashSet::new(),
            deferred_stateful: Vec::new(),
        };
        for (i, k) in [Kind::TieLow, Kind::TieHigh, Kind::TieX].into_iter().enumerate() {
            let id = n.insts.len() as InstId;
            n.insts.push(Some(Instance { kind: k, base: i as u32, inline: true, metadata: 0 }));
            n.table.push(Slot::Ref(id, 0));
            n.net_map[i] = i as u32;
            n.visited.insert(i as u32);
        }
        n
    }

    /// Copy an inline instance into the new table now; reserve a heap instance's place.
    fn emit(&mut self, id: InstId) {
        let inst = self.g.inst(id);
        let old_base = inst.base;
        let slots = inst.slots();
        let needed = (old_base + slots) as usize;
        if needed > self.net_map.len() {
            self.net_map.resize(needed, UNMAPPED);
        }
        let new_base = self.table.len() as u32;
        let new_id = self.insts.len() as InstId;
        if inst.inline {
            let mut copy = inst.clone();
            copy.base = new_base;
            self.insts.push(Some(copy));
        } else {
            assert!(self.emitted.insert(id), "duplicate heap emit");
            self.insts.push(None);
            self.heap.push((id, new_id));
        }
        for i in 0..slots {
            self.table.push(Slot::Ref(new_id, i));
            self.net_map[(old_base + i) as usize] = new_base + i;
        }
    }

    /// Emit bits `start..start+width` of a bitwise cell as a cell of their own (built in the old
    /// graph first, like any other); the sliced bits map to it.
    fn emit_slice(&mut self, id: InstId, start: u32, width: u32) {
        let (s, e) = (start as usize, (start + width) as usize);
        let kind = match &self.g.inst(id).kind {
            Kind::Buffer(a) => Kind::Buffer(a[s..e].to_vec()),
            Kind::Not(a) => Kind::Not(a[s..e].to_vec()),
            Kind::Bin(op, a, b) => Kind::Bin(*op, a[s..e].to_vec(), b[s..e].to_vec()),
            Kind::Mux(sel, a, b) => Kind::Mux(*sel, a[s..e].to_vec(), b[s..e].to_vec()),
            Kind::Dangling(_) => Kind::Dangling(width),
            k => panic!("emitSlice on {}", k.keyword()),
        };
        let lsb = self.g.add(kind)[0];
        let new_inst = self.g.resolve(lsb).0;
        self.emit(new_inst);
        let old_out = self.g.output(id);
        let new_out = self.g.output(new_inst);
        for i in 0..width {
            self.net_map[old_out[(start + i) as usize].0 as usize] = self.net_map[new_out[i as usize].0 as usize];
        }
    }

    /// A loop breaker on `fanin`, emitted at once; its net.
    fn break_loop(&mut self, fanin: Net) -> Net {
        let net = self.g.add(Kind::LoopBreaker(vec![fanin]))[0];
        let id = self.g.resolve(net).0;
        self.emit(id);
        self.visited.insert(net.0);
        net
    }

    /// Observable cells and inputs first, in slot order.
    fn emit_roots(&mut self) {
        for id in self.g.instance_list() {
            let k = &self.g.inst(id).kind;
            if k.has_effects() || matches!(k, Kind::Input(..)) {
                self.emit(id);
                for bit in self.g.output(id) {
                    self.visited.insert(bit.0);
                }
            }
        }
    }

    fn dfs(&mut self, net: Net) {
        if self.visited.contains(&net.0) {
            return;
        }
        assert!(!self.stack.contains(&net.0), "topo_dfs re-entered for net on stack");
        assert!((net.0 as usize) < self.live.len() && self.live[net.0 as usize], "topo_dfs on dead or out-of-bounds net %{}", net.0);
        self.stack.insert(net.0);
        let (id, offset) = self.g.resolve(net);
        let kind = &self.g.inst(id).kind;
        let forwarded = match kind {
            Kind::Buffer(a) | Kind::LoopBreaker(a) => Some(a[offset as usize]),
            _ => None,
        };
        let (stateful, sliceable) = (kind.has_state(), kind.is_sliceable());
        if let Some(fanin) = forwarded {
            // Forwarded, not emitted: the net maps to whatever its input maps to.
            if self.stack.contains(&fanin.0) {
                let b = self.break_loop(fanin);
                self.net_map[net.0 as usize] = self.net_map[b.0 as usize];
            } else {
                self.dfs(fanin);
                self.net_map[net.0 as usize] = self.net_map[fanin.0 as usize];
            }
            self.visited.insert(net.0);
        } else if stateful {
            // A sequential boundary: emitted now, its inputs walked after every output is known,
            // so feedback through it needs no loop breaker.
            self.emit(id);
            for bit in self.g.output(id) {
                self.visited.insert(bit.0);
            }
            self.deferred_stateful.push(id);
        } else if sliceable {
            let pins = self.g.inst(id).kind.slice_pins(offset);
            self.dfs_inputs(id, pins);
            self.emit_live_range(id, offset);
        } else {
            // Every output bit shares every input: all go on the stack so a cycle through any is seen.
            for bit in self.g.output(id) {
                self.stack.insert(bit.0);
            }
            let pins = self.g.inst(id).kind.pins();
            self.dfs_inputs(id, pins);
            assert!(!self.visited.contains(&self.g.inst(id).base), "non-sliceable instance already visited before emit");
            self.emit(id);
            for bit in self.g.output(id) {
                self.visited.insert(bit.0);
                self.stack.remove(&bit.0);
            }
        }
        self.stack.remove(&net.0);
    }

    /// Walk each input in turn (read when its turn comes); an input on the stack is rewired
    /// through a loop breaker.
    fn dfs_inputs(&mut self, id: InstId, pins: Vec<Pin>) {
        for p in pins {
            let fanin = self.g.inst(id).kind.get(p);
            if self.stack.contains(&fanin.0) {
                let b = self.break_loop(fanin);
                self.g.inst_mut(id).kind.set(p, b);
            } else {
                self.dfs(fanin);
            }
        }
    }

    /// Grow the bit range around `offset` over neighbours that are live, not yet placed, and whose
    /// inputs are all placed; emit the whole cell if the range covers it, else the slice.
    fn emit_live_range(&mut self, id: InstId, offset: u32) {
        let out = self.g.output(id);
        let width = self.g.inst(id).output_width();
        let extendable = |s: &Self, bit: u32| -> bool {
            let net = out[bit as usize];
            if !s.live[net.0 as usize] || s.visited.contains(&net.0) || s.stack.contains(&net.0) {
                return false;
            }
            let kind = &s.g.inst(id).kind;
            kind.slice_pins(bit).into_iter().all(|p| s.visited.contains(&kind.get(p).0))
        };
        let mut bottom = offset;
        let mut top = offset + 1;
        while bottom > 0 && extendable(self, bottom - 1) {
            bottom -= 1;
        }
        while top < width && extendable(self, top) {
            top += 1;
        }
        if bottom == 0 && top == width {
            self.emit(id);
        } else {
            self.emit_slice(id, bottom, top - bottom);
        }
        for i in bottom..top {
            assert!(self.visited.insert(out[i as usize].0), "sliceable instance already visited before emit");
        }
    }

    /// The inputs of every observable cell, in slot order.
    fn dfs_from_effects(&mut self) {
        let mut it = self.g.instances();
        while let Some(id) = it.next(self.g) {
            if self.g.inst(id).kind.has_effects() {
                for net in self.g.inst(id).kind.inputs() {
                    self.dfs(net);
                }
            }
        }
    }

    /// Then the inputs of the sequential cells met on the way (the list grows as it is walked).
    fn dfs_deferred_stateful(&mut self) {
        let mut i = 0;
        while i < self.deferred_stateful.len() {
            let id = self.deferred_stateful[i];
            for net in self.g.inst(id).kind.inputs() {
                self.dfs(net);
            }
            i += 1;
        }
    }

    /// Then any live net nothing observable reached (an inverter kept for a tentative name).
    fn dfs_remaining_live(&mut self) {
        for i in 3..self.live.len() {
            if self.live[i] {
                self.dfs(Net(i as u32));
            }
        }
    }

    /// Move the carried heap instances over, renumber every input, re-add the tentative names
    /// over their live runs, and swap the new table in.
    fn finish(mut self, mut tentative: Vec<Tentative>) {
        for &(old, new) in &self.heap {
            let inst = self.g.insts[old as usize].take().expect("a live heap instance");
            self.insts[new as usize] = Some(inst);
        }
        for (s, slot) in self.table.iter().enumerate() {
            if let Slot::Ref(i, 0) = *slot {
                self.insts[i as usize].as_mut().unwrap().base = s as u32;
            }
        }
        let net_map = &self.net_map;
        for inst in self.insts.iter_mut().flatten() {
            inst.kind.map_inputs(|n| {
                let m = net_map.get(n.0 as usize).copied().unwrap_or(UNMAPPED);
                assert!(m != UNMAPPED, "dead net %{} in remap", n.0);
                Net(m)
            });
        }
        for tn in &mut tentative {
            for n in &mut tn.value {
                let m = net_map.get(n.0 as usize).copied().unwrap_or(UNMAPPED);
                *n = if m == UNMAPPED { Net::SENTINEL } else { Net(m) };
            }
        }
        for tn in tentative {
            let width = tn.value.len();
            let mut i = 0;
            while i < width {
                if tn.value[i] == Net::SENTINEL {
                    i += 1;
                    continue;
                }
                let start = i;
                while i < width && tn.value[i] != Net::SENTINEL {
                    i += 1;
                }
                let name = super::instance::NameInst {
                    name: tn.name.clone(),
                    value: tn.value[start..i].to_vec(),
                    from: tn.from + start as u32,
                    to: tn.from + i as u32,
                    tentative: true,
                    is_vector: tn.is_vector,
                };
                let id = self.insts.len() as InstId;
                let base = self.table.len() as u32;
                self.insts.push(Some(Instance { kind: Kind::Name(Box::new(name)), base, inline: false, metadata: 0 }));
                self.table.push(Slot::Ref(id, 0));
            }
        }
        self.g.table = self.table;
        self.g.insts = self.insts;
    }
}
