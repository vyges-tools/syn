// SPDX-License-Identifier: Apache-2.0
//! Latch inference on the elaborated graph (DIVERGENCE D2: not in the reference `syn`).
//!
//! The frontend is built with mux lowering, which emits a latch (`always_latch`, or an `always`
//! block that does not assign a variable on every path) as a mux tree that reads the variable
//! back: a combinational loop. The reference `syn` rejects such a loop (`check_combinational_loops`,
//! SYN-0080); before that check was ported we mapped the loop as logic, and a clock gate's latch
//! became an AND with a loop breaker. The Yosys reference flow keeps it a latch: its slang frontend
//! creates `$dlatch` for an `always_latch` (`handle_comb_like_process`, non-mux-lowering build),
//! `proc_dlatch` does the same for a process, and the latch is mapped to the library's latch cell
//! (`dfflegalize` + `techmap` of `$_DLATCH_P_`/`$_DLATCH_N_`).
//!
//! `infer_latches` runs where the reference runs `check_combinational_loops`: after the graph is
//! normalized and constant-folded, on the loops that survive, each cut by a loop breaker. Run on
//! the graph as the frontend built it (as Yosys runs `proc`), it also took structural loops that
//! optimization removes, such as a static function variable read back before it is written (2,802
//! bits on CoralNPU, 2026-11-17, where the base and the reference have two latches).
//! For each loop breaker whose loop is a mux tree, `latch_rule::proc_dlatch` gives the hold
//! condition and the data input (the breaker's output is the feedback), and the bit becomes a
//! library latch cell: enable active low on the
//! hold where the library has one (a `$_DLATCH_N_`), else active high on its complement, or on
//! the hold's own input when the hold is a complement (Yosys `opt` folds the inverter into the
//! enable polarity the same way).

use std::sync::Arc;

use crate::flow::latch_rule::{self, LatchGraph, Node};
use crate::ir::instance::{BinOp, LibCell, LibDirection, ShiftOp};
use crate::ir::net::Net;
use crate::ir::{Graph, InstId, Kind};
use crate::library::{pin_expr, Libraries};

/// A slot form wider than this many select bits is not walked (2^bits slots per bit).
const MAX_SLOT_SELECT_BITS: usize = 6;

/// A library latch: no clear or preset, its data input and its output the state itself.
#[derive(Clone, Debug)]
pub struct LatchCell {
    pub cell: Arc<LibCell>,
    /// Transparent while the enable is 1 (`enable : "CLK"`), else while it is 0 (`"!CLK"`).
    pub enable_high: bool,
    enable_in: usize,
    data_in: usize,
    data_out: usize,
    inputs: usize,
}

fn input_position(cell: &LibCell, name: &str) -> Option<usize> {
    let mut pos = 0;
    for p in cell.ports.iter().filter(|p| p.direction == LibDirection::Input) {
        if p.name == name {
            return Some(pos);
        }
        pos += if p.is_bus { p.size as usize } else { 1 };
    }
    None
}

/// The cell as a plain latch: one `latch` group whose enable is a pin or its complement, whose
/// data input is a pin, no clear or preset, an output that is the state, no other input.
fn detect_latch(cell: &Arc<LibCell>) -> Option<LatchCell> {
    let seq = cell.seq.as_ref()?;
    if !seq.latch || seq.clear.is_some() || seq.preset.is_some() {
        return None;
    }
    let (enable_high, enable_port) = pin_expr(seq.clocked_on.as_deref()?)?;
    let (true, data_port) = pin_expr(seq.next_state.as_deref()?)? else { return None };
    let enable_in = input_position(cell, &enable_port)?;
    let data_in = input_position(cell, &data_port)?;
    let mut data_out = None;
    let mut pos = 0;
    for p in cell.ports.iter().filter(|p| !p.pwr_gnd && p.direction == LibDirection::Output) {
        if matches!(p.function.as_deref().and_then(pin_expr), Some((true, n)) if n == seq.iq) && data_out.is_none() {
            data_out = Some(pos);
        }
        pos += if p.is_bus { p.size as usize } else { 1 };
    }
    let total = cell.ports.iter().filter(|p| !p.pwr_gnd && p.direction == LibDirection::Input).count();
    if total != 2 || enable_in == data_in {
        return None;
    }
    let inputs = cell.ports.iter().filter(|p| p.direction == LibDirection::Input).map(|p| if p.is_bus { p.size as usize } else { 1 }).sum();
    Some(LatchCell { cell: cell.clone(), enable_high, enable_in, data_in, data_out: data_out?, inputs })
}

/// The library's latches, (active high, active low): per polarity the smallest area, then the
/// name (`DHLx1`/`DLLx1` on ASAP7, the cells the reference flow's latch map names). Cells withheld
/// by `dont_use` are skipped.
pub fn latch_cells(libs: &Libraries) -> (Option<LatchCell>, Option<LatchCell>) {
    let (mut high, mut low): (Option<LatchCell>, Option<LatchCell>) = (None, None);
    for cell in libs.cells() {
        if cell.dont_use {
            continue;
        }
        let Some(l) = detect_latch(cell) else { continue };
        let slot = if l.enable_high { &mut high } else { &mut low };
        let better = match slot {
            None => true,
            Some(have) => l.cell.area < have.cell.area || (l.cell.area == have.cell.area && l.cell.name < have.cell.name),
        };
        if better {
            *slot = Some(l);
        }
    }
    (high, low)
}

/// The graph as `latch_rule` reads it, for one feedback: `needles` are the loop breakers that cut
/// its loop (normalize cuts each back edge to the same net with a breaker of its own); only nets in
/// that loop are walked.
struct View<'g> {
    g: &'g mut Graph,
    needles: &'g [Net],
    scc: &'g [u32],
}

/// The data inputs a net's driver passes through (never a select): the edges of the mux graph.
fn mux_fanins(g: &Graph, net: Net) -> Vec<Net> {
    match node(g, net) {
        Node::Alias(a) => vec![a],
        Node::Mux { one, zero, .. } => vec![one, zero],
        Node::Slots { slots, .. } => slots,
        Node::Needle | Node::Leaf => Vec::new(),
    }
}

/// The driver of `net` as a mux form: a buffer passes its bit through; a mux is one; bit `i` of a
/// logical right shift by `s` (stride `w`) is slot `k` = input bit `i + k*w` (past the end: the
/// shift's fill) when `s == k`.
fn node(g: &Graph, net: Net) -> Node<Net> {
    if net.is_const() {
        return Node::Leaf;
    }
    let Some((id, off)) = g.try_resolve(net) else { return Node::Leaf };
    let off = off as usize;
    match &g.inst(id).kind {
        // a loop breaker is transparent here: the loop it cuts is the loop looked for
        Kind::Buffer(a) | Kind::LoopBreaker(a) => Node::Alias(a[off]),
        Kind::Mux(s, a, b) => Node::Mux { sel: *s, one: a[off], zero: b[off] },
        Kind::Shift(op @ (ShiftOp::UShr | ShiftOp::XShr), a, s, stride) if !s.is_empty() && s.len() <= MAX_SLOT_SELECT_BITS => {
            let fill = if *op == ShiftOp::UShr { Net::ZERO } else { Net::UNDEF };
            let slots = (0..1usize << s.len()).map(|k| a.get(off + k * *stride as usize).copied().unwrap_or(fill)).collect();
            Node::Slots { sel: s.clone(), slots }
        }
        _ => Node::Leaf,
    }
}

impl LatchGraph for View<'_> {
    type Net = Net;
    fn node(&self, net: Net) -> Node<Net> {
        if self.needles.contains(&net) {
            return Node::Needle;
        }
        // a net made after the components were found (a latch already inferred) is no loop's
        match self.scc.get(net.0 as usize) {
            Some(&c) if !net.is_const() && c == self.scc[self.needles[0].0 as usize] => {}
            _ => return Node::Leaf,
        }
        node(self.g, net)
    }
    fn one(&self) -> Net {
        Net::ONE
    }
    fn undef(&self) -> Net {
        Net::UNDEF
    }
    /// A complement of a complement is its input.
    fn not(&mut self, a: Net) -> Net {
        if let Some(x) = complement_of(self.g, a) {
            return x;
        }
        self.g.add(Kind::Not(vec![a]))[0]
    }
    fn and(&mut self, a: Net, b: Net) -> Net {
        self.g.add(Kind::Bin(BinOp::And, vec![a], vec![b]))[0]
    }
    fn or(&mut self, a: Net, b: Net) -> Net {
        self.g.add(Kind::Bin(BinOp::Or, vec![a], vec![b]))[0]
    }
    fn eq_const(&mut self, sel: &[Net], k: usize) -> Net {
        if sel.len() == 1 {
            return if k == 1 { sel[0] } else { self.not(sel[0]) };
        }
        let c = (0..sel.len()).map(|i| if (k >> i) & 1 == 1 { Net::ONE } else { Net::ZERO }).collect();
        self.g.add(Kind::Bin(BinOp::Eq, sel.to_vec(), c))[0]
    }
    fn mux(&mut self, sel: Net, one: Net, zero: Net) -> Net {
        self.g.add(Kind::Mux(sel, vec![one], vec![zero]))[0]
    }
    fn slots(&mut self, sel: &[Net], slots: &[Net]) -> Net {
        self.g.add(Kind::Shift(ShiftOp::UShr, slots.to_vec(), sel.to_vec(), 1))[0]
    }
}

/// `a` when `net` is `!a`.
fn complement_of(g: &Graph, net: Net) -> Option<Net> {
    if net.is_const() {
        return None;
    }
    let (id, off) = g.try_resolve(net)?;
    match &g.inst(id).kind {
        Kind::Not(a) => Some(a[off as usize]),
        _ => None,
    }
}

/// Strongly connected components of the mux graph (nets, edges to `mux_fanins`), iterative
/// Tarjan: each net's component id; a net on no loop has a component of its own.
fn mux_sccs(g: &Graph) -> Vec<u32> {
    let n = g.table_size() as usize;
    const NONE: u32 = u32::MAX;
    let mut index = vec![NONE; n];
    let mut low = vec![0u32; n];
    let mut comp = vec![NONE; n];
    let mut on_stack = vec![false; n];
    let mut stack: Vec<u32> = Vec::new();
    let (mut next_index, mut next_comp) = (0u32, 0u32);
    for root in 0..n {
        if index[root] != NONE || g.try_resolve(Net(root as u32)).is_none() {
            continue;
        }
        // (net, its fanins, the next fanin to visit)
        let mut work: Vec<(u32, Vec<Net>, usize)> = vec![(root as u32, mux_fanins(g, Net(root as u32)), 0)];
        index[root] = next_index;
        low[root] = next_index;
        next_index += 1;
        stack.push(root as u32);
        on_stack[root] = true;
        while let Some(top) = work.len().checked_sub(1) {
            let v = work[top].0 as usize;
            if work[top].2 < work[top].1.len() {
                let w = work[top].1[work[top].2].0 as usize;
                work[top].2 += 1;
                if Net(w as u32).is_const() || g.try_resolve(Net(w as u32)).is_none() {
                    continue;
                }
                if index[w] == NONE {
                    index[w] = next_index;
                    low[w] = next_index;
                    next_index += 1;
                    stack.push(w as u32);
                    on_stack[w] = true;
                    work.push((w as u32, mux_fanins(g, Net(w as u32)), 0));
                } else if on_stack[w] {
                    low[v] = low[v].min(index[w]);
                }
                continue;
            }
            work.pop();
            if let Some((parent, ..)) = work.last() {
                let p = *parent as usize;
                low[p] = low[p].min(low[v]);
            }
            if low[v] == index[v] {
                loop {
                    let w = stack.pop().expect("the component's root is still on the stack") as usize;
                    on_stack[w] = false;
                    comp[w] = next_comp;
                    if w == v {
                        break;
                    }
                }
                next_comp += 1;
            }
        }
    }
    comp
}

/// What `infer_latches` did.
#[derive(Clone, Copy, Default, PartialEq, Eq, Debug)]
#[must_use]
pub struct LatchCount {
    /// Bits made library latches.
    pub mapped: usize,
    /// Bits a mux tree reads back that stay loops: the libraries have no plain latch.
    pub unmapped: usize,
}

/// Every loop breaker whose loop is a mux tree becomes a library latch (see the module note).
/// On a normalized graph; normalize it again after.
pub fn infer_latches(g: &mut Graph, libs: &Libraries) -> LatchCount {
    let sccs = mux_sccs(g);
    let mut size = vec![0u32; sccs.len()];
    for &c in &sccs {
        if c != u32::MAX {
            size[c as usize] += 1;
        }
    }
    // loop breakers on a loop of the mux graph, by the net they cut, in slot order of the first:
    // (that net, the breakers, their nets)
    let mut candidates: Vec<(Net, Vec<InstId>, Vec<Net>)> = Vec::new();
    for id in g.instance_list() {
        let Kind::LoopBreaker(a) = &g.inst(id).kind else { continue };
        if a.len() != 1 {
            continue;
        }
        let (q, rhs) = (Net(g.base_id(id)), a[0]);
        let c = sccs[q.0 as usize];
        if rhs.is_const() || rhs == q || c == u32::MAX || size[c as usize] <= 1 {
            continue;
        }
        // breakers on the same net are one feedback (nested `if`s: one per back edge)
        match candidates.iter_mut().find(|(r, ..)| *r == rhs) {
            Some((_, ids, qs)) => {
                ids.push(id);
                qs.push(q);
            }
            None => candidates.push((rhs, vec![id], vec![q])),
        }
    }
    if candidates.is_empty() {
        return LatchCount::default();
    }
    let (high, low) = latch_cells(libs);
    let mut count = LatchCount::default();
    for (rhs, ids, qs) in candidates {
        let latch = {
            let mut v = View { g, needles: &qs, scc: &sccs };
            latch_rule::proc_dlatch(&mut v, rhs)
        };
        let Some(latch) = latch else { continue };
        // enable active low on the hold; active high on the hold's input when it is a complement
        let inverted_hold = complement_of(g, latch.hold);
        let (cell, enable) = match (&high, &low, inverted_hold) {
            (Some(h), _, Some(x)) => (h, x),
            (_, Some(l), _) => (l, latch.hold),
            (Some(h), None, None) => (h, g.add(Kind::Not(vec![latch.hold]))[0]),
            (None, None, _) => {
                count.unmapped += 1;
                continue;
            }
        };
        let mut inputs = vec![Net::UNDEF; cell.inputs];
        inputs[cell.enable_in] = enable;
        inputs[cell.data_in] = latch.data;
        let out = g.add(Kind::Target(cell.cell.clone(), inputs))[cell.data_out];
        // the breakers' readers now read the latch; so does every reader of the net they cut, its
        // name among them: on the loop that net IS the variable (Yosys: the latch's Q is the
        // variable), and a name left on the dead tree is lost
        for id in ids {
            g.inst_mut(id).kind = Kind::Buffer(vec![out]);
        }
        g.force_replace(&[rhs], &[out]);
        count.mapped += 1;
    }
    count
}
