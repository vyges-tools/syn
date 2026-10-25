// SPDX-License-Identifier: Apache-2.0
//! Combinational mapping: the AND / ANDNOT / OR network covered by library cells, cut by cut.
//!
//! Each net's cuts (up to six leaves) are enumerated from its two inputs' best cuts, each cut's
//! function canonicalized to its NPN class and kept as a match when the library has the class.
//! Both polarities of each net then select a match and a cell: four area-flow rounds, then three
//! exact-area rounds, each walking the nets in id order. The selection is then built out of
//! library cells, with inverters where a polarity the mapping uses is not otherwise made, and the
//! constants tied off with tie cells.

use std::collections::{BTreeMap, BTreeSet};

use super::npn::{mask6, npn_semiclass, Npn, Truth6, COFACTOR_MASKS};
use super::target_index::{build_index, MapTarget, TargetIndex, CUT_MAXIMUM};
use crate::elab::backend::ElabError;
use crate::ir::instance::BinOp;
use crate::ir::net::{ControlNet as Literal, Net};
use crate::ir::{Graph, Kind};
use crate::library::Libraries;

const NPRIORITY_CUTS: usize = 64;
const NMATCHES_MAX: usize = 16;
const MAX_CUT_LEN: usize = 6;

type Cut = [Net; CUT_MAXIMUM];
const EMPTY_CUT: Cut = [Net::SENTINEL; CUT_MAXIMUM];

fn cut_len(cut: &Cut) -> usize {
    cut.iter().position(|&n| n == Net::SENTINEL).unwrap_or(CUT_MAXIMUM)
}

/// The union of two cuts sorted by id, into `target`; false when it would exceed `max_cut`.
fn cut_union(target: &mut Cut, len: &mut usize, max_cut: usize, cut1: &Cut, cut2: &Cut) -> bool {
    *len = 0;
    let mut j = 0;
    for &c1 in cut1.iter().take_while(|&&n| n != Net::SENTINEL) {
        while j < CUT_MAXIMUM && cut2[j] != Net::SENTINEL && cut2[j].0 < c1.0 {
            if *len == max_cut {
                return false;
            }
            target[*len] = cut2[j];
            *len += 1;
            j += 1;
        }
        if j < CUT_MAXIMUM && cut2[j] != Net::SENTINEL && cut2[j] == c1 {
            j += 1;
        }
        if *len == max_cut {
            return false;
        }
        target[*len] = c1;
        *len += 1;
    }
    while j < CUT_MAXIMUM && cut2[j] != Net::SENTINEL {
        if *len == max_cut {
            return false;
        }
        target[*len] = cut2[j];
        *len += 1;
        j += 1;
    }
    true
}

/// `t1` over `vars1` as a table over `vars2` (both sorted by id): a variable of `vars2` not in
/// `vars1` is a don't-care; one of `vars1` not in `vars2` must not be in `t1`'s support.
fn recode6(t1: Truth6, vars1: &[Net], vars2: &[Net]) -> Truth6 {
    let mut t2 = 0;
    for i2 in 0..1usize << vars2.len() {
        let mut i1 = 0;
        let mut var2i = 0;
        for (var1i, v1) in vars1.iter().enumerate() {
            while var2i < vars2.len() && vars2[var2i].0 < v1.0 {
                var2i += 1;
            }
            if var2i == vars2.len() {
                break;
            }
            if i2 & 1 << var2i != 0 {
                i1 |= 1 << var1i;
            }
        }
        if t1 & 1u64 << i1 != 0 {
            t2 |= 1u64 << i2;
        }
    }
    t2
}

/// Does the table depend on variable `var_idx`?
fn check_support6(t: Truth6, var_idx: usize) -> bool {
    let t_shift = t << (1 << var_idx);
    (t_shift ^ t) & COFACTOR_MASKS[var_idx] != 0
}

#[derive(Clone, Copy)]
struct ClassMatch {
    semiclass: Truth6,
    npn: Npn,
    cut: Cut,
}

/// A selection: the node's match and the target within the match's class, by index.
type Selected = Option<(usize, usize)>;

#[derive(Clone)]
struct NodePolarity {
    map_fouts: i32,
    flow_fouts: f32,
    farea: f32,
    selected: Selected,
}

#[derive(Clone)]
struct Node {
    fanouts: u32,
    pol: [NodePolarity; 2],
    matches: Vec<ClassMatch>,
    fid: usize,
}

#[derive(Clone, Copy)]
struct PriorityCut {
    cut: Cut,
    function: Truth6,
}

fn is_mappable_kind(kind: &Kind) -> bool {
    matches!(kind, Kind::Bin(BinOp::And | BinOp::Andnot | BinOp::Or, ..))
}

fn pol_index(lit: Literal) -> usize {
    (!lit.positive) as usize
}

struct Mapping<'a> {
    index: &'a TargetIndex,
    nodes: Vec<Node>,
    primary_outputs: Vec<Literal>,
    primary_output_fixups: Vec<(Literal, Net)>,
}

impl<'a> Mapping<'a> {
    fn new(g: &Graph, index: &'a TargetIndex) -> Self {
        let node = Node {
            fanouts: 0,
            pol: std::array::from_fn(|_| NodePolarity { map_fouts: 0, flow_fouts: 1.0, farea: 0.0, selected: None }),
            matches: Vec::new(),
            fid: 0,
        };
        Mapping { index, nodes: vec![node; g.table_size() as usize], primary_outputs: Vec::new(), primary_output_fixups: Vec::new() }
    }

    fn node(&mut self, net: Net) -> &mut Node {
        &mut self.nodes[net.0 as usize]
    }

    fn is_mappable(g: &Graph, net: Net) -> bool {
        is_mappable_kind(&g.inst(g.resolve(net).0).kind)
    }

    /// Through inverters and buffers to the driving net, with the polarity they add up to.
    fn strip_inverter(g: &Graph, net: Net) -> Literal {
        let (id, off) = g.resolve(net);
        match &g.inst(id).kind {
            Kind::Not(a) => {
                let l = Self::strip_inverter(g, a[off as usize]);
                Literal::with_polarity(l.net, !l.positive)
            }
            Kind::Buffer(a) => Self::strip_inverter(g, a[off as usize]),
            _ => Literal::pos(net),
        }
    }

    fn target(&self, m: &ClassMatch, ti: usize) -> &'a MapTarget {
        &self.index.classes[&(m.npn.ninputs(), m.semiclass)][ti]
    }

    fn inverter_area(&self) -> f32 {
        self.index.inverter.as_ref().unwrap().area
    }

    /// Every net a mapped cell must make: what a cell outside the network reads (through
    /// inverters, which are transparent here), and what a network cell reads from outside it that
    /// turns out to be the network's behind inverters. Ordered by (net, polarity).
    fn collect_primary_outputs(&mut self, g: &Graph) {
        let mut outputs = BTreeSet::new();
        let mut fixups = BTreeSet::new();
        let mut register = |net: Net| {
            let cnet = Self::strip_inverter(g, net);
            let driver = &g.inst(g.resolve(cnet.net).0).kind;
            if is_mappable_kind(driver) || driver.is_mapped() {
                outputs.insert(cnet);
                if cnet.net != net {
                    fixups.insert((cnet, net));
                }
            }
        };
        for id in g.instance_list() {
            let kind = &g.inst(id).kind;
            if matches!(kind, Kind::Name(n) if n.tentative) || matches!(kind, Kind::Not(_)) {
                continue;
            }
            if !is_mappable_kind(kind) {
                kind.inputs().into_iter().for_each(&mut register);
            } else {
                for fanin in kind.inputs() {
                    if !Self::is_mappable(g, fanin) && !fanin.is_const() {
                        register(fanin);
                    }
                }
            }
        }
        self.primary_outputs = outputs.into_iter().collect();
        self.primary_output_fixups = fixups.into_iter().collect();
    }

    fn compute_fanouts(&mut self, g: &Graph) {
        for id in g.instance_list() {
            let kind = &g.inst(id).kind;
            if is_mappable_kind(kind) {
                for n in kind.inputs() {
                    self.node(n).fanouts += 1;
                }
            }
        }
        for i in 0..self.primary_outputs.len() {
            let n = self.primary_outputs[i].net;
            self.node(n).fanouts += 100;
        }
    }

    fn prepare_matches(&mut self, g: &Graph, npriority_cuts: usize, nmatches_max: usize, max_cut_len: usize) {
        // Frontier slots, recycled: walking the instances last to first, a cell's inputs take a
        // slot when first seen and its outputs give theirs back.
        let mut frontier_size = 1; // slot 0 unused
        let mut free_slots: Vec<usize> = Vec::new();
        let mut assign_fid = |nd: &mut Node, free_slots: &mut Vec<usize>| {
            if nd.fid == 0 {
                if let Some(s) = free_slots.pop() {
                    nd.fid = s;
                } else {
                    nd.fid = frontier_size;
                    frontier_size += 1;
                }
            }
        };
        for id in g.instance_list_reversed() {
            let kind = &g.inst(id).kind;
            let width = g.inst(id).output_width();
            let out = g.output(id);
            for i in (0..width as usize).rev() {
                if let Kind::Bin(_, a, b) = kind {
                    if is_mappable_kind(kind) {
                        assign_fid(&mut self.nodes[a[i].0 as usize], &mut free_slots);
                        assign_fid(&mut self.nodes[b[i].0 as usize], &mut free_slots);
                    }
                }
                let cur = &mut self.nodes[out[i].0 as usize];
                assign_fid(cur, &mut free_slots);
                if cur.fid != 0 {
                    free_slots.push(cur.fid);
                }
            }
        }

        let mut pcuts = vec![PriorityCut { cut: EMPTY_CUT, function: 0 }; frontier_size * npriority_cuts];
        // per slot: its cuts' count and the net that last filled it
        let mut cache: Vec<(usize, Net)> = vec![(0, Net::SENTINEL); frontier_size];

        for id in 0..g.table_size() {
            let net = Net(id);
            let Some((inst, offset)) = g.try_resolve(net) else { continue };
            let fid = self.nodes[id as usize].fid;
            cache[fid] = (0, net);
            let kind = &g.inst(inst).kind;
            let off = offset as usize;
            let (fanin1, fanin2, in1_compl, in2_compl, out_compl) = match kind {
                Kind::Bin(BinOp::And, a, b) => (a[off], b[off], false, false, false),
                Kind::Bin(BinOp::Andnot, a, b) => (a[off], b[off], false, true, false),
                Kind::Bin(BinOp::Or, a, b) => (a[off], b[off], true, true, true),
                _ => continue,
            };
            let fid1 = self.nodes[fanin1.0 as usize].fid;
            let fid2 = self.nodes[fanin2.0 as usize].fid;
            let mut t1 = EMPTY_CUT;
            t1[0] = fanin1;
            let mut t2 = EMPTY_CUT;
            t2[0] = fanin2;

            let mut seen_cuts = BTreeSet::new();
            let mut matches = Vec::new();
            let mut ps_slot = 0;

            let mut i: i64 = -1;
            while i < cache[fid1].0 as i64 {
                let mut j: i64 = -1;
                while j < cache[fid2].0 as i64 {
                    let (n1_cut, n1_len, mut n1_func) = if i == -1 {
                        (t1, 1, 2)
                    } else {
                        let pc = pcuts[fid1 * npriority_cuts + i as usize];
                        (pc.cut, cut_len(&pc.cut), pc.function)
                    };
                    let (n2_cut, n2_len, mut n2_func) = if j == -1 {
                        (t2, 1, 2)
                    } else {
                        let pc = pcuts[fid2 * npriority_cuts + j as usize];
                        (pc.cut, cut_len(&pc.cut), pc.function)
                    };
                    j += 1;
                    if in1_compl {
                        n1_func ^= mask6(n1_len);
                    }
                    if in2_compl {
                        n2_func ^= mask6(n2_len);
                    }

                    let mut working = EMPTY_CUT;
                    let mut working_len = 0;
                    if !cut_union(&mut working, &mut working_len, max_cut_len, &n1_cut, &n2_cut) {
                        continue;
                    }
                    let w = &working[..working_len];
                    let mut function = recode6(n1_func, &n1_cut[..n1_len], w) & recode6(n2_func, &n2_cut[..n2_len], w);
                    if out_compl {
                        function ^= mask6(working_len);
                    }

                    // the variables the function does not depend on dropped
                    let mut reduced = EMPTY_CUT;
                    let mut reduced_len = 0;
                    for (idx, &v) in w.iter().enumerate() {
                        if check_support6(function, idx) {
                            reduced[reduced_len] = v;
                            reduced_len += 1;
                        }
                    }
                    if reduced_len < working_len {
                        function = recode6(function, w, &reduced[..reduced_len]);
                    }

                    let mut cut_hash = reduced_len as u64;
                    for v in &reduced[..reduced_len] {
                        cut_hash = cut_hash.wrapping_mul(6364136223846793005).wrapping_add(v.0 as u64);
                    }
                    if !seen_cuts.insert(cut_hash) {
                        continue;
                    }

                    let mut npn = Npn::default();
                    let sc = npn_semiclass(function, reduced_len, &mut npn);
                    if self.index.classes.contains_key(&(reduced_len, sc)) && matches.len() < nmatches_max {
                        let mut cut = [Net::UNDEF; CUT_MAXIMUM];
                        cut[..reduced_len].copy_from_slice(&reduced[..reduced_len]);
                        matches.push(ClassMatch { semiclass: sc, npn, cut });
                    }

                    if ps_slot < npriority_cuts {
                        pcuts[fid * npriority_cuts + ps_slot] = PriorityCut { cut: reduced, function };
                        ps_slot += 1;
                    }
                }
                i += 1;
            }
            cache[fid] = (ps_slot, net);
            self.nodes[id as usize].matches = matches;
        }
    }

    /// The cut's literals for a selection: each leaf with the polarity the cell reads it in. The
    /// leaves past the cut's size are the undefined net, read positive.
    fn cut_literals(&self, net: Net, sel: (usize, usize)) -> [Literal; CUT_MAXIMUM] {
        let m = &self.nodes[net.0 as usize].matches[sel.0];
        let local = self.target(m, sel.1).via.compose(&m.npn);
        std::array::from_fn(|i| Literal::with_polarity(m.cut[i], !local.input_complement[i]))
    }

    fn selected_area(&self, net: Net, sel: (usize, usize)) -> f32 {
        let m = &self.nodes[net.0 as usize].matches[sel.0];
        self.target(m, sel.1).cell.area
    }

    fn ref_cut(&mut self, g: &Graph, lit: Literal) -> f32 {
        if !Self::is_mappable(g, lit.net) {
            return 0.0;
        }
        let sel = self.nodes[lit.net.0 as usize].pol[pol_index(lit)].selected.expect("selected");
        let mut sum = 0.0f32;
        for cut_lit in self.cut_literals(lit.net, sel) {
            let cut_pol = &mut self.nodes[cut_lit.net.0 as usize].pol[pol_index(cut_lit)];
            cut_pol.map_fouts += 1;
            if cut_pol.map_fouts == 1 {
                if Self::is_mappable(g, cut_lit.net) {
                    let cut_sel = cut_pol.selected.expect("selected");
                    sum += self.selected_area(cut_lit.net, cut_sel);
                    sum += self.ref_cut(g, cut_lit);
                } else if !cut_lit.positive {
                    sum += self.inverter_area();
                }
            }
        }
        sum
    }

    fn deref_cut(&mut self, g: &Graph, lit: Literal) {
        if !Self::is_mappable(g, lit.net) {
            return;
        }
        let sel = self.nodes[lit.net.0 as usize].pol[pol_index(lit)].selected.expect("selected");
        for cut_lit in self.cut_literals(lit.net, sel) {
            let cut_pol = &mut self.nodes[cut_lit.net.0 as usize].pol[pol_index(cut_lit)];
            cut_pol.map_fouts -= 1;
            if cut_pol.map_fouts == 0 && Self::is_mappable(g, cut_lit.net) {
                self.deref_cut(g, cut_lit);
            }
        }
    }

    fn ref_node(&mut self, g: &Graph, lit: Literal) -> f32 {
        if lit.net.is_const() {
            return 0.0;
        }
        let pol = &mut self.nodes[lit.net.0 as usize].pol[pol_index(lit)];
        pol.map_fouts += 1;
        if pol.map_fouts == 1 {
            if Self::is_mappable(g, lit.net) {
                let sel = pol.selected.expect("selected");
                return self.selected_area(lit.net, sel) + self.ref_cut(g, lit);
            }
            if !lit.positive {
                return self.inverter_area();
            }
        }
        0.0
    }

    fn deref_node(&mut self, g: &Graph, lit: Literal) {
        if lit.net.is_const() {
            return;
        }
        let pol = &mut self.nodes[lit.net.0 as usize].pol[pol_index(lit)];
        pol.map_fouts -= 1;
        if pol.map_fouts == 0 && Self::is_mappable(g, lit.net) {
            self.deref_cut(g, lit);
        }
    }

    fn walk_selection(&mut self, g: &Graph, initial: bool) -> f32 {
        if !initial {
            for i in 0..self.primary_outputs.len() {
                self.deref_node(g, self.primary_outputs[i]);
            }
        }
        let mut area = 0.0f32;
        for i in 0..self.primary_outputs.len() {
            area += self.ref_node(g, self.primary_outputs[i]);
        }
        area
    }

    /// Each feasible (match, target) for polarity `c` of `net` in order: its target index and the
    /// local transform. Feasible: every cut leaf the network makes has a selection in the polarity
    /// read.
    fn candidates(&self, g: &Graph, net: Net, c: usize) -> Vec<(usize, usize)> {
        let nd = &self.nodes[net.0 as usize];
        let mut out = Vec::new();
        for (mi, m) in nd.matches.iter().enumerate() {
            let Some(targets) = self.index.classes.get(&(m.npn.ninputs(), m.semiclass)) else { continue };
            for (ti, target) in targets.iter().enumerate() {
                let local = target.via.compose(&m.npn);
                if local.output_complement != (c != 0) {
                    continue;
                }
                out.push((mi, ti));
            }
        }
        out.retain(|&sel| {
            self.cut_literals(net, sel).iter().all(|cl| {
                !(Self::is_mappable(g, cl.net) && self.nodes[cl.net.0 as usize].pol[pol_index(*cl)].selected.is_none())
            })
        });
        out
    }

    fn area_flow_round(&mut self, g: &Graph, refs_blend: f32, initial: bool) {
        let inv_area = self.inverter_area();
        for nd in &mut self.nodes {
            for c in &mut nd.pol {
                let blended = refs_blend * nd.fanouts as f32 + (1.0 - refs_blend) * c.map_fouts as f32;
                c.flow_fouts = blended.max(1.0);
            }
        }
        for id in 0..g.table_size() {
            let net = Net(id);
            if g.try_resolve(net).is_none() {
                continue;
            }
            if !Self::is_mappable(g, net) {
                let nd = &mut self.nodes[id as usize];
                nd.pol[0].farea = 0.0;
                nd.pol[1].farea = inv_area / nd.pol[1].flow_fouts;
                continue;
            }
            for c in 0..2 {
                let mut best_area = 1.0e30f32;
                let mut best: Selected = None;
                for sel in self.candidates(g, net, c) {
                    let mut area = self.selected_area(net, sel);
                    for cl in self.cut_literals(net, sel) {
                        area += self.nodes[cl.net.0 as usize].pol[pol_index(cl)].farea;
                    }
                    area = area.min(1.0e20);
                    if area < best_area {
                        best_area = area;
                        best = Some(sel);
                    }
                }
                let lit = Literal::with_polarity(net, c == 0);
                let pol = &self.nodes[id as usize].pol[c];
                if pol.map_fouts != 0 && best.is_some() && pol.selected != best {
                    self.deref_cut(g, lit);
                    self.nodes[id as usize].pol[c].selected = best;
                    self.ref_cut(g, lit);
                } else {
                    self.nodes[id as usize].pol[c].selected = best;
                }
                let pol = &mut self.nodes[id as usize].pol[c];
                pol.farea = best_area / pol.flow_fouts;
            }
        }
        self.walk_selection(g, initial);
    }

    fn exact_round(&mut self, g: &Graph) {
        for id in 0..g.table_size() {
            let net = Net(id);
            if g.try_resolve(net).is_none() || !Self::is_mappable(g, net) {
                continue;
            }
            for c in 0..2 {
                let lit = Literal::with_polarity(net, c == 0);
                if self.nodes[id as usize].pol[c].map_fouts != 0 {
                    self.deref_cut(g, lit);
                }
                let mut best_area = 1.0e30f32;
                let mut best: Selected = None;
                for sel in self.candidates(g, net, c) {
                    // selected for the moment, to measure what it adds
                    self.nodes[id as usize].pol[c].selected = Some(sel);
                    let mut area = self.selected_area(net, sel) + self.ref_cut(g, lit);
                    area = area.min(1.0e20);
                    self.deref_cut(g, lit);
                    if area < best_area {
                        best_area = area;
                        best = Some(sel);
                    }
                }
                self.nodes[id as usize].pol[c].selected = best;
                if self.nodes[id as usize].pol[c].map_fouts != 0 {
                    self.ref_cut(g, lit);
                }
            }
        }
        self.walk_selection(g, false);
    }

    /// The selection as library cells, net by net in id order; then the outputs that were read
    /// through inverters rewired, and the constants that cells and outputs read tied off.
    fn integrate(&mut self, g: &mut Graph) {
        let index = self.index;
        let mut complements: BTreeMap<Net, Net> = BTreeMap::new();
        complements.insert(Net::ZERO, Net::ONE);
        complements.insert(Net::UNDEF, Net::ONE);
        complements.insert(Net::ONE, Net::ZERO);
        let inverter = index.inverter.clone().unwrap();

        let size = g.table_size();
        for id in 0..size {
            let net = Net(id);
            if net.is_const() || g.try_resolve(net).is_none() {
                continue;
            }
            if !Self::is_mappable(g, net) {
                if self.nodes[id as usize].pol[1].map_fouts != 0 {
                    let inv_out = g.add(Kind::Target(inverter.clone(), vec![net]));
                    complements.insert(net, inv_out[0]);
                }
                continue;
            }
            for c in 0..2 {
                if self.nodes[id as usize].pol[c].map_fouts == 0 {
                    continue;
                }
                let sel = self.nodes[id as usize].pol[c].selected.expect("selected");
                let m = self.nodes[id as usize].matches[sel.0];
                let target = self.target(&m, sel.1);
                let local = target.via.compose(&m.npn).inv();
                let inputs: Vec<Net> = (0..m.npn.ninputs())
                    .map(|i| {
                        let inet = m.cut[local.permutation[i] as usize];
                        if local.input_complement[i] {
                            complements[&inet]
                        } else {
                            inet
                        }
                    })
                    .collect();
                let out = g.add(Kind::Target(target.cell.clone(), inputs));
                if c == 0 {
                    g.force_replace(&[net], &[out[0]]);
                } else {
                    complements.insert(net, out[0]);
                }
            }
            // only the complement is made: an inverter back, for the name
            if self.nodes[id as usize].pol[1].map_fouts != 0 && self.nodes[id as usize].pol[0].map_fouts == 0 {
                let n = g.add(Kind::Not(vec![complements[&net]]));
                g.force_replace(&[net], &n);
            }
        }

        for &(underlying, original) in &self.primary_output_fixups {
            if !underlying.positive {
                g.force_replace(&[original], &[complements[&underlying.net]]);
            } else {
                g.force_replace(&[original], &[underlying.net]);
            }
        }

        let (tie_low, low_out) = index.tie_low.clone().unwrap();
        let (tie_high, high_out) = index.tie_high.clone().unwrap();
        let (high, low) = if std::sync::Arc::ptr_eq(&tie_low, &tie_high) {
            let tie = g.add(Kind::Target(tie_low, Vec::new()));
            (tie[high_out], tie[low_out])
        } else {
            let high = g.add(Kind::Target(tie_high, Vec::new()))[high_out];
            let low = g.add(Kind::Target(tie_low, Vec::new()))[low_out];
            (high, low)
        };
        for id in g.instance_list() {
            let kind = &mut g.inst_mut(id).kind;
            if matches!(kind, Kind::Target(..) | Kind::Output(..)) {
                kind.map_inputs(|n| if !n.is_const() { n } else if n == Net::ONE { high } else { low });
            }
        }
    }
}

/// Normalizes, indexes the library (SYN-0016 without an inverter, SYN-1017 without both tie
/// cells), maps, normalizes. Prints `[INFO SYN-0017]` when done.
pub fn map_combinationals(g: &mut Graph, libs: &Libraries) -> Result<(), ElabError> {
    g.normalize();
    let index = build_index(libs);
    if index.inverter.is_none() {
        return Err(ElabError { code: 16, message: "mapCombinationals: no inverter cell found".into() });
    }
    if index.tie_low.is_none() || index.tie_high.is_none() {
        return Err(ElabError { code: 1017, message: "mapCombinationals: no tie cells found".into() });
    }
    g.normalize();

    let mut state = Mapping::new(g, &index);
    state.collect_primary_outputs(g);
    state.compute_fanouts(g);
    state.prepare_matches(g, NPRIORITY_CUTS, NMATCHES_MAX, MAX_CUT_LEN);

    state.area_flow_round(g, 1.0, true);
    state.area_flow_round(g, 0.5, false);
    state.area_flow_round(g, 0.2, false);
    state.area_flow_round(g, 0.0, false);
    state.exact_round(g);
    state.exact_round(g);
    state.exact_round(g);
    state.integrate(g);

    println!("[INFO SYN-0017] mapCombinationals: done");
    g.normalize();
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    // Rule: a cut union merges by net id, a shared leaf once; past the limit it fails.
    #[test]
    fn cuts_merge_by_id() {
        let mut a = EMPTY_CUT;
        a[..2].copy_from_slice(&[Net(5), Net(9)]);
        let mut b = EMPTY_CUT;
        b[..2].copy_from_slice(&[Net(3), Net(9)]);
        let (mut t, mut len) = (EMPTY_CUT, 0);
        assert!(cut_union(&mut t, &mut len, 6, &a, &b));
        assert_eq!(&t[..len], &[Net(3), Net(5), Net(9)]);
        assert!(!cut_union(&mut t, &mut len, 2, &a, &b));
    }

    // Rule: recoding a one-variable table onto a superset of variables keeps it a function of
    // that variable; a variable out of the support is dropped by checkSupport6.
    #[test]
    fn tables_recode_onto_other_variables() {
        // x (net 7) over [3, 7]: 1 where bit 1 is set
        assert_eq!(recode6(0b10, &[Net(7)], &[Net(3), Net(7)]), 0b1100);
        assert!(check_support6(0b1100, 1));
        assert!(!check_support6(0b1100, 0));
    }
}
