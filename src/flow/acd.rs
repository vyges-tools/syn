// SPDX-License-Identifier: Apache-2.0
//! Gate-level resynthesis of a small function by enumerating Ashenhurst-Curtis decompositions
//! with a shared set (Mishchenko, Brayton, Calvino, De Micheli, "Boolean decomposition
//! revisited", IWLS'23), adapted to library cells: each round picks a bound set, encodes its
//! column multiplicity in one decoder cell (optionally sharing one bound variable with the upper
//! function), and recurses on the smaller upper function, branch-and-bound on area plus a
//! timing term.
//!
//! Stages in the order a call runs them: [`TruthTable`] → [`MatchCache`] (cells by function, up to
//! a permutation of inputs) → `Search` (`recurse` → `try_bound_choice` → `build_upper_function`)
//! → `Emitter` (the round chain as a [`GateNetwork`]) → [`synthesize`]. The timing helpers
//! ([`output_arrival`], [`network_slack`], [`find_delay_lower_bound`]) evaluate a network on the
//! Liberty gate tables at a fixed input slew.

use std::collections::BTreeMap;
use std::sync::Arc;

use vyges_loom::liberty_func::Func;
use vyges_sta::liberty::{Cell as TimingCell, Library as TimingLibrary, Model};

use super::npn::{mask6, npn_semiclass, Npn, Truth6, COFACTOR_MASKS};
use super::target_index::TargetIndex;
use crate::elab::backend::ElabError;
use crate::ir::instance::{LibCell, LibDirection};

/// Rise and fall, in the order every per-transition loop here walks them.
const RISE: usize = 0;
const FALL: usize = 1;
const RISE_FALL: [usize; 2] = [RISE, FALL];

/// `std::max`: the first unless it is less than the second (a NaN first is kept).
fn max_f(a: f32, b: f32) -> f32 {
    if a < b {
        b
    } else {
        a
    }
}

/// `std::min`: the first unless the second is less.
fn min_f(a: f32, b: f32) -> f32 {
    if b < a {
        b
    } else {
        a
    }
}

/// A double as the logger prints `{}`: the shortest digits that read back, fixed between 1e-4
/// and 1e16, else `d.ddde±XX`.
pub fn fmt_double(v: f64) -> String {
    if v == 0.0 || !v.is_finite() {
        return format!("{v}");
    }
    let e = format!("{v:e}");
    let (mant, exp) = e.split_once('e').unwrap_or((&e, "0"));
    let exp: i32 = exp.parse().unwrap_or(0);
    if (-4..16).contains(&exp) {
        format!("{v}")
    } else {
        format!("{mant}e{}{:02}", if exp < 0 { '-' } else { '+' }, exp.abs())
    }
}

/// The debug channels this module prints on, and the lines printed: `acd` (the search) and
/// `acd_resynth` (the command), each at its level as `set_debug_level SYN <group> <level>` sets it.
#[derive(Default, Debug)]
pub struct DebugLog {
    pub acd: u32,
    pub acd_resynth: u32,
    pub lines: Vec<String>,
}

impl DebugLog {
    pub fn check_acd(&self, level: u32) -> bool {
        self.acd >= level
    }

    pub fn print_acd(&mut self, level: u32, msg: String) {
        if self.check_acd(level) {
            self.lines.push(format!("[DEBUG SYN-acd] {msg}"));
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Truth tables

/// A possibly-multi-output truth table over a list of variable ids. Values and don't-cares are
/// output-major: output `o`, minterm `m` at `o · 2^nvars + m`, variable position `i` bit `i` of `m`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TruthTable {
    variables: Vec<usize>,
    num_outputs: usize,
    values: Vec<bool>,
    dontcares: Vec<bool>,
}

impl Default for TruthTable {
    fn default() -> Self {
        TruthTable::new(Vec::new(), 1, false, false)
    }
}

impl TruthTable {
    pub fn new(variables: Vec<usize>, num_outputs: usize, initial_value: bool, initial_dontcare: bool) -> Self {
        let size = num_outputs << variables.len();
        TruthTable { variables, num_outputs, values: vec![initial_value; size], dontcares: vec![initial_dontcare; size] }
    }

    pub fn variables(&self) -> &[usize] {
        &self.variables
    }
    pub fn variable(&self, position: usize) -> usize {
        self.variables[position]
    }
    pub fn num_variables(&self) -> usize {
        self.variables.len()
    }
    pub fn num_outputs(&self) -> usize {
        self.num_outputs
    }
    pub fn num_minterms(&self) -> usize {
        1 << self.num_variables()
    }
    pub fn size(&self) -> usize {
        self.num_outputs() * self.num_minterms()
    }

    fn index(&self, output: usize, minterm: usize) -> usize {
        debug_assert!(output < self.num_outputs() && minterm < self.num_minterms());
        output * self.num_minterms() + minterm
    }

    pub fn value(&self, output: usize, minterm: usize) -> bool {
        self.values[self.index(output, minterm)]
    }
    pub fn dont_care(&self, output: usize, minterm: usize) -> bool {
        self.dontcares[self.index(output, minterm)]
    }
    pub fn set_value(&mut self, output: usize, minterm: usize, value: bool) {
        let i = self.index(output, minterm);
        self.values[i] = value;
    }
    pub fn set_dont_care(&mut self, output: usize, minterm: usize, dontcare: bool) {
        let i = self.index(output, minterm);
        self.dontcares[i] = dontcare;
    }

    /// Swap variable positions `a` and `b`, every output alike.
    pub fn swap_vars(&mut self, a: usize, b: usize) {
        if a == b {
            return;
        }
        self.variables.swap(a, b);
        let n = self.num_minterms();
        for o in 0..self.num_outputs() {
            let base = o * n;
            for i in 0..n {
                if (i >> a & 1) != 0 || (i >> b & 1) == 0 {
                    continue;
                }
                let j = (i & !(1 << b)) | (1 << a);
                self.values.swap(base + i, base + j);
                self.dontcares.swap(base + i, base + j);
            }
        }
    }

    /// The first variable position no output depends on: a variable is supported when two care
    /// minterms differing in it alone differ in value. ⚠️ The scan runs over every output's
    /// minterms as one index, so a minterm and its neighbour always sit in the same output.
    pub fn find_unsupported_var(&self) -> Option<usize> {
        let mut supported: u32 = 0;
        for i in 0..self.size() {
            for j in 0..self.num_variables() {
                if i & (1 << j) != 0 {
                    continue;
                }
                let k = i | (1 << j);
                if !self.dontcares[i] && !self.dontcares[k] && self.values[i] != self.values[k] {
                    supported |= 1 << j;
                }
            }
        }
        (0..self.num_variables()).find(|&j| supported & (1 << j) == 0)
    }

    /// The first variable position output `o` equals at every care minterm.
    pub fn output_passthrough(&self, o: usize) -> Option<usize> {
        let nm = self.num_minterms();
        let base = o * nm;
        (0..self.num_variables())
            .find(|&v| (0..nm).all(|m| self.dontcares[base + m] || self.values[base + m] == ((m >> v) & 1 != 0)))
    }

    /// Drop unsupported variables one at a time, re-checking after each: merging a variable's
    /// cofactors fills don't-cares, which can make another variable supported. The dropped variable
    /// is first swapped to the top position; each merged minterm takes the low cofactor when it is
    /// care, else the high one when that is, else stays don't-care.
    pub fn shrink_to_support(&mut self) {
        while let Some(j) = self.find_unsupported_var() {
            let nv = self.num_variables();
            self.swap_vars(j, nv - 1);
            let old_n = 1 << nv;
            let new_n = old_n >> 1;
            let mut vals = vec![false; self.num_outputs() * new_n];
            let mut dcs = vec![true; self.num_outputs() * new_n];
            for o in 0..self.num_outputs() {
                for i in 0..new_n {
                    let lo = o * old_n + i;
                    let hi = lo + new_n;
                    let dst = o * new_n + i;
                    if !self.dontcares[lo] {
                        vals[dst] = self.values[lo];
                        dcs[dst] = false;
                    } else if !self.dontcares[hi] {
                        vals[dst] = self.values[hi];
                        dcs[dst] = false;
                    }
                }
            }
            self.variables.pop();
            self.values = vals;
            self.dontcares = dcs;
        }
    }

    pub fn has_dontcares(&self) -> bool {
        self.dontcares.contains(&true)
    }
}

// ---------------------------------------------------------------------------------------------
// Timing objective

/// Minus the delay budget left from a node to each cut exit, per (exit output, exit transition):
/// an arrival-time view of the budgets. Index `out · 2 + rf`; unset entries are −∞.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct ArrivalSet {
    v: [f32; 4],
}

impl Default for ArrivalSet {
    fn default() -> Self {
        ArrivalSet { v: [f32::NEG_INFINITY; 4] }
    }
}

impl ArrivalSet {
    pub fn at_exit(&self, out: usize, out_rf: usize) -> f32 {
        self.v[out * 2 + out_rf]
    }
    pub fn at_exit_mut(&mut self, out: usize, out_rf: usize) -> &mut f32 {
        &mut self.v[out * 2 + out_rf]
    }
    /// Elementwise `std::max` into this set.
    pub fn merge_max(&mut self, o: &ArrivalSet) {
        for i in 0..4 {
            self.v[i] = max_f(self.v[i], o.v[i]);
        }
    }
    /// Every entry plus `d` (−∞ stays −∞).
    pub fn plus(&self, d: f32) -> ArrivalSet {
        let mut r = ArrivalSet::default();
        for i in 0..4 {
            r.v[i] = self.v[i] + d;
        }
        r
    }
    pub fn max_entry(&self) -> f32 {
        max_f(max_f(self.v[0], self.v[1]), max_f(self.v[2], self.v[3]))
    }
}

/// A node's arrival sets for its rise and its fall.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct NodeArrivals {
    rise: ArrivalSet,
    fall: ArrivalSet,
}

impl NodeArrivals {
    pub fn at_transition(&self, rf: usize) -> &ArrivalSet {
        if rf == RISE {
            &self.rise
        } else {
            &self.fall
        }
    }
    pub fn at_transition_mut(&mut self, rf: usize) -> &mut ArrivalSet {
        if rf == RISE {
            &mut self.rise
        } else {
            &mut self.fall
        }
    }
    /// The slack were this node exit `idx`: the least of minus its rise→rise and fall→fall entries.
    pub fn exit_slack(&self, idx: usize) -> f32 {
        let mut ret = f32::INFINITY;
        for rf in RISE_FALL {
            ret = min_f(ret, -self.at_transition(rf).at_exit(idx, rf));
        }
        ret
    }
    pub fn max_entry(&self) -> f32 {
        max_f(self.rise.max_entry(), self.fall.max_entry())
    }
}

#[derive(Clone, Debug, Default)]
pub struct PrimaryInput {
    pub arrivals: NodeArrivals,
}

#[derive(Clone, Debug, Default)]
pub struct PrimaryOutput {
    pub external_load: f32,
    pub critical: bool,
    pub criticality: f64,
}

/// The function to synthesize, with each input's arrivals and each output's load and criticality.
#[derive(Clone, Debug)]
pub struct SynthesisProblem {
    function: TruthTable,
    inputs: Vec<PrimaryInput>,
    outputs: Vec<PrimaryOutput>,
}

impl SynthesisProblem {
    pub fn new(f: TruthTable) -> Self {
        let inputs = vec![PrimaryInput::default(); f.num_variables()];
        let outputs = vec![PrimaryOutput::default(); f.num_outputs()];
        SynthesisProblem { function: f, inputs, outputs }
    }
    pub fn function(&self) -> &TruthTable {
        &self.function
    }
    pub fn num_inputs(&self) -> usize {
        self.inputs.len()
    }
    pub fn num_outputs(&self) -> usize {
        self.outputs.len()
    }
    pub fn input(&self, i: usize) -> &PrimaryInput {
        &self.inputs[i]
    }
    pub fn input_mut(&mut self, i: usize) -> &mut PrimaryInput {
        &mut self.inputs[i]
    }
    pub fn output(&self, i: usize) -> &PrimaryOutput {
        &self.outputs[i]
    }
    pub fn output_mut(&mut self, i: usize) -> &mut PrimaryOutput {
        &mut self.outputs[i]
    }
}

pub type Cost = f64;
pub const INF_COST: Cost = f64::MAX / 200.0;
pub const MAX_BOUND_VARS: usize = 6;

// ---------------------------------------------------------------------------------------------
// Cells

/// A cell's output port: the cell and the port's position among its ports.
#[derive(Clone, Debug)]
pub struct Driver {
    pub cell: Arc<LibCell>,
    pub port: usize,
}

impl Driver {
    /// The cell's first output port (none for a cell without one).
    pub fn cell_output(cell: &Arc<LibCell>) -> Option<Driver> {
        let port = cell.ports.iter().position(|p| !p.pwr_gnd && p.direction == LibDirection::Output)?;
        Some(Driver { cell: cell.clone(), port })
    }

    /// The input ports, power and ground left out, in the cell's order.
    pub fn input_ports(&self) -> impl Iterator<Item = &crate::ir::instance::LibPort> {
        self.cell.ports.iter().filter(|p| !p.pwr_gnd && p.direction == LibDirection::Input)
    }
}

/// A cell matching a function up to a permutation of its inputs: cell input port `j` (in the
/// cell's order) is fed by the function's input `perm[j]`.
#[derive(Clone, Debug)]
pub struct CellMatch {
    pub driver: Driver,
    pub perm: [i32; 6],
    pub arity: usize,
    pub area: Cost,
}

/// The timing libraries, in read order: a cell's timing is the first library's that has it.
#[derive(Default)]
pub struct Corner {
    libs: Vec<TimingLibrary>,
}

impl Corner {
    pub fn add(&mut self, lib: TimingLibrary) {
        self.libs.push(lib);
    }
    pub fn cell(&self, name: &str) -> Option<&TimingCell> {
        self.libs.iter().find_map(|l| l.cells.get(name))
    }
}

pub struct DelayEstimationParameters<'a> {
    pub nand_delay: f32,
    pub fixed_slews: [f32; 2],
    pub corner: &'a Corner,
}

/// Cell matches by (truth table, arity), kept across calls so a function seen once is not
/// canonicalized again.
pub struct MatchCache<'a> {
    nand2: Arc<LibCell>,
    index: &'a TargetIndex,
    cache: BTreeMap<(Truth6, usize), Option<CellMatch>>,
    /// The smallest area of a cell of each arity.
    min_area_for_width: Vec<Cost>,
}

/// Don't-care bits [`MatchCache::match_dc`] enumerates fills for (2^n).
const MAX_DC_FILL: u32 = 8;

impl<'a> MatchCache<'a> {
    /// The NAND2 is the smallest (area, name) cell in the 2-input NAND class reached by a pure
    /// permutation; SYN-0039 when there is none. ⚠️ The reference compares the names as POINTERS,
    /// so between NAND2s of equal area its pick is the earlier-allocated name; we compare the
    /// names themselves (no library witnessed with such a tie).
    pub fn new(index: &'a TargetIndex, max_arity: usize) -> Result<Self, ElabError> {
        let mut nand2: Option<Arc<LibCell>> = None;
        let mut semiclass_map = Npn::default();
        let nand2_canonical = npn_semiclass(0b0111, 2, &mut semiclass_map);
        if let Some(targets) = index.classes.get(&(2, nand2_canonical)) {
            for target in targets {
                if target.via.compose(&semiclass_map).c_fingerprint() == 0 {
                    let smaller = match &nand2 {
                        None => true,
                        Some(n) => {
                            target.cell.area < n.area || (target.cell.area == n.area && target.cell.name < n.name)
                        }
                    };
                    if smaller {
                        nand2 = Some(target.cell.clone());
                    }
                }
            }
        }
        let Some(nand2) = nand2 else {
            return Err(ElabError {
                code: 39,
                message: "ACD remapper requires a NAND2 specimen in the library but none was found".into(),
            });
        };

        let mut min_area_for_width = vec![INF_COST; max_arity + 1];
        for (&(arity, _), targets) in &index.classes {
            if arity > max_arity {
                continue;
            }
            for t in targets {
                if (t.cell.area as Cost) < min_area_for_width[arity] {
                    min_area_for_width[arity] = t.cell.area as Cost;
                }
            }
        }
        Ok(MatchCache { nand2, index, cache: BTreeMap::new(), min_area_for_width })
    }

    pub fn min_area_for_width(&self, w: usize) -> Cost {
        self.min_area_for_width.get(w).copied().unwrap_or(INF_COST)
    }

    pub fn inverter(&self) -> Option<&Arc<LibCell>> {
        self.index.inverter.as_ref()
    }

    pub fn nand2(&self) -> &Arc<LibCell> {
        &self.nand2
    }

    /// The smallest cell computing `tt` up to a permutation of its inputs: the class's targets in
    /// order, those whose residual transform is a pure permutation, the first of least area.
    /// Constants (arity 0) never match.
    pub fn match_tt(&mut self, tt: Truth6, arity: usize) -> Option<CellMatch> {
        if arity == 0 {
            return None;
        }
        if let Some(hit) = self.cache.get(&(tt, arity)) {
            return hit.clone();
        }
        let mut to_canonical = Npn::default();
        let canonical = npn_semiclass(tt, arity, &mut to_canonical);
        let mut best: Option<CellMatch> = None;
        if let Some(targets) = self.index.classes.get(&(arity, canonical)) {
            for target in targets {
                let residual = target.via.compose(&to_canonical).inv();
                if residual.c_fingerprint() != 0 {
                    continue;
                }
                let area = target.cell.area as Cost;
                if best.as_ref().is_none_or(|b| area < b.area) {
                    let Some(driver) = Driver::cell_output(&target.cell) else { continue };
                    let mut perm = [-1; 6];
                    perm[..arity].copy_from_slice(&residual.permutation[..arity]);
                    best = Some(CellMatch { driver, perm, arity, area });
                }
            }
        }
        self.cache.insert((tt, arity), best.clone());
        best
    }

    /// As [`MatchCache::match_tt`], free to fill the don't-care rows: every fill (counting up over
    /// the don't-care bits, from none) when there are at most eight, the first of least area; with
    /// more, the care rows as given (don't-cares 0).
    pub fn match_dc(&mut self, care_tt: Truth6, care_mask: Truth6, arity: usize) -> Option<CellMatch> {
        if arity == 0 {
            return None;
        }
        let full = mask6(arity);
        let care_mask = care_mask & full;
        let care_tt = care_tt & care_mask;
        if care_mask == full {
            return self.match_tt(care_tt, arity);
        }
        let dc = full & !care_mask;
        if dc.count_ones() > MAX_DC_FILL {
            return self.match_tt(care_tt, arity);
        }
        let mut best: Option<CellMatch> = None;
        let fill_mask = !care_mask & full;
        let mut fill: Truth6 = 0;
        let mut first = true;
        while first || fill != 0 {
            if let Some(m) = self.match_tt(care_tt | fill, arity) {
                if best.as_ref().is_none_or(|b| m.area < b.area) {
                    best = Some(m);
                }
            }
            first = false;
            fill = (fill | !fill_mask).wrapping_add(1) & fill_mask;
        }
        best
    }
}

// ---------------------------------------------------------------------------------------------
// Networks

#[derive(Clone, Debug)]
pub struct GateNode {
    pub driver_port: Driver,
    /// Per input port of the cell (in its order): (a primary input, its index) or (a node, its index).
    pub fanins: Vec<(bool, usize)>,
}

#[derive(Clone, Debug, Default)]
pub struct GateNetwork {
    pub ninputs: usize,
    /// Topologically ordered.
    pub nodes: Vec<GateNode>,
    /// Per output: (a primary input, its index) or (a node, its index).
    pub outs: Vec<(bool, usize)>,
}

/// A cell's Liberty function over a truth table per input port (a port not given is 0).
fn compose_fexpr(f: &Func, nvars: usize, port_tt: &BTreeMap<&str, Truth6>) -> Truth6 {
    match f {
        Func::Port(p) => port_tt.get(p.as_str()).copied().unwrap_or(0),
        Func::Not(a) => mask6(nvars) & !compose_fexpr(a, nvars, port_tt),
        Func::Or(a, b) => compose_fexpr(a, nvars, port_tt) | compose_fexpr(b, nvars, port_tt),
        Func::And(a, b) => compose_fexpr(a, nvars, port_tt) & compose_fexpr(b, nvars, port_tt),
        Func::Xor(a, b) => compose_fexpr(a, nvars, port_tt) ^ compose_fexpr(b, nvars, port_tt),
        Func::One => mask6(nvars),
        Func::Zero => 0,
    }
}

/// The driver port's function, parsed (`None` when it has none or it does not parse).
fn driver_function(d: &Driver) -> Option<Func> {
    let text = d.cell.ports[d.port].function.as_deref()?;
    Func::parse_in(text, |n| d.cell.ports.iter().any(|p| p.name == n))
}

/// The (possibly multi-output) truth table a network computes, each node's Liberty function
/// composed over its fanins' tables.
pub fn evaluate_function(net: &GateNetwork) -> TruthTable {
    let pi_tt = |i: usize| COFACTOR_MASKS[i] & mask6(net.ninputs);
    let mut node_tt: Vec<Truth6> = Vec::with_capacity(net.nodes.len());
    for node in &net.nodes {
        let mut cell_inputs: BTreeMap<&str, Truth6> = BTreeMap::new();
        for (idx, p) in node.driver_port.input_ports().enumerate() {
            let (is_pi, k) = node.fanins[idx];
            cell_inputs.insert(p.name.as_str(), if is_pi { pi_tt(k) } else { node_tt[k] });
        }
        let tt = driver_function(&node.driver_port).map_or(0, |f| compose_fexpr(&f, net.ninputs, &cell_inputs));
        node_tt.push(tt);
    }
    let mut result = TruthTable::new((0..net.ninputs).collect(), net.outs.len(), false, false);
    for (i, &(is_pi, idx)) in net.outs.iter().enumerate() {
        let tt = if is_pi { pi_tt(idx) } else { node_tt[idx] };
        for j in 0..1usize << net.ninputs {
            result.set_value(i, j, (tt >> j) & 1 != 0);
        }
    }
    result
}

// ---------------------------------------------------------------------------------------------
// Timing on the Liberty gate tables

/// `LibertyPort::capacitance()`: the largest of its rise/fall × min/max values.
fn port_cap(p: &vyges_sta::liberty::Port) -> f32 {
    let c = &p.capacitance;
    max_f(max_f(c[RISE][0], c[RISE][1]), max_f(c[FALL][0], c[FALL][1]))
}

/// A timing cell's signal input ports, in its order.
fn timing_inputs(cell: &TimingCell) -> impl Iterator<Item = &vyges_sta::liberty::Port> {
    cell.ports.iter().filter(|p| p.direction.is_input())
}

/// The output's arrival sets, from its input ports' (in the cell's input order): for each
/// non-check arc into the output from an input port, the input transition's set plus the gate
/// delay at the fixed slew of that transition and `load`, merged by max into the arc's output
/// transition. Arcs from a port that is not an input (output → output) are skipped.
pub fn output_arrival(
    out_port: &Driver,
    input_pin_arrivals: &[NodeArrivals],
    load: f32,
    corner: &Corner,
    fixed_slew: [f32; 2],
) -> NodeArrivals {
    let mut result = NodeArrivals::default();
    let Some(cell) = corner.cell(&out_port.cell.name) else { return result };
    let out_name = &out_port.cell.ports[out_port.port].name;
    let in_ports: Vec<&str> = timing_inputs(cell).map(|p| p.name.as_str()).collect();
    for arc_set in &cell.arc_sets {
        if &arc_set.to != out_name || arc_set.role.is_timing_check() {
            continue;
        }
        for arc in &arc_set.arcs {
            let Model::Gate(model) = &arc.model else { continue };
            let Some(in_idx) = in_ports.iter().position(|n| *n == arc_set.from) else { continue };
            let (gate_delay, _drvr_slew) = model.gate_delay(fixed_slew[arc.from_rf], load);
            let shifted = input_pin_arrivals[in_idx].at_transition(arc.from_rf).plus(gate_delay);
            result.at_transition_mut(arc.to_rf).merge_max(&shifted);
        }
    }
    result
}

/// The mean input pin capacitance of a cell (0 with no inputs).
pub fn avg_input_cap(cell: &TimingCell) -> f32 {
    let mut sum = 0.0f32;
    let mut n = 0;
    for p in timing_inputs(cell) {
        sum += port_cap(p);
        n += 1;
    }
    if n > 0 {
        sum / n as f32
    } else {
        0.0
    }
}

/// The least gate delay over every non-check arc of the cell, at the fixed slews and twice its
/// mean input capacitance as load.
pub fn find_delay_lower_bound(corner: &Corner, cell_name: &str, fixed_slew: [f32; 2]) -> f32 {
    let mut bound = f32::INFINITY;
    let Some(cell) = corner.cell(cell_name) else { return bound };
    let avg_cin = avg_input_cap(cell);
    for arc_set in cell.arc_sets.iter().filter(|s| !s.role.is_timing_check()) {
        for arc in &arc_set.arcs {
            let Model::Gate(model) = &arc.model else { continue };
            let (gate_delay, _) = model.gate_delay(fixed_slew[arc.from_rf], 2.0 * avg_cin);
            bound = min_f(bound, gate_delay);
        }
    }
    bound
}

/// The worst slack of a network under a problem's timing: loads are each output's external load
/// plus the input pin caps each node drives; arrivals propagate node by node; the slack is the
/// least of minus each output's rise→rise and fall→fall entry.
pub fn network_slack(problem: &SynthesisProblem, net: &GateNetwork, corner: &Corner, fixed_slew: [f32; 2]) -> f32 {
    let mut load = vec![0.0f32; net.nodes.len()];
    for i in 0..problem.num_outputs() {
        let (is_pi, gate_idx) = net.outs[i];
        if !is_pi {
            load[gate_idx] += problem.output(i).external_load;
        }
    }
    for node in &net.nodes {
        let Some(cell) = corner.cell(&node.driver_port.cell.name) else { continue };
        for (port_idx, port) in timing_inputs(cell).enumerate() {
            let (is_pi, idx) = node.fanins[port_idx];
            if !is_pi {
                load[idx] += port_cap(port);
            }
        }
    }

    let mut node_arrivals: Vec<NodeArrivals> = vec![NodeArrivals::default(); net.nodes.len()];
    for (i, node) in net.nodes.iter().enumerate() {
        let inputs: Vec<NodeArrivals> = node
            .fanins
            .iter()
            .map(|&(is_pi, k)| if is_pi { problem.input(k).arrivals } else { node_arrivals[k] })
            .collect();
        node_arrivals[i] = output_arrival(&node.driver_port, &inputs, load[i], corner, fixed_slew);
    }

    let mut ws = f32::INFINITY;
    for (i, &(is_pi, k)) in net.outs.iter().enumerate() {
        let arrivals = if is_pi { problem.input(k).arrivals } else { node_arrivals[k] };
        for rf in RISE_FALL {
            ws = min_f(ws, -arrivals.at_transition(rf).at_exit(i, rf));
        }
    }
    ws
}

// ---------------------------------------------------------------------------------------------
// The search

const MAX_RECURSION_DEPTH: usize = 8;

/// A lower bound on the area of a function of `nvars` inputs: cells of the widest arity first,
/// each `w`-input cell removing `w − 1` variables.
fn lut_min_cost(mc: &MatchCache, max_width: usize, mut nvars: usize) -> Cost {
    if nvars == 0 {
        return 0.0;
    }
    let mut cost = 0.0;
    for w in (2..=max_width).rev() {
        let per = mc.min_area_for_width(w);
        if per >= INF_COST {
            continue;
        }
        let n = (nvars - 1) / (w - 1);
        cost += n as Cost * per;
        nvars -= n * (w - 1);
        if nvars <= 1 {
            break;
        }
    }
    cost
}

struct Fragment {
    /// The bound columns that determine this fragment.
    column_bound_idx: Vec<usize>,
    bs_high: u32,
    bs_low: u32,
}

/// Columns `b1` and `b2` agree wherever both are care, on every output; `b1_refined` set when
/// `b2` is care somewhere `b1` is not.
fn columns_match(tt: &TruthTable, fraglen: usize, b1: usize, b2: usize, b1_refined: &mut bool) -> bool {
    let mut refining = false;
    for out in 0..tt.num_outputs() {
        for i in 0..fraglen {
            let m1 = b1 * fraglen + i;
            let m2 = b2 * fraglen + i;
            if tt.dont_care(out, m1) && !tt.dont_care(out, m2) {
                refining = true;
            }
            if !tt.dont_care(out, m1) && !tt.dont_care(out, m2) && tt.value(out, m1) != tt.value(out, m2) {
                return false;
            }
        }
    }
    if refining {
        *b1_refined = true;
    }
    true
}

fn fragment_matches(tt: &TruthTable, frag: &Fragment, fraglen: usize, candidate_b: usize, refined: &mut bool) -> bool {
    if frag.column_bound_idx.is_empty() {
        return false;
    }
    frag.column_bound_idx.iter().all(|&b1| columns_match(tt, fraglen, b1, candidate_b, refined))
}

struct FragmentSet {
    fragments: Vec<Fragment>,
    /// Bound-set value → its fragment.
    fragment_map: Vec<usize>,
}

/// The distinct columns over the top `bn` variables, first fit in column order: a column joins the
/// first fragment all of whose determining columns it agrees with (and becomes one of them when it
/// refines one), else starts a fragment.
fn find_fragments(tt: &TruthTable, bn: usize) -> FragmentSet {
    let fnv = tt.num_variables() - bn;
    let fraglen = 1 << fnv;
    let bs_mask: u32 = (1u32 << bn) - 1;
    let mut result = FragmentSet { fragments: Vec::new(), fragment_map: vec![usize::MAX; 1 << bn] };
    for b in 0..1usize << bn {
        let mut matched = false;
        for fi in 0..result.fragments.len() {
            let mut refined = false;
            if fragment_matches(tt, &result.fragments[fi], fraglen, b, &mut refined) {
                let frag = &mut result.fragments[fi];
                if refined {
                    frag.column_bound_idx.push(b);
                }
                frag.bs_high |= b as u32;
                frag.bs_low |= bs_mask & !(b as u32);
                result.fragment_map[b] = fi;
                matched = true;
                break;
            }
        }
        if !matched {
            result.fragment_map[b] = result.fragments.len();
            result.fragments.push(Fragment {
                column_bound_idx: vec![b],
                bs_high: b as u32,
                bs_low: bs_mask & !(b as u32),
            });
        }
    }
    result
}

/// `f` restricted to the outputs at `keep`, in that order.
fn project_outputs(f: &TruthTable, keep: &[usize]) -> TruthTable {
    let mut g = TruthTable::new(f.variables().to_vec(), keep.len(), false, false);
    for (o, &src) in keep.iter().enumerate() {
        for m in 0..f.num_minterms() {
            g.set_value(o, m, f.value(src, m));
            g.set_dont_care(o, m, f.dont_care(src, m));
        }
    }
    g
}

/// One level of decomposition: a decoder cell (none at a leaf), the rest of the chain, or two
/// independent chains once the outputs stop sharing structure.
#[derive(Default)]
struct Round {
    driver: Option<Driver>,
    /// Variable ids feeding the cell's input ports, in port order.
    inputs: Vec<usize>,
    /// The variable id the cell drives.
    output: usize,
    /// Per output of this round's function: the variable it passes through, or `None` when `next`
    /// or `split` produces it.
    out_passthrough: Vec<Option<usize>>,
    next: Option<Box<Round>>,
    split: Vec<Round>,
    cost: Cost,
}

fn swap_vars6(t: Truth6, i: usize, j: usize) -> Truth6 {
    if i == j {
        return t;
    }
    let (i, j) = if i > j { (j, i) } else { (i, j) };
    let mi = COFACTOR_MASKS[i];
    let mj = COFACTOR_MASKS[j];
    let stay = t & !(mi ^ mj);
    let i1j0 = t & mi & !mj;
    let i0j1 = t & !mi & mj;
    let d = (1 << j) - (1 << i);
    stay | (i1j0 << d) | (i0j1 >> d)
}

/// A class id per input position; positions sharing one are interchangeable (the don't-care set
/// invariant under the swap, the care values agreeing). Union-find over pairs in order, the
/// first's root linked under the second's.
fn symmetry_classes(f: &TruthTable) -> Vec<usize> {
    let nv = f.num_variables();
    let nm = 1usize << nv;
    let fmask = mask6(nv);
    let mut val = vec![0 as Truth6; f.num_outputs()];
    let mut dc = vec![0 as Truth6; f.num_outputs()];
    for o in 0..f.num_outputs() {
        for m in 0..nm {
            if f.value(o, m) {
                val[o] |= 1 << m;
            }
            if f.dont_care(o, m) {
                dc[o] |= 1 << m;
            }
        }
    }
    let symmetric = |i: usize, j: usize| -> bool {
        for o in 0..f.num_outputs() {
            if (swap_vars6(dc[o], i, j) & fmask) != (dc[o] & fmask) {
                return false;
            }
            let care = fmask & !dc[o];
            if ((swap_vars6(val[o], i, j) ^ val[o]) & care) != 0 {
                return false;
            }
        }
        true
    };
    let mut parent: Vec<usize> = (0..nv).collect();
    fn find(parent: &mut [usize], mut x: usize) -> usize {
        while parent[x] != x {
            parent[x] = parent[parent[x]];
            x = parent[x];
        }
        x
    }
    for i in 0..nv {
        for j in i + 1..nv {
            if symmetric(i, j) {
                let ri = find(&mut parent, i);
                let rj = find(&mut parent, j);
                parent[ri] = rj;
            }
        }
    }
    (0..nv).map(|i| find(&mut parent, i)).collect()
}

struct Objective {
    min_slacks: [f32; 2],
    slack_cost_factor: [f64; 2],
}

/// The table's bits as hex nibbles, four bits each, lowest index first (values, or don't-cares).
fn hexdump(tt: &TruthTable, dump_dontcares: bool) -> String {
    let mut ret = String::new();
    let mut i = 0;
    while i < tt.size() {
        let mut nibble = 0u8;
        for j in i..(i + 4).min(tt.size()) {
            let (output, minterm) = (j / tt.num_minterms(), j % tt.num_minterms());
            let bit = if dump_dontcares { tt.dont_care(output, minterm) } else { tt.value(output, minterm) };
            if bit {
                nibble |= 1 << (j - i);
            }
        }
        ret.push(if nibble < 10 { (b'0' + nibble) as char } else { (b'A' - 10 + nibble) as char });
        i += 4;
    }
    ret
}

/// Per symmetry class (at most three: six inputs, two members each), how many members have been
/// bound so far.
#[derive(Clone, Copy, Default)]
struct SiTracking {
    sym_classes_consumed: [usize; 3],
}

struct Search<'s, 'a> {
    debug: &'s mut DebugLog,
    mc: &'s mut MatchCache<'a>,
    dparams: &'s DelayEstimationParameters<'s>,
    problem: &'s SynthesisProblem,
    objective: Objective,
    max_bound_width: usize,
    /// Off: only rounds that reduce the variable count (no lateral factor-out).
    lateral_enabled: bool,
    next_var: usize,
    /// Per input variable id: (its symmetry class among the classes of two or more, its rank in
    /// that class), or (−1, 0).
    sym_info: Vec<(i32, usize)>,
    timing: bool,
    explore_calls: i64,
    /// Estimated arrivals per variable id.
    arrivals: Vec<NodeArrivals>,
}

impl<'s, 'a> Search<'s, 'a> {
    /// Inputs are variables `0..n` in order. Symmetry classes are found once on the whole
    /// function; within a class the members are ranked by most slack first (least max arrival)
    /// when timing, else by id, a stable sort on (class root, that key).
    fn new(
        debug: &'s mut DebugLog,
        mc: &'s mut MatchCache<'a>,
        dparams: &'s DelayEstimationParameters<'s>,
        problem: &'s SynthesisProblem,
        objective: Objective,
        max_bound_width: usize,
        lateral_enabled: bool,
    ) -> Self {
        let timing = !(objective.slack_cost_factor[0] == 0.0 && objective.slack_cost_factor[1] == 0.0);
        let mut s = Search {
            debug,
            mc,
            dparams,
            problem,
            objective,
            max_bound_width,
            lateral_enabled,
            next_var: problem.num_inputs(),
            sym_info: Vec::new(),
            timing,
            explore_calls: 0,
            arrivals: Vec::new(),
        };
        if s.timing {
            for i in 0..problem.num_inputs() {
                s.set_arrivals(i, problem.input(i).arrivals);
            }
        }

        let classes = symmetry_classes(problem.function());
        let mut classified: Vec<(usize, usize)> =
            (0..problem.num_inputs()).map(|i| (problem.function().variable(i), classes[i])).collect();
        let less = |a: &(usize, usize), b: &(usize, usize)| -> bool {
            if a.1 != b.1 {
                return a.1 < b.1;
            }
            if s.timing {
                s.arrivals[a.0].max_entry() < s.arrivals[b.0].max_entry()
            } else {
                a.0 < b.0
            }
        };
        classified.sort_by(|a, b| {
            if less(a, b) {
                std::cmp::Ordering::Less
            } else if less(b, a) {
                std::cmp::Ordering::Greater
            } else {
                std::cmp::Ordering::Equal
            }
        });

        let mut small_class_id = 0i32;
        s.sym_info = vec![(-1, 0); problem.num_inputs()];
        let mut i = 0;
        while i < classified.len() {
            let class = classified[i].1;
            let mut size = 1;
            while i + size < classified.len() && classified[i + size].1 == class {
                size += 1;
            }
            if size > 1 {
                for j in 0..size {
                    s.sym_info[classified[i + j].0] = (small_class_id, j);
                }
                if s.debug.check_acd(3) {
                    let members: String = (0..size).map(|j| format!("{} ", classified[i + j].0)).collect();
                    s.debug.print_acd(2, format!("symmetry set {small_class_id}: {members}"));
                }
                small_class_id += 1;
            }
            i += size;
        }
        s
    }

    fn run(&mut self, budget: Cost) -> Option<Box<Round>> {
        let global_output_ids: Vec<usize> = (0..self.problem.num_outputs()).collect();
        let f = self.problem.function().clone();
        self.recurse(f, &global_output_ids, 0, true, budget, &SiTracking::default())
    }

    /// Bound input variables of a symmetry class must be taken in rank order: those bound here
    /// must be exactly the next ranks after the ones already consumed.
    fn consume_symmetric_inputs(&self, prior: &SiTracking, updated: &mut SiTracking, bound_vars: &[usize]) -> bool {
        *updated = *prior;
        for &v in bound_vars {
            if v < self.problem.num_inputs() {
                let (cb, _) = self.sym_info[v];
                if cb >= 0 {
                    updated.sym_classes_consumed[cb as usize] += 1;
                }
            }
        }
        for &v in bound_vars {
            if v < self.problem.num_inputs() {
                let (cb, pb) = self.sym_info[v];
                if cb >= 0 && (pb < prior.sym_classes_consumed[cb as usize] || pb >= updated.sym_classes_consumed[cb as usize]) {
                    return false;
                }
            }
        }
        true
    }

    fn sym_class(&self, var: usize) -> (i32, usize) {
        if var >= self.problem.num_inputs() {
            (-1, 0)
        } else {
            self.sym_info[var]
        }
    }

    /// A cell's output arrivals with a load of twice its mean input capacitance.
    fn cell_delay(&self, output: &Driver, input_arrivals: &[NodeArrivals]) -> NodeArrivals {
        let load = self.dparams.corner.cell(&output.cell.name).map_or(0.0, avg_input_cap) * 2.0;
        output_arrival(output, input_arrivals, load, self.dparams.corner, self.dparams.fixed_slews)
    }

    fn set_arrivals(&mut self, var: usize, a: NodeArrivals) {
        if var >= self.arrivals.len() {
            self.arrivals.resize(var + 1, NodeArrivals::default());
        }
        self.arrivals[var] = a;
    }

    /// The best slack output `output` could have from these variables: the least of minus every
    /// entry toward it, less one NAND delay. 0 without timing.
    fn slack_upper_bound(&self, vars: &[usize], output: usize) -> f32 {
        let mut slack = f32::INFINITY;
        if !self.timing {
            return 0.0;
        }
        for &idx in vars {
            for rf1 in RISE_FALL {
                for rf2 in RISE_FALL {
                    slack = min_f(slack, -self.arrivals[idx].at_transition(rf1).at_exit(output, rf2));
                }
            }
        }
        slack - self.dparams.nand_delay
    }

    fn indent(depth: usize) -> String {
        " ".repeat(depth * 2)
    }

    /// One node of the search: peel passthrough outputs, shrink to support, bound by cost; then a
    /// single cell for a single output (don't-cares filled freely), every bound set of each width
    /// from 2, and at depth ≥ 1 with two outputs, the two decomposed apart.
    fn recurse(
        &mut self,
        f: TruthTable,
        f_output_ids: &[usize],
        depth: usize,
        allow_lateral: bool,
        mut budget: Cost,
        prior_si: &SiTracking,
    ) -> Option<Box<Round>> {
        self.explore_calls += 1;
        if depth > MAX_RECURSION_DEPTH {
            self.debug.print_acd(2, format!("{}depth limit reached", Self::indent(depth)));
            return None;
        }

        let mut npeeled = 0;
        let mut out_passthrough: Vec<Option<usize>> = vec![None; f.num_outputs()];
        let mut kept_positions = Vec::new();
        let mut kept_outputs = Vec::new();
        for i in 0..f.num_outputs() {
            if let Some(v) = f.output_passthrough(i) {
                out_passthrough[i] = Some(f.variable(v));
                npeeled += 1;
            } else {
                kept_positions.push(i);
                kept_outputs.push(f_output_ids[i]);
            }
        }

        if kept_outputs.is_empty() {
            let mut r = Round { out_passthrough, ..Round::default() };
            if self.timing {
                for (i, &idx) in f_output_ids.iter().enumerate().take(f.num_outputs()) {
                    let v = r.out_passthrough[i].expect("every output peeled");
                    r.cost += self.arrivals[v].exit_slack(idx) as f64 * self.objective.slack_cost_factor[idx];
                }
            }
            if r.cost >= budget {
                return None;
            }
            return Some(Box::new(r));
        }
        let mut f = project_outputs(&f, &kept_positions);
        f.shrink_to_support();
        let f_output_ids: &[usize] = &kept_outputs;

        if self.debug.check_acd(2) {
            let line = if f.has_dontcares() {
                format!(
                    "{}{} (dontcare {}) nvars={} npeeled={}",
                    Self::indent(depth),
                    hexdump(&f, false),
                    hexdump(&f, true),
                    f.num_variables(),
                    npeeled
                )
            } else {
                format!("{}{} nvars={} npeeled={}", Self::indent(depth), hexdump(&f, false), f.num_variables(), npeeled)
            };
            self.debug.print_acd(2, line);
        }

        if f.num_variables() == 0 {
            return None;
        }

        let mut slack_cost: Cost = 0.0;
        for &idx in f_output_ids {
            let out_slack = self.slack_upper_bound(f.variables(), idx);
            if out_slack < self.objective.min_slacks[idx] {
                return None;
            }
            slack_cost += out_slack as f64 * self.objective.slack_cost_factor[idx];
        }

        let lb = slack_cost + lut_min_cost(self.mc, self.max_bound_width, f.num_variables());
        if lb >= budget {
            self.debug.print_acd(2, format!("{}  reject by lower cost bound", Self::indent(depth)));
            return None;
        }

        let mut best_decomp: Option<Box<Round>> = None;

        if f.num_outputs() == 1 {
            if let Some(leaf) = self.leaf_match(&f, f_output_ids[0], budget, depth) {
                let mut leaf = leaf;
                leaf.out_passthrough = out_passthrough;
                return Some(leaf);
            }
        }

        let mut bn = 2;
        while bn <= self.max_bound_width && bn <= f.num_variables() {
            if slack_cost + self.mc.min_area_for_width(bn) >= budget {
                break;
            }
            let fnv = f.num_variables() - bn;
            if fnv == 0 {
                // Bound = every variable: one bound set, tried once.
                if let Some(c) = self.try_bound_choice(&f, f_output_ids, bn, fnv, budget, depth, allow_lateral, prior_si) {
                    if c.cost < budget {
                        budget = c.cost;
                        best_decomp = Some(c);
                    }
                }
                bn += 1;
                continue;
            }
            self.bound_sets(&f, f_output_ids, bn, fnv, &mut budget, depth, allow_lateral, prior_si, &mut best_decomp);
            bn += 1;
        }

        if depth >= 1 && f.num_outputs() == 2 {
            let f0 = project_outputs(&f, &[0]);
            let f1 = project_outputs(&f, &[1]);
            self.debug.print_acd(3, format!("{} splitting", Self::indent(depth)));
            let b0 = budget - self.objective.slack_cost_factor[1] * self.slack_upper_bound(f.variables(), 1) as f64;
            // ⚠️ The split children are told they are outputs 0 and 1 literally, not `f_output_ids`.
            if let Some(s0) = self.recurse(f0, &[0], depth + 1, allow_lateral, b0, prior_si) {
                let b1 = budget - s0.cost;
                if let Some(s1) = self.recurse(f1, &[1], depth + 1, allow_lateral, b1, prior_si) {
                    // ⚠️ Replaces any bound-set solution without comparing: the budgets above
                    // already hold it below the best so far.
                    best_decomp = Some(Box::new(Round { cost: s0.cost + s1.cost, split: vec![*s0, *s1], ..Round::default() }));
                }
            }
        }

        let mut best = best_decomp?;
        best.out_passthrough = out_passthrough;
        Some(best)
    }

    /// The leaf base case: the whole single-output function as one cell. Its output variable id is
    /// taken only when it is accepted.
    fn leaf_match(&mut self, f: &TruthTable, out_id: usize, budget: Cost, depth: usize) -> Option<Box<Round>> {
        let nvars = f.num_variables();
        let mut care_tt: Truth6 = 0;
        let mut care_mask: Truth6 = 0;
        for m in 0..1usize << nvars {
            if !f.dont_care(0, m) {
                care_mask |= 1 << m;
                if f.value(0, m) {
                    care_tt |= 1 << m;
                }
            }
        }
        let cm = self.mc.match_dc(care_tt, care_mask, nvars)?;
        let port_vars: Vec<usize> = (0..cm.arity).map(|j| f.variable(cm.perm[j] as usize)).collect();
        let (solution_cost, leaf_arr) = if self.timing {
            let port_in: Vec<NodeArrivals> = port_vars.iter().map(|&v| self.arrivals[v]).collect();
            let arr = self.cell_delay(&cm.driver, &port_in);
            (cm.area + arr.exit_slack(out_id) as f64 * self.objective.slack_cost_factor[out_id], arr)
        } else {
            (cm.area, NodeArrivals::default())
        };
        if solution_cost >= budget {
            return None;
        }
        let id = self.next_var;
        self.next_var += 1;
        if self.timing {
            self.set_arrivals(id, leaf_arr);
        }
        self.debug.print_acd(
            2,
            format!("{} exact match {} accepted (cost={})", Self::indent(depth), cm.driver.cell.name, fmt_double(solution_cost)),
        );
        Some(Box::new(Round {
            driver: Some(cm.driver),
            inputs: port_vars,
            output: id,
            next: Some(Box::new(Round { out_passthrough: vec![Some(id)], ..Round::default() })),
            cost: solution_cost,
            ..Round::default()
        }))
    }

    /// Every `bn`-subset of the variables as the top `bn` positions, in the order a chain of swaps
    /// visits them (`p[level]` the free position swapped in at each bound position); a subset whose
    /// symmetric inputs are out of rank order is skipped.
    #[allow(clippy::too_many_arguments)]
    fn bound_sets(
        &mut self,
        f: &TruthTable,
        f_output_ids: &[usize],
        bn: usize,
        fnv: usize,
        budget: &mut Cost,
        depth: usize,
        allow_lateral: bool,
        prior_si: &SiTracking,
        best_decomp: &mut Option<Box<Round>>,
    ) {
        let mut cur = f.clone();
        let mut p = vec![0usize; bn];
        let mut level: isize = bn as isize - 1;
        loop {
            let bs: Vec<usize> = cur.variables()[fnv..fnv + bn].to_vec();
            let mut updated_si = SiTracking::default();
            if self.consume_symmetric_inputs(prior_si, &mut updated_si, &bs) {
                if self.debug.check_acd(3) {
                    let text: String = bs.iter().map(|v| format!("{v} ")).collect();
                    self.debug.print_acd(3, format!("{} bs {text}", Self::indent(depth)));
                }
                if let Some(c) = self.try_bound_choice(&cur, f_output_ids, bn, fnv, *budget, depth, allow_lateral, &updated_si) {
                    if c.cost < *budget {
                        *budget = c.cost;
                        *best_decomp = Some(c);
                    }
                }
            } else if self.debug.check_acd(3) {
                let text: String = bs.iter().map(|v| format!("{v} ")).collect();
                self.debug.print_acd(3, format!("{} bs {text}redundant by symmetry", Self::indent(depth)));
            }

            if level < 0 {
                break;
            }
            let l = level as usize;
            cur.swap_vars(fnv + l, p[l]);
            p[l] += 1;
            if p[l] == fnv {
                level -= 1;
            } else {
                while (level as usize) < bn - 1 {
                    let l = level as usize;
                    p[l + 1] = p[l];
                    level += 1;
                }
            }
        }
    }

    /// One bound set (the top `bn` positions of `g`): at most four fragments (one or two decoder
    /// bits); with two, one bound variable is shared with the upper function — each choice of it,
    /// skipping a choice symmetric to an earlier one. Fragments get a slot (0 or 1) per shared
    /// value group in first-seen order; each of the `2^groups` slot flips is a decoder function,
    /// shrunk to its support and matched to a cell; the upper function is then searched with the
    /// remaining budget. A lateral round (no fewer variables) needs a 2-input decoder at least and
    /// forbids another lateral round right below it.
    #[allow(clippy::too_many_arguments)]
    fn try_bound_choice(
        &mut self,
        g: &TruthTable,
        f_output_ids: &[usize],
        bn: usize,
        fnv: usize,
        mut budget: Cost,
        depth: usize,
        allow_lateral: bool,
        prior_si: &SiTracking,
    ) -> Option<Box<Round>> {
        let nvars = g.num_variables();
        let fset = find_fragments(g, bn);
        let nfrags = fset.fragments.len();
        let ndecoding_luts_raw = if nfrags > 1 { (usize::BITS - (nfrags - 1).leading_zeros()) as usize } else { 0 };
        if !(1..=2).contains(&ndecoding_luts_raw) {
            return None;
        }

        let mut best_local: Option<Round> = None;
        let (sh_first, sh_last): (isize, isize) = if ndecoding_luts_raw == 1 { (-1, -1) } else { (0, bn as isize - 1) };
        for sh in sh_first..=sh_last {
            if sh >= 0 {
                let sh_cls = self.sym_class(g.variable(fnv + sh as usize)).0;
                let redundant =
                    (0..sh as usize).any(|sh2| sh_cls >= 0 && self.sym_class(g.variable(fnv + sh2)).0 == sh_cls);
                if redundant {
                    continue;
                }
            }
            let shmask: u32 = if sh < 0 { 0 } else { 1 << sh };
            let nshared = if sh < 0 { 0 } else { 1 };
            let ngroups = 1usize << nshared;

            let lateral = fnv + 1 + nshared == nvars;
            if lateral && (!allow_lateral || !self.lateral_enabled) {
                continue;
            }

            let mut group_frags: [Vec<usize>; 2] = [Vec::new(), Vec::new()];
            let mut group_of = vec![0usize; 1 << bn];
            let mut slot_of = vec![0usize; 1 << bn];
            let mut feasible = true;
            for b in 0..1usize << bn {
                let grp = if shmask != 0 { (b >> sh) & 1 } else { 0 };
                let frag = fset.fragment_map[b];
                let slots = &mut group_frags[grp];
                let slot = match slots.iter().position(|&x| x == frag) {
                    Some(s) => s,
                    None => {
                        if slots.len() >= 2 {
                            feasible = false;
                            break;
                        }
                        slots.push(frag);
                        slots.len() - 1
                    }
                };
                group_of[b] = grp;
                slot_of[b] = slot;
            }
            if !feasible {
                continue;
            }

            for flip in 0..1usize << ngroups {
                let mut decoder: Truth6 = 0;
                let mut bound_to_code = vec![0i32; 1 << bn];
                for b in 0..1usize << bn {
                    let code = (((flip >> group_of[b]) & 1) ^ slot_of[b]) as i32;
                    bound_to_code[b] = code;
                    if code != 0 {
                        decoder |= 1 << b;
                    }
                }

                let bound_var_indices: Vec<usize> = (0..bn)
                    .filter(|&v| {
                        let mv = COFACTOR_MASKS[v];
                        (decoder & !mv) != ((decoder & mv) >> (1 << v))
                    })
                    .collect();
                let arity = bound_var_indices.len();
                if arity == 0 || (lateral && arity < 2) {
                    continue;
                }
                let mut shrunk: Truth6 = 0;
                for b in 0..1usize << bn {
                    if decoder & (1 << b) == 0 {
                        continue;
                    }
                    let mut nb = 0;
                    for (k, &bv) in bound_var_indices.iter().enumerate() {
                        if b & (1 << bv) != 0 {
                            nb |= 1 << k;
                        }
                    }
                    shrunk |= 1 << nb;
                }
                shrunk &= mask6(arity);

                let Some(m) = self.mc.match_tt(shrunk, arity) else { continue };
                let decoding_cost = m.area;
                let port_vars: Vec<usize> =
                    (0..arity).map(|j| g.variable(fnv + bound_var_indices[m.perm[j] as usize])).collect();

                // A fresh id for the decoder's output, taken whether or not the round succeeds.
                let dec = self.next_var;
                self.next_var += 1;
                if self.timing {
                    let port_in: Vec<NodeArrivals> = port_vars.iter().map(|&v| self.arrivals[v]).collect();
                    let a = self.cell_delay(&m.driver, &port_in);
                    self.set_arrivals(dec, a);
                }

                let upper = build_upper_function(g, bn, fnv, 1, shmask, nshared, &bound_to_code, dec);
                let Some(sub) = self.recurse(upper, f_output_ids, depth + 1, !lateral, budget - decoding_cost, prior_si)
                else {
                    continue;
                };
                budget = sub.cost + decoding_cost;
                best_local = Some(Round {
                    driver: Some(m.driver),
                    inputs: port_vars,
                    output: dec,
                    cost: sub.cost + decoding_cost,
                    next: Some(sub),
                    ..Round::default()
                });
            }
        }
        best_local.map(Box::new)
    }
}

/// The function above a round: variables are the free ones, the decoder outputs, then the shared
/// bound variables; every entry starts as a don't-care 1, and each bound column writes its free
/// rows at its code — a care value overwrites, a don't-care never overwrites a care one.
#[allow(clippy::too_many_arguments)]
fn build_upper_function(
    f: &TruthTable,
    bn: usize,
    fnv: usize,
    ndecoding_luts: usize,
    shmask: u32,
    nshared: usize,
    bound_to_code: &[i32],
    varcounter: usize,
) -> TruthTable {
    let mut variables = Vec::with_capacity(fnv + ndecoding_luts + nshared);
    variables.extend((0..fnv).map(|i| f.variable(i)));
    variables.extend((0..ndecoding_luts).map(|i| varcounter + i));
    variables.extend((0..bn).filter(|&i| shmask & (1 << i) != 0).map(|i| f.variable(fnv + i)));
    let mut up = TruthTable::new(variables, f.num_outputs(), true, true);

    let fraglen = 1 << fnv;
    for out in 0..f.num_outputs() {
        for (b, &code) in bound_to_code.iter().enumerate().take(1 << bn) {
            if code < 0 {
                continue;
            }
            let mut shared_part = 0;
            let mut sh_pos = 0;
            for i in 0..bn {
                if shmask & (1 << i) != 0 {
                    if b & (1 << i) != 0 {
                        shared_part |= 1 << sh_pos;
                    }
                    sh_pos += 1;
                }
            }
            for free_idx in 0..fraglen {
                let up_idx = free_idx | ((code as usize) << fnv) | (shared_part << (fnv + ndecoding_luts));
                let src = b * fraglen + free_idx;
                let src_is_dc = f.dont_care(out, src);
                let dst_is_dc = up.dont_care(out, up_idx);
                if dst_is_dc || !src_is_dc {
                    up.set_value(out, up_idx, f.value(out, src));
                    up.set_dont_care(out, up_idx, src_is_dc);
                }
            }
        }
    }
    up
}

// ---------------------------------------------------------------------------------------------
// Emission

/// Walks a round chain into a network: each round's cell (its inputs resolved to primary inputs
/// or cells already emitted), then the rest of the chain; split children in order, sharing the
/// bindings.
struct Emitter<'n> {
    out: &'n mut GateNetwork,
    /// Decoder variable id → its node.
    binding: BTreeMap<usize, (bool, usize)>,
}

impl<'n> Emitter<'n> {
    fn new(ninputs: usize, out: &'n mut GateNetwork) -> Self {
        out.ninputs = ninputs;
        out.nodes.clear();
        out.outs.clear();
        Emitter { out, binding: BTreeMap::new() }
    }

    fn emit(&mut self, r: &Round) -> Vec<(bool, usize)> {
        if let Some(driver) = &r.driver {
            let fanins = r.inputs.iter().map(|&v| self.resolve(v)).collect();
            self.binding.insert(r.output, (false, self.out.nodes.len()));
            self.out.nodes.push(GateNode { driver_port: driver.clone(), fanins });
        }
        let mut inner: Vec<(bool, usize)> = Vec::new();
        if !r.split.is_empty() {
            for child in &r.split {
                let refs = self.emit(child);
                inner.push(refs[0]);
            }
        } else if let Some(next) = &r.next {
            inner = self.emit(next);
        }
        let mut kept = 0;
        r.out_passthrough
            .iter()
            .map(|p| match p {
                Some(v) => self.resolve(*v),
                None => {
                    kept += 1;
                    inner[kept - 1]
                }
            })
            .collect()
    }

    fn resolve(&self, vid: usize) -> (bool, usize) {
        if vid < self.out.ninputs {
            return (true, vid);
        }
        *self.binding.get(&vid).expect("a decoder output is emitted before it is used")
    }
}

fn emit_network_for_solution(ninputs: usize, round: &Round) -> GateNetwork {
    let mut network = GateNetwork::default();
    let outs = Emitter::new(ninputs, &mut network).emit(round);
    network.outs = outs;
    network
}

/// Synthesize `problem`'s function into a network of library cells: `Ok(None)` when no
/// decomposition fits the budget; SYN-0067 for more than two outputs. Critical outputs weigh
/// their slack by `−effort` in the cost; with none critical the search is area only.
#[allow(clippy::too_many_arguments)]
pub fn synthesize(
    problem: &SynthesisProblem,
    mc: &mut MatchCache,
    dparams: &DelayEstimationParameters,
    debug: &mut DebugLog,
    budget: f64,
    allow_lateral: bool,
    explore_calls: Option<&mut i64>,
    effort: f32,
) -> Result<Option<GateNetwork>, ElabError> {
    if problem.num_outputs() > 2 {
        return Err(ElabError {
            code: 67,
            message: format!("ACD remapper is limited to up to 2 outputs but problem has {}", problem.num_outputs()),
        });
    }
    let mut objective = Objective { min_slacks: [f32::NEG_INFINITY; 2], slack_cost_factor: [0.0; 2] };
    for i in 0..problem.num_outputs().min(2) {
        objective.slack_cost_factor[i] = if problem.output(i).critical { -effort as f64 } else { 0.0 };
    }
    let mut ex = Search::new(debug, mc, dparams, problem, objective, MAX_BOUND_VARS, allow_lateral);
    let root = ex.run(budget);
    if let Some(calls) = explore_calls {
        *calls = ex.explore_calls;
    }
    Ok(root.map(|r| emit_network_for_solution(problem.num_inputs(), &r)))
}

#[cfg(test)]
mod tests;
