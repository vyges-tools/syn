// SPDX-License-Identifier: Apache-2.0
//! Gate-level resynthesis around the gate outputs failing timing: from each one, enumerate the
//! cuts of the logic behind it (leaves expanded one at a time, gates below the cut taken in where
//! their fanout reconverges), read each cut's function and its timing budget off the timed
//! netlist, synthesize a replacement with [`super::acd::synthesize`], and keep per output the one
//! that gains the most slack. Committing replaces the gates of every substitution not overlapped
//! by an earlier one.
//!
//! Stages in the order the command runs them: [`Netlist::read`] (the database, as the timer
//! sees it) → [`Resynthesis::resynthesize`] (`resynthesize_pin` per head → `expand_cut` →
//! `expand_forward` → `collect_cone` → `evaluate_cut` → [`populate_cut_timing`]) →
//! [`commit`] (`apply_substitution` per substitution, then the gates it leaves
//! without a use removed).

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::time::Instant;

use vyges_opendb::Db;
use vyges_sta::graph::Graph;
use vyges_sta::liberty::{Cell as TimingCell, Direction, Port as TimingPort, MAX};
use vyges_sta::search::{Search, Tag};

use super::acd::{
    evaluate_function, find_delay_lower_bound, network_slack, port_cap, synthesize, Corner, DebugLog, DelayEstimationParameters,
    GateNetwork, GateNode, MatchCache, SynthesisProblem,
};
use crate::library::Libraries;

// ---------------------------------------------------------------------------------------------
// The netlist, as the timer sees it

/// A terminal: an instance pin, or a block port acting as one.
#[derive(Clone, Debug)]
pub struct Pin {
    /// What the timer orders pins by: an instance pin's database id doubled, a port's doubled
    /// plus one. Pins are held in this order, so a pin's index orders as its id does.
    pub id: u64,
    pub inst: Option<usize>,
    /// The master terminal, or the port.
    pub term: String,
    /// `inst/term`, or the port's name.
    pub name: String,
    pub net: Option<usize>,
    /// The database's io type: INPUT, OUTPUT, INOUT, FEEDTHRU.
    pub io: String,
    /// The signal type is SIGNAL (not a supply, nor a clock terminal).
    pub signal: bool,
    /// Supply (POWER / GROUND).
    pub supply: bool,
    /// The timing graph's vertex (the driver vertex for a driver).
    pub vertex: Option<usize>,
}

#[derive(Clone, Debug)]
pub struct Inst {
    pub name: String,
    pub master: String,
    /// In `getITerms` order.
    pub pins: Vec<usize>,
    pub dont_touch: bool,
    /// The master's type is CORE (a logic standard cell).
    pub core: bool,
}

#[derive(Clone, Debug)]
pub struct Net {
    pub name: String,
    /// Instance pins in `getITerms` order.
    pub iterms: Vec<usize>,
    pub bterms: Vec<usize>,
    pub dont_touch: bool,
    /// `Network::drivers`: the instance pins that are outputs (or bidirectional), the ports that
    /// are inputs (or bidirectional); supplies are neither.
    pub drivers: Vec<usize>,
}

pub struct Netlist {
    pub pins: Vec<Pin>,
    pub insts: Vec<Inst>,
    pub nets: Vec<Net>,
    /// Per timing-graph vertex, its pin.
    pub vertex_pin: Vec<Option<usize>>,
}

impl Netlist {
    /// The database's instances in `getInsts` order, each with its pins in `getITerms` order;
    /// every pin found its vertex in `graph`.
    pub fn read(db: &Db, graph: &Graph) -> Result<Netlist, String> {
        let e = |x: vyges_opendb::Error| x.to_string();
        let net_names = db.net_names();
        let net_index: HashMap<&str, usize> = net_names.iter().enumerate().map(|(k, n)| (n.as_str(), k)).collect();
        let net_of = |n: &str| if n.is_empty() { None } else { net_index.get(n).copied() };
        let mut pins = Vec::new();
        let mut insts = Vec::new();
        let mut sig_types: HashMap<String, HashMap<String, String>> = HashMap::new();
        let mut core: HashMap<String, bool> = HashMap::new();
        for name in db.inst_names() {
            let master = db.inst_master(&name);
            if !sig_types.contains_key(&master) {
                sig_types.insert(master.clone(), db.master_mterms(&master).map_err(e)?.into_iter().collect());
                core.insert(master.clone(), db.master_get_type(&master).map_err(e)? == "CORE");
            }
            let sig = &sig_types[&master];
            let k = insts.len();
            let mut inst_pins = Vec::new();
            for (term, io, net) in db.inst_iterm_info(&name).map_err(e)? {
                let id = u64::from(db.iterm_id(&name, &term).map_err(e)?) * 2;
                let st = sig.get(&term).map(String::as_str).unwrap_or("SIGNAL");
                inst_pins.push(pins.len());
                pins.push(Pin {
                    id,
                    inst: Some(k),
                    name: format!("{name}/{term}"),
                    term,
                    net: net_of(&net),
                    io,
                    signal: st == "SIGNAL",
                    supply: matches!(st, "POWER" | "GROUND"),
                    vertex: None,
                });
            }
            insts.push(Inst { dont_touch: db.inst_is_do_not_touch(&name), core: core[&master], name, master, pins: inst_pins });
        }
        for b in db.bterm_names() {
            let id = u64::from(db.bterm_id(&b).map_err(e)?) * 2 + 1;
            let st = db.bterm_get_sig_type(&b);
            pins.push(Pin {
                id,
                inst: None,
                term: b.clone(),
                name: b.clone(),
                net: net_of(&db.bterm_net(&b)),
                io: db.bterm_get_io_type(&b),
                signal: st == "SIGNAL",
                supply: matches!(st.as_str(), "POWER" | "GROUND"),
                vertex: None,
            });
        }
        // Hold the pins in id order, so a set of pin indices iterates as the timer's pin sets do.
        let mut order: Vec<usize> = (0..pins.len()).collect();
        order.sort_by_key(|&p| pins[p].id);
        let mut new_index = vec![0; pins.len()];
        for (to, &from) in order.iter().enumerate() {
            new_index[from] = to;
        }
        let mut sorted: Vec<Pin> = order.iter().map(|&p| pins[p].clone()).collect();
        for inst in &mut insts {
            for p in &mut inst.pins {
                *p = new_index[*p];
            }
        }
        let index = graph.index();
        let mut vertex_pin = vec![None; graph.vertices.len()];
        for (k, p) in sorted.iter_mut().enumerate() {
            p.vertex = index.get(&p.name).copied();
            if let Some(v) = p.vertex {
                vertex_pin[v] = Some(k);
            }
        }
        let by_name: HashMap<&str, usize> = sorted.iter().enumerate().map(|(k, p)| (p.name.as_str(), k)).collect();
        let mut nets = Vec::new();
        for n in &net_names {
            let mut iterms = Vec::new();
            for (i, t) in db.net_iterm_pairs(n).map_err(e)? {
                iterms.push(*by_name.get(format!("{i}/{t}").as_str()).ok_or_else(|| format!("{n}: no pin {i}/{t}"))?);
            }
            let bterms: Vec<usize> = db.net_bterms(n).iter().filter_map(|b| by_name.get(b.as_str()).copied()).collect();
            let is_driver = |p: &Pin| {
                !p.supply
                    && match p.inst {
                        Some(_) => matches!(p.io.as_str(), "OUTPUT" | "INOUT" | "FEEDTHRU"),
                        None => matches!(p.io.as_str(), "INPUT" | "INOUT" | "FEEDTHRU"),
                    }
            };
            let drivers = iterms.iter().chain(&bterms).copied().filter(|&p| is_driver(&sorted[p])).collect();
            nets.push(Net { name: n.clone(), iterms, bterms, dont_touch: db.net_is_do_not_touch(n), drivers });
        }
        Ok(Netlist { pins: sorted, insts, nets, vertex_pin })
    }

    fn is_signal_input(&self, p: usize) -> bool {
        self.pins[p].signal && self.pins[p].io == "INPUT"
    }

    fn is_signal_output(&self, p: usize) -> bool {
        self.pins[p].signal && self.pins[p].io == "OUTPUT"
    }

    /// `Network::connectedPinIterator(net)`: the net's pins as a pin set holds them — in pin id
    /// order (instance pins and ports interleaved), not the net's own order.
    pub fn connected_pins(&self, net: usize) -> Vec<usize> {
        let n = &self.nets[net];
        let mut pins: Vec<usize> = n.iterms.iter().chain(&n.bterms).copied().collect();
        pins.sort_unstable();
        pins
    }

    fn drivers(&self, net: usize) -> &[usize] {
        &self.nets[net].drivers
    }
}

// ---------------------------------------------------------------------------------------------
// Formatting as the reference's logger does

/// A time in the library's unit at `digits` decimals (`delayAsString`): the float quotient,
/// printed fixed.
fn delay_as_string(v: f32, digits: usize, time_scale: f32) -> String {
    format!("{:.*}", digits, f64::from(v / time_scale))
}

/// A double as the logger's `{:a}` prints it: `0x1.<hex>p±e`, trailing zero digits dropped — as
/// C's `%a`, except that zero takes the subnormal exponent (`0x0p-1022`, where C prints `0x0p+0`).
pub fn hexfloat(v: f64) -> String {
    let sign = if v.is_sign_negative() { "-" } else { "" };
    let a = v.abs();
    if a == 0.0 {
        return format!("{sign}0x0p-1022");
    }
    let bits = a.to_bits();
    let (lead, mut mant, exp) = match (bits >> 52) as i64 {
        0 => (0, bits & ((1 << 52) - 1), -1022),
        e => (1, bits & ((1 << 52) - 1), e - 1023),
    };
    let mut digits = 13;
    while digits > 0 && mant & 0xf == 0 {
        mant >>= 4;
        digits -= 1;
    }
    let frac = if digits == 0 { String::new() } else { format!(".{mant:0digits$x}") };
    format!("{sign}0x{lead}{frac}p{}{}", if exp < 0 { '-' } else { '+' }, exp.abs())
}

// ---------------------------------------------------------------------------------------------
// Cut timing

/// `std::min`: the first unless the second is less.
fn min_f(a: f32, b: f32) -> f32 {
    if b < a {
        b
    } else {
        a
    }
}

/// `std::max`: the first unless it is less than the second.
fn max_f(a: f32, b: f32) -> f32 {
    if a < b {
        b
    } else {
        a
    }
}

/// What the cut's problem needs from the timed netlist: per output its external load (the net's
/// load less the cone's own input pins on it), per input and transition the most each output can
/// take of it — walking every max path of the leaf's driver forward through the cone, through
/// each arc as the search would tag it, `arrival − required` at each output reached.
///
/// An output's required time is the search's, except when it also feeds the cone: then it is the
/// least over its arcs leaving the cone of the far pin's required less the arc's delay, so the
/// budget is the one the cut's own logic does not consume.
#[allow(clippy::too_many_arguments)]
pub fn populate_cut_timing(
    nl: &Netlist,
    graph: &Graph,
    search: &Search,
    corner: &Corner,
    problem: &mut SynthesisProblem,
    roots: &[Option<usize>],
    leaves: &[Option<usize>],
    cone: &HashSet<usize>,
) {
    let in_cone = |v: usize| nl.vertex_pin[v].and_then(|p| nl.pins[p].inst).is_some_and(|i| cone.contains(&i));
    let po_required = |po_v: usize, po_path: &vyges_sta::search::Path| -> f32 {
        let sta_req = po_path.required;
        let cur_rf = po_path.tag.rf;
        let mut ext = f32::INFINITY;
        let (mut has_internal, mut has_external) = (false, false);
        for &e in &graph.out_edges[po_v] {
            let w = graph.edges[e].to;
            if in_cone(w) {
                has_internal = true;
                continue;
            }
            for (arc, to_rf) in search.edge_arcs_from(e, cur_rf) {
                let Some(to_tag) = search.thru_tag(&po_path.tag, e, to_rf) else { continue };
                let Some(sp) = search.vertex_path(w, &to_tag) else { continue };
                ext = min_f(ext, sp.required - search.edge_arc_delay(e, arc, MAX));
                has_external = true;
            }
        }
        if has_internal && has_external {
            ext
        } else {
            sta_req
        }
    };

    let mut vertex_po_index: HashMap<usize, usize> = HashMap::new();
    let no_parasitics = HashMap::new();
    for (i, root) in roots.iter().enumerate() {
        let Some(net) = *root else { continue };
        let [pin] = nl.drivers(net) else { continue };
        let Some(v) = nl.pins[*pin].vertex else { continue };
        vertex_po_index.insert(v, i);
        let mut load = graph.load_cap(v, &no_parasitics);
        for p in nl.connected_pins(net) {
            let pin = &nl.pins[p];
            let Some(inst) = pin.inst else { continue };
            if !cone.contains(&inst) {
                continue;
            }
            let Some(port) = liberty_port(nl, corner, p) else { continue };
            if port.direction == Direction::Input {
                load -= port_cap(port);
            }
        }
        problem.output_mut(i).external_load = load;
    }

    for (li, leaf) in leaves.iter().enumerate() {
        let Some(net) = *leaf else { continue };
        let [pin] = nl.drivers(net) else { continue };
        let Some(leaf_v) = nl.pins[*pin].vertex else { continue };
        for p0 in &search.paths[leaf_v] {
            if p0.tag.mm != MAX {
                continue;
            }
            let leaf_rf = p0.tag.rf;
            let a0 = p0.arrival;
            let mut stack: Vec<(usize, Tag, usize)> = vec![(leaf_v, p0.tag, leaf_rf)];
            let mut visited: HashSet<(usize, Tag)> = HashSet::new();
            visited.insert((leaf_v, p0.tag));
            while let Some((v, tag, cur_rf)) = stack.pop() {
                for &e in &graph.out_edges[v] {
                    let w = graph.edges[e].to;
                    for (_, to_rf) in search.edge_arcs_from(e, cur_rf) {
                        let Some(to_tag) = search.thru_tag(&tag, e, to_rf) else { continue };
                        let Some(wp) = search.vertex_path(w, &to_tag) else { continue };
                        if let Some(&po) = vertex_po_index.get(&w) {
                            let m = a0 - po_required(w, wp);
                            let entry = problem.input_mut(li).arrivals.at_transition_mut(leaf_rf).at_exit_mut(po, to_rf);
                            *entry = max_f(*entry, m);
                        }
                        if in_cone(w) && visited.insert((w, to_tag)) {
                            stack.push((w, to_tag, to_rf));
                        }
                    }
                }
            }
        }
    }
}

/// The Liberty cell of an instance: the first library's of the master's name.
fn liberty_cell<'c>(nl: &Netlist, corner: &'c Corner, inst: usize) -> Option<&'c TimingCell> {
    corner.cell(&nl.insts[inst].master)
}

/// The Liberty port of an instance pin.
fn liberty_port<'c>(nl: &Netlist, corner: &'c Corner, pin: usize) -> Option<&'c TimingPort> {
    let p = &nl.pins[pin];
    liberty_cell(nl, corner, p.inst?)?.ports.iter().find(|q| q.name == p.term)
}

// ---------------------------------------------------------------------------------------------
// The command

/// `acd_resynth`'s options.
#[derive(Clone, Debug)]
pub struct Options {
    pub max_leaves: usize,
    pub max_intermediate_leaves: usize,
    pub max_cells: usize,
    pub max_outerfans: usize,
    pub exclude_buffers: bool,
    pub allow_lateral: bool,
    pub timing_opt_effort: f32,
    pub apply: bool,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            max_leaves: 6,
            max_intermediate_leaves: 8,
            max_cells: 20,
            max_outerfans: 3,
            exclude_buffers: false,
            allow_lateral: false,
            timing_opt_effort: 1e11,
            apply: false,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct Stats {
    pub heads: i64,
    pub expansions: i64,
    pub cuts: i64,
    pub syntheses: i64,
    pub forward_scans: i64,
    pub taken_in: i64,
    pub explores: i64,
    pub worst_explore: i64,
    pub t_sta: f64,
    pub t_enumerate: f64,
    pub t_forward: f64,
    pub t_cut_timing: f64,
    pub t_synthesize: f64,
    pub t_slack: f64,
    pub t_commit: f64,
}

/// A replacement for the gates of a cut: pins are the netlist's.
#[derive(Clone, Debug)]
pub struct Substitution {
    pub leaves: Vec<usize>,
    pub original: GateNetwork,
    pub replacement: GateNetwork,
    pub gain: f32,
}

/// The enumeration over a timed netlist; [`commit`] applies what it finds.
pub struct Resynthesis<'r> {
    nl: &'r Netlist,
    graph: &'r Graph<'r>,
    search: &'r Search<'r, 'r>,
    corner: &'r Corner,
    libs: &'r Libraries,
    mc: MatchCache<'r>,
    fixed_slew: [f32; 2],
    nand_delay: f32,
    epsilon: f32,
    wns: f32,
    time_scale: f32,
    o: Options,
    pub stats: Stats,
    pub substitutions: Vec<Substitution>,
    head: usize,
    pin_best: Option<Substitution>,
    /// `set_debug_level SYN acd_resynth` (and `acd`, for the search).
    pub debug: DebugLog,
    /// The call-sequence trace lines (`VYG …`), interleaved with the debug lines.
    pub trace: bool,
    pub lines: Vec<String>,
}

/// SYN-0061 and its kin: an error the reference raises (and stops on).
#[derive(Debug)]
pub struct Error(pub String);

type Cone = BTreeSet<usize>;
type Users = HashMap<usize, i32>;

impl<'r> Resynthesis<'r> {
    /// `Resynthesis::init`: the fixed slews, the match cache, the NAND2's delay and the slack
    /// difference below which a candidate is noise (an eighth of it).
    #[allow(clippy::too_many_arguments)]
    pub fn init(
        nl: &'r Netlist,
        graph: &'r Graph<'r>,
        search: &'r Search<'r, 'r>,
        corner: &'r Corner,
        libs: &'r Libraries,
        mc: MatchCache<'r>,
        fixed_slew: [f32; 2],
        time_scale: f32,
        debug: DebugLog,
        trace: bool,
    ) -> Result<Self, Error> {
        if fixed_slew[0] <= 0.0 || fixed_slew[1] <= 0.0 {
            return Err(Error("[ERROR SYN-0061] No buffer target slew available; delay estimation would be meaningless.".into()));
        }
        let nand_delay = find_delay_lower_bound(corner, &mc.nand2().name, fixed_slew);
        let epsilon = nand_delay / 8.0;
        let mut r = Resynthesis {
            nl,
            graph,
            search,
            corner,
            libs,
            mc,
            fixed_slew,
            nand_delay,
            epsilon,
            wns: 0.0,
            time_scale,
            o: Options::default(),
            stats: Stats::default(),
            substitutions: Vec::new(),
            head: 0,
            pin_best: None,
            debug,
            trace,
            lines: Vec::new(),
        };
        if r.trace {
            let l = format!(
                "VYG init slew {:08x} {:08x} nand {} {:08x} eps {:08x}",
                fixed_slew[0].to_bits(),
                fixed_slew[1].to_bits(),
                r.mc.nand2().name,
                nand_delay.to_bits(),
                epsilon.to_bits()
            );
            r.lines.push(l);
        }
        Ok(r)
    }

    fn debug_print(&mut self, level: u32, msg: String) {
        if self.debug.acd_resynth >= level {
            self.lines.push(format!("[DEBUG SYN-acd_resynth] {msg}"));
        }
    }

    fn vyg(&mut self, msg: String) {
        if self.trace {
            self.lines.push(msg);
        }
    }

    fn name(&self, p: usize) -> &str {
        &self.nl.pins[p].name
    }

    /// Everything on the pin's net but the pin, ports included.
    fn nusers(&self, pin: usize) -> i32 {
        let Some(net) = self.nl.pins[pin].net else { return 0 };
        let n = &self.nl.nets[net];
        (n.iterms.len() + n.bterms.len()) as i32 - 1
    }

    fn as_driver_iterm(&self, pin: usize) -> Option<usize> {
        self.nl.pins[pin].inst.map(|_| pin)
    }

    /// The one driver of an input's net (none without a net, or with other than one driver).
    fn driver_of(&self, input: usize) -> Option<usize> {
        let net = self.nl.pins[input].net?;
        match self.nl.drivers(net) {
            [d] => Some(*d),
            _ => None,
        }
    }

    fn sibling_output(&self, driver: usize) -> Option<usize> {
        let inst = self.nl.pins[driver].inst?;
        self.nl.insts[inst].pins.iter().copied().find(|&p| p != driver && self.nl.is_signal_output(p))
    }

    fn is_multi_output(&self, pin: usize) -> bool {
        self.as_driver_iterm(pin).is_some_and(|d| self.sibling_output(d).is_some())
    }

    /// `Resynthesis::resynthesize`: the design's worst slack, the heads (every signal output with
    /// negative slack, in instance then pin order, taken up front), a cut enumeration from each,
    /// the substitutions found. Committing them is [`commit`]'s (the caller's, with the
    /// database), then [`report_stats`].
    pub fn resynthesize(&mut self, o: Options) {
        self.stats = Stats::default();
        let t0 = Instant::now();
        self.wns = worst_slack(self.search, self.graph.vertices.len());
        self.stats.t_sta = t0.elapsed().as_secs_f64();
        self.vyg(format!("VYG wns {:08x}", self.wns.to_bits()));
        self.o = o;
        self.substitutions.clear();

        let mut heads = Vec::new();
        for inst in &self.nl.insts {
            for &pin in &inst.pins {
                if self.nl.is_signal_output(pin) {
                    let slack = self.nl.pins[pin].vertex.map_or(vyges_sta::search::INF_SLACK, |v| self.search.vertex_slack(v));
                    if self.trace {
                        self.lines.push(format!("VYG out {} {:08x}", self.nl.pins[pin].name, slack.to_bits()));
                    }
                    if slack < 0.0 {
                        heads.push(pin);
                    }
                }
            }
        }
        self.debug_print(1, format!("resynthesizing around {} gate outputs", heads.len()));
        self.stats.heads = heads.len() as i64;
        let t0 = Instant::now();
        for head in heads {
            self.resynthesize_pin(head);
        }
        self.stats.t_enumerate = t0.elapsed().as_secs_f64();

        let mut gain = 0.0f32;
        for s in &self.substitutions {
            gain += s.gain;
        }
        let msg = format!("{} substitutions to be had, {} of gain between them", self.substitutions.len(), delay_as_string(gain, 6, self.time_scale));
        self.debug_print(1, msg);
    }

    fn resynthesize_pin(&mut self, head: usize) {
        self.head = head;
        self.pin_best = None;
        self.vyg(format!("VYG head {}", self.nl.pins[head].name));

        let cone: Cone = [head].into();
        let n = self.nusers(head);
        self.expand_cut(0, vec![head], 0, 0, 1, cone, [(head, n)].into(), [(head, n)].into());

        if self.debug.acd_resynth >= 1 {
            if let Some(best) = self.pin_best.clone() {
                let msg = format!(
                    "pin best at {}: gain {}, area {:.2} -> {:.2}",
                    self.name(self.head),
                    delay_as_string(best.gain, 6, self.time_scale),
                    self.network_area(&best.original),
                    self.network_area(&best.replacement)
                );
                self.debug_print(1, msg);
                let msg = format!("  -{}", self.format_gate_network(&best.original, &best.leaves));
                self.debug_print(1, msg);
                let msg = format!("  +{}", self.format_gate_network(&best.replacement, &best.leaves));
                self.debug_print(1, msg);
            }
        }
        if let Some(best) = self.pin_best.take() {
            self.substitutions.push(best);
        }
    }

    /// `expandableDriver`: a CORE instance, not dont-touch, with a combinational Liberty cell (not
    /// a buffer when those are excluded); no pin on a dont-touch net, no signal inout, at most
    /// `max_intermediate_leaves` signal inputs and two outputs, the driver's port two-state with a
    /// function; every other signal input on a net with exactly one driver.
    fn expandable_driver(&self, driver: usize) -> bool {
        let nl = self.nl;
        let Some(inst) = nl.pins[driver].inst else { return false };
        let instance = &nl.insts[inst];
        if !instance.core || instance.dont_touch {
            return false;
        }
        let Some(cell) = liberty_cell(nl, self.corner, inst) else { return false };
        if cell.is_sequential() {
            return false;
        }
        if self.o.exclude_buffers && cell.is_buffer() {
            return false;
        }
        let (mut ninputs, mut noutputs) = (0, 0);
        for &pin in &instance.pins {
            let p = &nl.pins[pin];
            if p.net.is_some_and(|n| nl.nets[n].dont_touch) {
                return false;
            }
            if p.signal {
                match p.io.as_str() {
                    "INOUT" => return false,
                    "INPUT" => {
                        ninputs += 1;
                        if ninputs > self.o.max_intermediate_leaves {
                            return false;
                        }
                    }
                    "OUTPUT" => {
                        noutputs += 1;
                        if noutputs > 2 {
                            return false;
                        }
                        match liberty_port(nl, self.corner, driver) {
                            Some(port) if port.function.is_some() && port.three_state.is_none() => {}
                            _ => return false,
                        }
                    }
                    _ => {}
                }
            }
        }
        for &pin in &instance.pins {
            if pin == driver || !nl.is_signal_input(pin) {
                continue;
            }
            let Some(net) = nl.pins[pin].net else { return false };
            if nl.drivers(net).len() != 1 {
                return false;
            }
        }
        true
    }

    fn contained_in_mffc(&self, drivers_in_cone: &Cone, mffc_users: &Users, pin: usize) -> bool {
        if !drivers_in_cone.contains(&pin) {
            return false;
        }
        mffc_users.get(&pin).is_some_and(|&u| u == self.nusers(pin))
    }

    fn enters_mffc(&self, drivers_in_cone: &Cone, mffc_users: &Users, pin: usize) -> bool {
        if self.is_multi_output(pin) {
            // The gate's other output keeps it unless that one is spoken for as well.
            let sibling = self.sibling_output(pin).expect("a sibling");
            if !self.contained_in_mffc(drivers_in_cone, mffc_users, sibling) {
                return false;
            }
        }
        self.contained_in_mffc(drivers_in_cone, mffc_users, pin)
    }

    fn ref_mffc(&self, drivers_in_cone: &Cone, mffc_size: &mut usize, mffc_users: &mut Users, pin: usize) {
        let inst = self.nl.pins[pin].inst.expect("an instance pin");
        *mffc_size += 1;
        for &input in &self.nl.insts[inst].pins {
            if !self.nl.is_signal_input(input) {
                continue;
            }
            let a = self.driver_of(input).expect("one driver");
            *mffc_users.entry(a).or_insert(0) += 1;
            if self.enters_mffc(drivers_in_cone, mffc_users, a) {
                self.ref_mffc(drivers_in_cone, mffc_size, mffc_users, a);
            }
        }
    }

    /// `collectCone`: the cut's gates read back from the head, a driver settling once every user
    /// it has in the cut is walked (so `order` comes out reverse-topological), the outputs of the
    /// cut the head and every driver with users outside it; the network's nodes in topological
    /// order, each node's fanins in its cell's input order.
    fn collect_cone(&self, leaves: &[usize], drivers_in_cone: &Cone, cut_users: &Users) -> (Vec<usize>, Vec<usize>, GateNetwork) {
        let nl = self.nl;
        let mut order: Vec<usize> = Vec::new();
        let mut settled: HashSet<usize> = HashSet::new();
        let mut done_users: HashMap<usize, i32> = HashMap::new();
        let mut cone: Vec<usize> = Vec::new();
        let mut roots: Vec<usize> = vec![self.head];

        let settle = |d: usize, order: &mut Vec<usize>, settled: &mut HashSet<usize>, roots: &mut Vec<usize>, cone: &mut Vec<usize>| {
            order.push(d);
            settled.insert(d);
            if d != self.head && cut_users[&d] != self.nusers(d) {
                roots.push(d);
            }
            let sibling = self.sibling_output(d);
            if sibling.is_none_or(|s| !drivers_in_cone.contains(&s) || settled.contains(&s)) {
                cone.push(nl.pins[d].inst.expect("an instance pin"));
            }
        };

        settle(self.head, &mut order, &mut settled, &mut roots, &mut cone);
        for &d in drivers_in_cone {
            if d != self.head && cut_users[&d] == 0 {
                settle(d, &mut order, &mut settled, &mut roots, &mut cone);
            }
        }
        let mut i = 0;
        while i < cone.len() {
            let inst = cone[i];
            for &input in &nl.insts[inst].pins {
                if !nl.is_signal_input(input) {
                    continue;
                }
                let Some(a) = self.driver_of(input) else { continue };
                if !drivers_in_cone.contains(&a) {
                    continue;
                }
                let n = done_users.entry(a).or_insert(0);
                *n += 1;
                if *n == cut_users[&a] {
                    settle(a, &mut order, &mut settled, &mut roots, &mut cone);
                }
            }
            i += 1;
        }

        let nnodes = order.len();
        let node_index: HashMap<usize, usize> = (0..nnodes).map(|i| (order[nnodes - 1 - i], i)).collect();
        let leaf_index: HashMap<usize, usize> = leaves.iter().enumerate().map(|(i, &l)| (l, i)).collect();
        let mut net = GateNetwork { ninputs: leaves.len(), nodes: Vec::with_capacity(nnodes), outs: Vec::new() };
        for i in 0..nnodes {
            let driver_pin = order[nnodes - 1 - i];
            let inst = nl.pins[driver_pin].inst.expect("an instance pin");
            let driver_port = self.driver_port(driver_pin);
            let mut fanins = Vec::new();
            for port in driver_port.input_ports() {
                let input = nl.insts[inst].pins.iter().copied().find(|&p| nl.pins[p].term == port.name).expect("the port's pin");
                let a = self.driver_of(input).expect("one driver");
                fanins.push(match node_index.get(&a) {
                    Some(&k) => (false, k),
                    None => (true, leaf_index[&a]),
                });
            }
            net.nodes.push(GateNode { driver_port, driver_pin: Some(driver_pin), fanins });
        }
        net.outs = roots.iter().map(|r| (false, node_index[r])).collect();
        (cone, roots, net)
    }

    /// The synthesis cell port an instance output pin is.
    fn driver_port(&self, pin: usize) -> super::acd::Driver {
        let p = &self.nl.pins[pin];
        let master = &self.nl.insts[p.inst.expect("an instance pin")].master;
        let cell = self.libs.find_cell(master).expect("a library cell");
        let port = cell.ports.iter().position(|q| q.name == p.term).expect("the cell's port");
        super::acd::Driver { cell, port }
    }

    /// `expandForward`: take gates in from below while that brings the output count down.
    fn expand_forward(&mut self, leaves: &mut Vec<usize>, drivers_in_cone: &mut Cone, cut_users: &mut Users, ngates: &mut usize, nouterfans: &mut i32) {
        while self.take_in_one_gate(leaves, drivers_in_cone, cut_users, ngates, nouterfans) {}
    }

    /// One scan: the cone's drivers in pin id order (the cone is a pin set; pin indices are held
    /// in id order), each one's users in the net's order, the first gate that goes in ends it. When
    /// two gates could go in from one cut the earlier driver's goes first: witnessed by a 5-gate
    /// netlist with two such gates, as the order of the `took in` lines and the Verilog.
    fn take_in_one_gate(&mut self, leaves: &mut Vec<usize>, drivers_in_cone: &mut Cone, cut_users: &mut Users, ngates: &mut usize, nouterfans: &mut i32) -> bool {
        self.stats.forward_scans += 1;
        let drivers: Vec<usize> = drivers_in_cone.iter().copied().collect();
        for d in drivers {
            if d == self.head || cut_users[&d] == self.nusers(d) {
                continue;
            }
            let Some(net) = self.nl.pins[d].net else { continue };
            for &user in &self.nl.nets[net].iterms {
                if self.nl.is_signal_input(user) {
                    let g = self.nl.pins[user].inst.expect("an instance pin");
                    if self.take_in_gate(g, leaves, drivers_in_cone, cut_users, ngates, nouterfans) {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// `takeInGate`: a one-output expandable gate not already in, none of its inputs the head; in
    /// when it lowers the output count without going over the cell or leaf limits.
    fn take_in_gate(
        &mut self,
        g: usize,
        leaves: &mut Vec<usize>,
        drivers_in_cone: &mut Cone,
        cut_users: &mut Users,
        ngates: &mut usize,
        nouterfans: &mut i32,
    ) -> bool {
        let nl = self.nl;
        let Some(out) = nl.insts[g].pins.iter().copied().find(|&p| nl.is_signal_output(p)) else { return false };
        if self.sibling_output(out).is_some() || !self.expandable_driver(out) || drivers_in_cone.contains(&out) {
            return false;
        }
        let mut reads: BTreeMap<usize, i32> = BTreeMap::new();
        for &input in &nl.insts[g].pins {
            if !nl.is_signal_input(input) {
                continue;
            }
            let Some(a) = self.driver_of(input) else { return false };
            if a == self.head {
                return false;
            }
            *reads.entry(a).or_insert(0) += 1;
        }
        let (mut completed, mut fresh_leaves) = (0i32, 0usize);
        for (&a, &count) in &reads {
            if !drivers_in_cone.contains(&a) {
                if *cut_users.entry(a).or_insert(0) == 0 {
                    fresh_leaves += 1;
                }
            } else if cut_users[&a] != self.nusers(a) && cut_users[&a] + count == self.nusers(a) {
                completed += 1;
            }
        }
        let out_users = cut_users.get(&out).copied().unwrap_or(0);
        let out_was_leaf = out_users > 0;
        let out_is_root = out_users != self.nusers(out);
        let delta = i32::from(out_is_root) - completed;
        let after_leaves = leaves.len() + fresh_leaves - usize::from(out_was_leaf);
        if delta > -1 || *ngates + 1 > self.o.max_cells || after_leaves > self.o.max_leaves {
            return false;
        }
        drivers_in_cone.insert(out);
        if out_was_leaf {
            let k = leaves.iter().position(|&l| l == out).expect("a leaf");
            leaves.remove(k);
        }
        cut_users.entry(out).or_insert(0);
        *ngates += 1;
        for (&a, &count) in &reads {
            let users = cut_users.entry(a).or_insert(0);
            if *users == 0 && !drivers_in_cone.contains(&a) {
                leaves.push(a);
            }
            *users += count;
        }
        *nouterfans += delta;
        self.stats.taken_in += 1;
        let msg = format!("took in {} from below: {} outputs accounted for, {} left", self.name(out), completed, nouterfans);
        self.debug_print(2, msg);
        true
    }

    /// `expandCut`: expand leaf `wedge` (its gate joins the cut), evaluate the cut when it is
    /// small enough, then go on expanding from each leaf at or after `wedge`.
    #[allow(clippy::too_many_arguments)]
    fn expand_cut(
        &mut self,
        wedge: usize,
        mut leaves: Vec<usize>,
        mut ngates: usize,
        mut mffc_size: usize,
        mut nouterfans: i32,
        mut drivers_in_cone: Cone,
        mut cut_users: Users,
        mut mffc_users: Users,
    ) {
        self.stats.expansions += 1;
        let y = leaves[wedge];
        if self.trace {
            let mut t = String::new();
            for &l in &leaves {
                t += &format!(" {}:{}", self.name(l), cut_users.get(&l).copied().unwrap_or(-1));
            }
            let mut c = String::new();
            for &d in &drivers_in_cone {
                c += &format!(" {}", self.name(d));
            }
            let l = format!("VYG expand w{} y={} g{} m{} o{} leaves{} | cone{}", wedge, self.name(y), ngates, mffc_size, nouterfans, t, c);
            self.lines.push(l);
        }

        let Some(driver) = self.as_driver_iterm(y) else { return };
        if !self.expandable_driver(driver) {
            return;
        }
        let sibling = self.sibling_output(driver);
        let gate_in_cone = sibling.is_some_and(|s| drivers_in_cone.contains(&s));

        leaves.remove(wedge);
        drivers_in_cone.insert(y);

        let mut in_mffc = false;
        if cut_users[&y] != self.nusers(y) {
            nouterfans += 1;
        } else if self.enters_mffc(&drivers_in_cone, &mffc_users, y) {
            in_mffc = true;
        }

        if !gate_in_cone {
            ngates += 1;
            let inst = self.nl.pins[driver].inst.expect("an instance pin");
            for &input in &self.nl.insts[inst].pins {
                if !self.nl.is_signal_input(input) {
                    continue;
                }
                let a = self.driver_of(input).expect("one driver");
                let u = cut_users.entry(a).or_insert(0);
                if *u == 0 {
                    leaves.push(a);
                }
                *u += 1;
                if drivers_in_cone.contains(&a) && cut_users[&a] == self.nusers(a) {
                    nouterfans -= 1;
                }
            }
        }

        if in_mffc {
            self.ref_mffc(&drivers_in_cone, &mut mffc_size, &mut mffc_users, y);
        }

        if ngates > self.o.max_cells || nouterfans > self.o.max_outerfans as i32 || leaves.len() > self.o.max_intermediate_leaves {
            return;
        }

        if leaves.len() <= self.o.max_leaves {
            let mut f_leaves = leaves.clone();
            let mut f_drivers = drivers_in_cone.clone();
            let mut f_cut_users = cut_users.clone();
            let mut f_ngates = ngates;
            let mut f_nouterfans = nouterfans;
            let t0 = Instant::now();
            self.expand_forward(&mut f_leaves, &mut f_drivers, &mut f_cut_users, &mut f_ngates, &mut f_nouterfans);
            self.stats.t_forward += t0.elapsed().as_secs_f64();

            // The timing objective only carries two outputs.
            if f_nouterfans <= 2 {
                let (cone, roots, net) = self.collect_cone(&f_leaves, &f_drivers, &f_cut_users);
                debug_assert_eq!(cone.len(), f_ngates);
                debug_assert_eq!(roots.len() as i32, f_nouterfans);
                if let Err(Error(e)) = self.evaluate_cut(&roots, &f_leaves, &cone, &net, mffc_size) {
                    self.lines.push(e);
                }
            }
        }

        // Leaves before `wedge` were passed over by an ancestor call.
        let mut w = wedge;
        while w < leaves.len() {
            self.expand_cut(w, leaves.clone(), ngates, mffc_size, nouterfans, drivers_in_cone.clone(), cut_users.clone(), mffc_users.clone());
            w += 1;
        }
    }

    /// The cells' area, a two-output gate read off the netlist counted once.
    fn network_area(&self, net: &GateNetwork) -> f32 {
        let mut area = 0.0f32;
        let mut counted: HashSet<usize> = HashSet::new();
        for node in &net.nodes {
            if let Some(p) = node.driver_pin {
                if !counted.insert(self.nl.pins[p].inst.expect("an instance pin")) {
                    continue;
                }
            }
            area += node.driver_port.cell.area;
        }
        area
    }

    fn format_gate_network(&self, net: &GateNetwork, leaves: &[usize]) -> String {
        let r = |(pi, k): (bool, usize)| format!("{}{k}", if pi { "i" } else { "n" });
        let mut text = String::from("leaves:");
        for (i, &l) in leaves.iter().enumerate().take(net.ninputs) {
            text += &format!(" i{i}={}", self.name(l));
        }
        text += " | nodes:";
        for (ni, node) in net.nodes.iter().enumerate() {
            let fanins: Vec<String> = node.fanins.iter().map(|&f| r(f)).collect();
            text += &format!(" n{ni}={}/{}({})", node.driver_port.cell.name, node.driver_port.cell.ports[node.driver_port.port].name, fanins.join(","));
        }
        text += " | outs:";
        for &(is_pi, idx) in &net.outs {
            text += &format!(" {}", r((is_pi, idx)));
            if !is_pi {
                if let Some(p) = net.nodes[idx].driver_pin {
                    text += &format!("={}", self.name(p));
                }
            }
        }
        text
    }

    /// `evaluateCut`: the cut's function and timing as a problem, its outputs failing timing
    /// marked critical (criticality 1 on the design's worst path, tapering to 0 at zero slack),
    /// the logic in place's slack the bar, a candidate synthesized and kept as the head's best when
    /// it clears the bar by more than the noise and gains more than the best so far.
    fn evaluate_cut(&mut self, roots: &[usize], leaves: &[usize], cone: &[usize], orig_net: &GateNetwork, mffc_size: usize) -> Result<(), Error> {
        self.stats.cuts += 1;
        let mut problem = SynthesisProblem::new(evaluate_function(orig_net));
        {
            let cone_set: HashSet<usize> = cone.iter().copied().collect();
            let root_nets: Vec<Option<usize>> = roots.iter().map(|&r| self.nl.pins[r].net).collect();
            let leaf_nets: Vec<Option<usize>> = leaves.iter().map(|&l| self.nl.pins[l].net).collect();
            let t0 = Instant::now();
            populate_cut_timing(self.nl, self.graph, self.search, self.corner, &mut problem, &root_nets, &leaf_nets, &cone_set);
            self.stats.t_cut_timing += t0.elapsed().as_secs_f64();
        }

        for (i, &root) in roots.iter().enumerate() {
            let Some(v) = self.nl.pins[root].vertex else { continue };
            let root_slack = self.search.vertex_slack(v);
            if root_slack >= 0.0 {
                continue;
            }
            let po = problem.output_mut(i);
            po.critical = true;
            po.criticality = if self.wns < 0.0 {
                let x = f64::from(root_slack) / f64::from(self.wns);
                if x < 1.0 {
                    x
                } else {
                    1.0
                }
            } else {
                1.0
            };
        }

        if self.trace {
            let f = problem.function();
            let mut t = String::new();
            for o in 0..f.num_outputs() {
                let mut v = 0u64;
                for m in 0..f.num_minterms() {
                    if f.value(o, m) {
                        v |= 1 << m;
                    }
                }
                let po = problem.output(o);
                t += &format!(" o{o}={v:x} load {:08x} crit {} {}", po.external_load.to_bits(), u8::from(po.critical), hexfloat(po.criticality));
            }
            self.lines.push(format!("VYG problem n{}{}", f.num_variables(), t));
            for i in 0..problem.num_inputs() {
                let mut a = String::new();
                for in_rf in [0, 1] {
                    for o in 0..problem.num_outputs() {
                        for out_rf in [0, 1] {
                            a += &format!(" {:08x}", problem.input(i).arrivals.at_transition(in_rf).at_exit(o, out_rf).to_bits());
                        }
                    }
                }
                self.lines.push(format!("VYG arr {i}{a}"));
            }
        }

        let t0 = Instant::now();
        let slack = network_slack(&problem, orig_net, self.corner, self.fixed_slew);
        self.stats.t_slack += t0.elapsed().as_secs_f64();
        self.vyg(format!("VYG slack {:08x}", slack.to_bits()));

        let mut explore_calls = 0i64;
        let t0 = Instant::now();
        self.stats.syntheses += 1;
        let dparams = DelayEstimationParameters { nand_delay: self.nand_delay, fixed_slews: self.fixed_slew, corner: self.corner };
        let solved = synthesize(&problem, &mut self.mc, &dparams, &mut self.debug, f64::INFINITY, self.o.allow_lateral, Some(&mut explore_calls), self.o.timing_opt_effort)
            .map_err(|e| Error(format!("[ERROR SYN-{:04}] {}", e.code, e.message)))?;
        // The search's own debug lines go out in order with ours.
        self.lines.append(&mut self.debug.lines);
        self.stats.explores += explore_calls;
        self.stats.worst_explore = self.stats.worst_explore.max(explore_calls);
        self.stats.t_synthesize += t0.elapsed().as_secs_f64();

        if self.debug.acd_resynth >= 2 {
            let msg = format!(
                "cut at {}: {} gates ({} in mffc), area {:.2}, slack {} | {}",
                self.name(self.head),
                cone.len(),
                mffc_size,
                self.network_area(orig_net),
                delay_as_string(slack, 3, self.time_scale),
                self.format_gate_network(orig_net, leaves)
            );
            self.debug_print(2, msg);
            match &solved {
                Some(cand) => {
                    let msg = format!(
                        "  candidate: {} gates, area {:.2}, slack {} ({} explored) | {}",
                        cand.nodes.len(),
                        self.network_area(cand),
                        delay_as_string(network_slack(&problem, cand, self.corner, self.fixed_slew), 3, self.time_scale),
                        explore_calls,
                        self.format_gate_network(cand, leaves)
                    );
                    self.debug_print(2, msg);
                }
                None => self.debug_print(2, "  candidate: none".into()),
            }
        }

        let Some(cand) = solved else { return Ok(()) };
        if evaluate_function(&cand) != *problem.function() {
            return Err(Error(format!(
                "[ERROR SYN-0062] Resynthesized network for the cut at {} is not equivalent to the logic it would replace.",
                self.name(self.head)
            )));
        }
        let cand_slack = network_slack(&problem, &cand, self.corner, self.fixed_slew);
        self.vyg(format!("VYG cand {} slack {:08x} explores {}", cand.nodes.len(), cand_slack.to_bits(), explore_calls));
        if cand_slack <= slack + self.epsilon {
            return Ok(());
        }
        let gain = cand_slack - slack;
        let best = self.pin_best.as_ref().is_none_or(|b| gain > b.gain);
        self.vyg(format!("VYG gain {:08x} best {}", gain.to_bits(), u8::from(best)));
        if best {
            self.pin_best = Some(Substitution { leaves: leaves.to_vec(), original: orig_net.clone(), replacement: cand, gain });
        }
        Ok(())
    }
}

/// The command's closing debug lines: its counts and where the time went.
pub fn report_stats(s: &Stats, debug: u32, lines: &mut Vec<String>) {
    if debug >= 1 {
        lines.push(format!(
            "[DEBUG SYN-acd_resynth] counts: {} heads, {} expansions, {} cuts, {} syntheses, {} forward scans, {} taken in; {} explores ({} worst)",
            s.heads, s.expansions, s.cuts, s.syntheses, s.forward_scans, s.taken_in, s.explores, s.worst_explore
        ));
        lines.push(format!(
            "[DEBUG SYN-acd_resynth] seconds: sta {:.2}, enumerate {:.2} (forward {:.2}, cut timing {:.2}, synthesize {:.2}, slack {:.2}), commit {:.2}",
            s.t_sta, s.t_enumerate, s.t_forward, s.t_cut_timing, s.t_synthesize, s.t_slack, s.t_commit
        ));
    }
}

/// `applySubstitution`: one new instance per replacement node, on the net of the original
/// output it stands for or a fresh one, its fanins connected in its cell's input order; the
/// original gates marked obsolete (left connected: their nets have two drivers until the
/// cleanup). A replacement output that is a bare leaf drops the substitution.
fn apply_substitution(nl: &Netlist, db: &mut Db, s: &Substitution, obsoleted: &mut Cone, made: &mut i64) -> Result<bool, String> {
    let net_name = |p: Option<usize>| -> String { nl.pins[p.expect("a netlist pin")].net.map(|n| nl.nets[n].name.clone()).unwrap_or_default() };
    let leaf_nets: Vec<String> = s.leaves.iter().map(|&l| net_name(Some(l))).collect();
    let mut taken_over: HashMap<usize, String> = HashMap::new();
    for i in 0..s.replacement.outs.len() {
        let (is_pi, node) = s.replacement.outs[i];
        if is_pi {
            return Ok(false);
        }
        let (_, orig_node) = s.original.outs[i];
        taken_over.insert(node, net_name(s.original.nodes[orig_node].driver_pin));
    }
    let e = |x: vyges_opendb::Error| x.to_string();
    let mut node_net: Vec<String> = Vec::with_capacity(s.replacement.nodes.len());
    for (ni, node) in s.replacement.nodes.iter().enumerate() {
        let cell = &node.driver_port.cell;
        let inst = format!("remap{made}");
        *made += 1;
        db.create_inst(&cell.name, &inst).map_err(e)?;
        let net = match taken_over.get(&ni) {
            Some(n) => n.clone(),
            None => {
                let n = format!("remap_net{made}");
                *made += 1;
                db.create_net(&n).map_err(e)?;
                n
            }
        };
        node_net.push(net);
        db.connect(&inst, &cell.ports[node.driver_port.port].name, &node_net[ni]).map_err(e)?;
        for (fi, port) in node.driver_port.input_ports().enumerate() {
            let (is_pi, idx) = node.fanins[fi];
            let net = if is_pi { &leaf_nets[idx] } else { &node_net[idx] };
            db.connect(&inst, &port.name, net).map_err(e)?;
        }
    }
    for node in &s.original.nodes {
        obsoleted.insert(node.driver_pin.expect("a netlist pin"));
    }
    Ok(true)
}

/// `Resynthesis::commit`: every substitution in the order found, passed over when a gate it
/// replaces was already replaced; then each obsoleted output's gate removed when all its outputs
/// are obsolete, else that output disconnected. SYN-0064. The instance and net names a commit
/// makes are `remap<N>` and `remap_net<N>` on one counter, `made`, which runs on from one run of
/// the command to the next.
pub fn commit(nl: &Netlist, db: &mut Db, subs: &[Substitution], made: &mut i64, trace: bool, stats: &mut Stats, lines: &mut Vec<String>) -> Result<(), String> {
    let t0 = Instant::now();
    let mut obsoleted: Cone = BTreeSet::new();
    let mut applied = 0;
    for s in subs {
        let stale = s.original.nodes.iter().any(|n| obsoleted.contains(&n.driver_pin.expect("a netlist pin")));
        if trace {
            let out = s.original.nodes[s.original.outs[0].1].driver_pin.expect("a netlist pin");
            lines.push(format!("VYG subst {} {}", nl.pins[out].name, if stale { "stale" } else { "fresh" }));
        }
        if stale {
            continue;
        }
        if apply_substitution(nl, db, s, &mut obsoleted, made)? {
            applied += 1;
        } else if trace {
            lines.push("VYG subst dropped (passthrough)".into());
        }
    }
    // Only once every substitution has been read is it safe to unhook anything: a later one can
    // name a leaf an earlier one made obsolete.
    let e = |x: vyges_opendb::Error| x.to_string();
    let mut doomed: Vec<usize> = Vec::new();
    let mut seen: HashSet<usize> = HashSet::new();
    for &p in &obsoleted {
        let inst = nl.pins[p].inst.expect("an instance pin");
        let all_spoken_for = nl.insts[inst].pins.iter().all(|&q| !nl.is_signal_output(q) || obsoleted.contains(&q));
        if all_spoken_for {
            if seen.insert(inst) {
                doomed.push(inst);
            }
        } else {
            db.disconnect(&nl.insts[inst].name, &nl.pins[p].term).map_err(e)?;
        }
    }
    for &inst in &doomed {
        if trace {
            lines.push(format!("VYG doomed {}", nl.insts[inst].name));
        }
        db.destroy_inst(&nl.insts[inst].name).map_err(e)?;
    }
    lines.push(format!("[INFO SYN-0064] acd_resynth: applied {} of {} substitutions, {} gates out", applied, subs.len(), doomed.len()));
    stats.t_commit = t0.elapsed().as_secs_f64();
    Ok(())
}

/// `Sta::worstSlack(max)`: over the end points in vertex order, the fuzzily least slack each counts
/// toward the worst (none: the initial value).
pub fn worst_slack(search: &Search, nvertices: usize) -> f32 {
    let mut worst = vyges_sta::search::INF_SLACK;
    for v in 0..nvertices {
        if !search.is_endpoint(v) {
            continue;
        }
        let s = search.wns_slack(v, true);
        if !vyges_sta::fuzzy::equal(s, vyges_sta::search::INF_SLACK) && vyges_sta::fuzzy::less(s, worst) {
            worst = s;
        }
    }
    worst
}

#[cfg(test)]
#[path = "acd_resynth/tests.rs"]
mod tests;
