// SPDX-License-Identifier: Apache-2.0
//! Sequential mapping: each flip-flop bit becomes a library flip-flop with the same clock edge and
//! asynchronous clear or set, complementing a polarity where the library offers only the other.

use std::collections::HashMap;
use std::sync::Arc;

use crate::elab::backend::ElabError;
use crate::ir::instance::{LibCell, LibDirection};
use crate::ir::net::{Net, Trit};
use crate::ir::{Graph, Kind};
use crate::library::{pin_expr, Libraries};

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
struct FeatureSet {
    clock_polarity: bool,
    has_clear: bool,
    clear_polarity: bool,
    has_set: bool,
    set_polarity: bool,
}

impl Default for FeatureSet {
    fn default() -> Self {
        FeatureSet { clock_polarity: true, has_clear: false, clear_polarity: true, has_set: false, set_polarity: true }
    }
}

impl FeatureSet {
    fn without_clear(self) -> Self {
        FeatureSet { has_clear: false, clear_polarity: true, ..self }
    }
    fn without_set(self) -> Self {
        FeatureSet { has_set: false, set_polarity: true, ..self }
    }
    fn complement_clear(self) -> Self {
        FeatureSet { clear_polarity: !self.clear_polarity, ..self }
    }
    fn complement_set(self) -> Self {
        FeatureSet { set_polarity: !self.set_polarity, ..self }
    }
    fn complement_clock(self) -> Self {
        FeatureSet { clock_polarity: !self.clock_polarity, ..self }
    }
}

/// Where each role sits: an input pin's offset in the cell's inputs, an output's in its outputs.
#[derive(Clone, Copy, Debug)]
struct PinPositions {
    clock_in: i32,
    data_in: i32,
    clear_in: i32,
    set_in: i32,
    data_out: i32,
    data_negated_out: i32,
}

#[derive(Clone, Debug)]
struct MapTarget {
    cell: Arc<LibCell>,
    features: FeatureSet,
    pins: PinPositions,
    data_negated: bool,
    area: f32,
    pin_count: i32,
}

impl MapTarget {
    /// Smaller area, then fewer input pins, then the name.
    fn better_than(&self, other: &MapTarget) -> bool {
        if self.area != other.area {
            return self.area < other.area;
        }
        if self.pin_count != other.pin_count {
            return self.pin_count < other.pin_count;
        }
        self.cell.name < other.cell.name
    }
}

/// The input offset of the input port `name`: inputs in the cell's order, a bus as wide as its bits.
fn input_port_position(cell: &LibCell, name: &str) -> i32 {
    let mut pos = 0;
    for p in &cell.ports {
        if p.direction == LibDirection::Input {
            if p.name == name {
                return pos;
            }
            pos += if p.is_bus { p.size as i32 } else { 1 };
        }
    }
    -1
}

/// The cell as a flip-flop target: one `ff` group whose clock, data, clear and preset are each a
/// pin or its complement, an output that is the state or its complement, and no input it does not
/// describe. Only a complemented output: it is used, the data complemented, clear and set swapped.
fn detect_cell(cell: &Arc<LibCell>) -> Option<MapTarget> {
    let seq = cell.seq.as_ref()?;
    if seq.latch {
        return None;
    }
    let mut feats = FeatureSet::default();
    let mut pins = PinPositions { clock_in: -1, data_in: -1, clear_in: -1, set_in: -1, data_out: -1, data_negated_out: -1 };

    let (clk_pol, clk_port) = pin_expr(seq.clocked_on.as_deref()?)?;
    feats.clock_polarity = clk_pol;
    pins.clock_in = input_port_position(cell, &clk_port);
    if pins.clock_in < 0 {
        return None;
    }
    let (data_pol, data_port) = pin_expr(seq.next_state.as_deref()?)?;
    pins.data_in = input_port_position(cell, &data_port);
    if pins.data_in < 0 {
        return None;
    }
    if let Some(clear) = &seq.clear {
        let (pol, port) = pin_expr(clear)?;
        feats.has_clear = true;
        feats.clear_polarity = pol;
        pins.clear_in = input_port_position(cell, &port);
        if pins.clear_in < 0 {
            return None;
        }
    }
    if let Some(preset) = &seq.preset {
        let (pol, port) = pin_expr(preset)?;
        feats.has_set = true;
        feats.set_polarity = pol;
        pins.set_in = input_port_position(cell, &port);
        if pins.set_in < 0 {
            return None;
        }
    }

    let mut pos = 0;
    for p in cell.ports.iter().filter(|p| !p.pwr_gnd && p.direction == LibDirection::Output) {
        match p.function.as_deref().and_then(pin_expr) {
            Some((true, n)) if n == seq.iq => pins.data_out = pos,
            Some((false, n)) if n == seq.iq => pins.data_negated_out = pos,
            _ => {}
        }
        pos += if p.is_bus { p.size as i32 } else { 1 };
    }

    let mut data_negated = !data_pol;
    if pins.data_out < 0 {
        if pins.data_negated_out < 0 {
            return None;
        }
        pins.data_out = pins.data_negated_out;
        pins.data_negated_out = -1;
        data_negated = !data_negated;
        std::mem::swap(&mut feats.has_clear, &mut feats.has_set);
        std::mem::swap(&mut feats.clear_polarity, &mut feats.set_polarity);
        std::mem::swap(&mut pins.clear_in, &mut pins.set_in);
    }

    let described = [pins.clock_in, pins.data_in, pins.clear_in, pins.set_in].iter().filter(|&&p| p >= 0).count() as i32;
    let total_inputs = cell.ports.iter().filter(|p| !p.pwr_gnd && p.direction == LibDirection::Input).count() as i32;
    if described != total_inputs {
        return None;
    }
    Some(MapTarget { cell: cell.clone(), features: feats, pins, data_negated, area: cell.area, pin_count: total_inputs })
}

/// The best target per feature set (library cells not withheld by `dont_use`), then each target
/// offered to the sets without its clear and without its set, until nothing changes.
fn build_index(libs: &Libraries) -> HashMap<FeatureSet, MapTarget> {
    let mut classes: HashMap<FeatureSet, MapTarget> = HashMap::new();
    for cell in libs.cells() {
        if cell.dont_use {
            continue;
        }
        let Some(mt) = detect_cell(cell) else { continue };
        if let Some(have) = classes.get(&mt.features) {
            if !mt.better_than(have) {
                continue;
            }
        }
        classes.insert(mt.features, mt);
    }
    // ⚠️ The reference walks a hash map here; the result does not depend on the order, as
    // `better_than` is a strict order and the walk repeats to a fixed point.
    let mut changed = true;
    while changed {
        changed = false;
        let snapshot = classes.clone();
        for (feats, target) in &snapshot {
            for df in [feats.without_clear(), feats.without_set()] {
                let replace = match classes.get(&df) {
                    None => true,
                    Some(have) => target.better_than(have),
                };
                if replace {
                    classes.insert(df, target.clone());
                    changed = true;
                }
            }
        }
    }
    classes
}

/// The target's inputs, every one X but the clear and set, held inactive.
fn build_default_inputs(mt: &MapTarget) -> Vec<Net> {
    let width: u32 = mt.cell.ports.iter().filter(|p| p.direction == LibDirection::Input).map(|p| if p.is_bus { p.size } else { 1 }).sum();
    let mut inputs = vec![Net::UNDEF; width as usize];
    if mt.features.has_clear {
        inputs[mt.pins.clear_in as usize] = if mt.features.clear_polarity { Net::ZERO } else { Net::ONE };
    }
    if mt.features.has_set {
        inputs[mt.pins.set_in as usize] = if mt.features.set_polarity { Net::ZERO } else { Net::ONE };
    }
    inputs
}

fn pol(has: bool, polarity: bool) -> &'static str {
    match (has, polarity) {
        (false, _) => "none",
        (true, true) => "pos",
        (true, false) => "neg",
    }
}

/// Normalizes, then maps every flip-flop, bit by bit, in slot order: its clock and asynchronous
/// clear (a 0 clear value) or set (a 1) looked up as they are, then the clear or set complemented,
/// then the clock, then both. The flip-flops are removed once all are mapped. SYN-0013 when no
/// library flip-flop fits a bit.
pub fn map_sequentials(g: &mut Graph, libs: &Libraries) -> Result<(), ElabError> {
    g.normalize();
    let classes = build_index(libs);
    let mut to_remove = Vec::new();
    let mut it = g.instances();
    while let Some(id) = it.next(g) {
        let Kind::Dff(dff) = &g.inst(id).kind else { continue };
        let dff = dff.clone();
        for i in 0..dff.data.len() {
            let mut feats = FeatureSet { clock_polarity: dff.clock.positive, ..FeatureSet::default() };
            let mut arst_is_set = false;
            if !dff.clear.is_always(false) {
                match dff.clear_value[i] {
                    Trit::Zero => {
                        feats.has_clear = true;
                        feats.clear_polarity = dff.clear.positive;
                    }
                    Trit::One => {
                        arst_is_set = true;
                        feats.has_set = true;
                        feats.set_polarity = dff.clear.positive;
                    }
                    Trit::Undef => {}
                }
            }
            let reset_complemented = if arst_is_set { feats.complement_set() } else { feats.complement_clear() };
            let found = [feats, reset_complemented, feats.complement_clock(), reset_complemented.complement_clock()]
                .into_iter()
                .find_map(|f| classes.get(&f).map(|t| (f, t)));
            let Some((key, mt)) = found else {
                return Err(ElabError {
                    code: 13,
                    message: format!(
                        "mapSequentials: no matching flip-flop cell for Dff bit {i} (clk={} clear={} set={})",
                        if feats.clock_polarity { "pos" } else { "neg" },
                        pol(feats.has_clear, feats.clear_polarity),
                        pol(feats.has_set, feats.set_polarity)
                    ),
                });
            };
            let mut mapped_clk = dff.clock;
            let mut mapped_arst = dff.clear;
            if !key.clock_polarity {
                mapped_clk.positive = !mapped_clk.positive;
            }
            if if arst_is_set { !key.set_polarity } else { !key.clear_polarity } {
                mapped_arst.positive = !mapped_arst.positive;
            }
            let mut inputs = build_default_inputs(mt);
            inputs[mt.pins.clock_in as usize] = g.emit_control(mapped_clk);
            inputs[mt.pins.data_in as usize] = match (mt.data_negated, dff.data[i]) {
                (false, d) => d,
                // DIVERGENCE (vyges-syn D4): a constant is complemented here, so the combinational
                // mapper ties it off like any other constant input. The reference adds a `Not` of
                // the constant, which the mapper treats as transparent and never maps: the export
                // then leaves the D pin on an undriven net.
                (true, Net::ONE) => Net::ZERO,
                (true, Net::ZERO) => Net::ONE,
                (true, Net::UNDEF) => Net::UNDEF,
                (true, d) => g.add(Kind::Not(vec![d]))[0],
            };
            if !dff.clear.is_always(false) {
                let at = if arst_is_set { mt.pins.set_in } else { mt.pins.clear_in };
                let n = g.emit_control(mapped_arst);
                // ⚠️ An X clear value names no pin (offset -1): the reference writes outside the
                // bundle there. Nothing is connected.
                if at >= 0 {
                    inputs[at as usize] = n;
                }
            }
            let target_out = g.add(Kind::Target(mt.cell.clone(), inputs));
            let old_out = g.output(id)[i];
            let new_out = target_out[mt.pins.data_out as usize];
            g.force_replace(&[old_out], &[new_out]);
        }
        to_remove.push(id);
    }
    for id in to_remove {
        g.remove_instance(id);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::eval::{all_values, Eval};
    use crate::ir::instance::Dff;
    use crate::ir::ControlNet;

    /// A flip-flop cell: clock `ck` ("CK" or "!CK"), an optional clear and preset expression, the
    /// output `IQ` or `!IQ`; next state `D`.
    fn ff(name: &str, ck: &str, clear: Option<&str>, preset: Option<&str>, out: &str) -> String {
        ff_next(name, ck, clear, preset, out, "D")
    }

    /// As [`ff`] with the next state given: `!D` is how a library describes a flop with only a QN
    /// pin (its state variable holds the complement, as ASAP7's `DFFASRHQNx1`).
    fn ff_next(name: &str, ck: &str, clear: Option<&str>, preset: Option<&str>, out: &str, next: &str) -> String {
        let mut pins = String::from("pin (CK) { direction : input; }\n    pin (D) { direction : input; }\n");
        let mut group = format!("clocked_on : \"{ck}\"; next_state : \"{next}\";");
        if let Some(c) = clear {
            pins.push_str("    pin (R) { direction : input; }\n");
            group.push_str(&format!(" clear : \"{c}\";"));
        }
        if let Some(p) = preset {
            pins.push_str("    pin (S) { direction : input; }\n");
            group.push_str(&format!(" preset : \"{p}\";"));
        }
        format!(
            "  cell ({name}) {{\n    area : 1.0;\n    {pins}    pin (Q) {{ direction : output; function : \"{out}\"; }}\n    ff (IQ, IQN) {{ {group} }}\n  }}\n"
        )
    }

    fn library(tag: &str, cells: &[String]) -> Libraries {
        let text = format!("library (seq) {{\n{}}}\n", cells.concat());
        let path = std::env::temp_dir().join(format!("vyges-syn-seqmap-{}-{tag}.lib", std::process::id()));
        std::fs::write(&path, text).expect("the temporary directory is writable");
        let mut libs = Libraries::default();
        libs.read(&path.to_string_lossy()).expect("the library parses");
        let _ = std::fs::remove_file(&path);
        libs
    }

    /// A constant data input on a cell with only the complemented output: the mapper complements
    /// the data, and the constant must reach the cell's D pin as a tie cell after combinational
    /// mapping, never as an undriven net. Rule (Yosys flow, as the ORFS netlist has it): a
    /// register whose next state is the constant 1, mapped to a QN-only flop, has its D tied low
    /// (here: TIEL); after the clear is released and a clock edge, Q is 1.
    #[test]
    fn a_constant_data_input_is_tied_through_the_complement() {
        let lib = library(
            "constd",
            &[
                "  cell (INV) { area : 1; pin (A) { direction : input; } pin (Y) { direction : output; function : \"!A\"; } }\n".into(),
                "  cell (TIEH) { area : 1; pin (H) { direction : output; function : \"1\"; } }\n".into(),
                "  cell (TIEL) { area : 1; pin (L) { direction : output; function : \"0\"; } }\n".into(),
                // as ASAP7 DFFASRHQNx1: only QN, the state holding !D, clear and preset swapped
                ff_next("DQNS", "CK", Some("!S"), Some("!R"), "IQ", "!D"),
            ],
        );
        for (data, want) in [(Net::ONE, "TIEL"), (Net::ZERO, "TIEH")] {
            let mut g = Graph::new();
            let ck = g.add(Kind::Input("ck".into(), 1))[0];
            let r = g.add(Kind::Input("r".into(), 1))[0];
            let q = g.add(Kind::Dff(Box::new(Dff {
                data: vec![data],
                clock: ControlNet::with_polarity(ck, true),
                clear: ControlNet::with_polarity(r, true),
                reset: ControlNet::ZERO,
                enable: ControlNet::ONE,
                init_value: vec![Trit::Undef],
                reset_value: vec![Trit::Undef],
                clear_value: vec![Trit::Zero],
            })));
            g.add(Kind::Output("q".into(), q));
            map_sequentials(&mut g, &lib).expect("the QN cell fits");
            crate::flow::combinational_mapper::map_combinationals(&mut g, &lib).expect("inverter and ties");
            let mut d_driver = None;
            for id in g.instance_list() {
                if let Kind::Target(cell, inputs) = &g.inst(id).kind {
                    if cell.name == "DQNS" {
                        let d = inputs[input_port_position(cell, "D") as usize];
                        d_driver = Some(g.try_resolve(d).map(|(i, _)| match &g.inst(i).kind {
                            Kind::Target(c, _) => c.name.clone(),
                            k => k.keyword().to_string(),
                        }));
                    }
                }
            }
            assert_eq!(d_driver, Some(Some(want.to_string())), "data {data:?}: the D pin's driver\n{}", g.dump());
            let mut e = Eval::new(&g);
            e.set_input("r", &[Trit::One]);
            e.set_input("ck", &[Trit::Zero]);
            e.set_input("r", &[Trit::Zero]);
            e.clock("ck", &[Trit::One]);
            let v = if data == Net::ONE { Trit::One } else { Trit::Zero };
            assert_eq!(e.output("q"), [v], "data {data:?}: Q after one edge");
        }
    }

    /// The mapped flip-flop behaves as the register on every input sequence: each register shape
    /// (clock edge rising or falling; no clear, or an active-high or active-low clear to zero or
    /// to one) against libraries that offer only one polarity of each pin, or only a complemented
    /// output (the mapper then complements the data and swaps clear and preset). From X, every
    /// sequence of 4 steps of (clock, data, clear), compared where the register is defined.
    #[test]
    fn mapped_flip_flops_keep_every_polarity() {
        let libs: Vec<(&str, Vec<String>)> = vec![
            ("pos", vec![ff("DP", "CK", None, None, "IQ"), ff("DPR", "CK", Some("R"), None, "IQ"), ff("DPS", "CK", None, Some("S"), "IQ")]),
            ("neg", vec![ff("DN", "!CK", None, None, "IQ"), ff("DNR", "!CK", Some("!R"), None, "IQ"), ff("DNS", "!CK", None, Some("!S"), "IQ")]),
            ("qn", vec![ff("DQN", "CK", None, None, "!IQ"), ff("DQNR", "CK", Some("!R"), None, "!IQ"), ff("DQNS", "CK", None, Some("S"), "!IQ")]),
            ("qn-neg", vec![ff("EQN", "!CK", Some("R"), None, "!IQ"), ff("EQNS", "!CK", None, Some("!S"), "!IQ"), ff("EN", "!CK", None, None, "!IQ")]),
            (
                "qn-state",
                vec![
                    ff_next("FQ", "CK", None, None, "IQ", "!D"),
                    ff_next("FQRS", "CK", Some("!S"), Some("!R"), "IQ", "!D"),
                ],
            ),
        ];
        let steps = all_values(3, false);
        for (tag, cells) in &libs {
            let lib = library(tag, cells);
            let mut mapped = 0;
            for clock_positive in [true, false] {
                for clear in [None, Some((true, Trit::Zero)), Some((false, Trit::Zero)), Some((true, Trit::One)), Some((false, Trit::One))] {
                    let mut g = Graph::new();
                    let ck = g.add(Kind::Input("ck".into(), 1))[0];
                    let d = g.add(Kind::Input("d".into(), 1));
                    let c = g.add(Kind::Input("c".into(), 1))[0];
                    let (clear_cn, clear_value) = match clear {
                        None => (ControlNet::ZERO, Trit::Undef),
                        Some((pos, v)) => (ControlNet::with_polarity(c, pos), v),
                    };
                    let q = g.add(Kind::Dff(Box::new(Dff {
                        data: d,
                        clock: ControlNet::with_polarity(ck, clock_positive),
                        clear: clear_cn,
                        reset: ControlNet::ZERO,
                        enable: ControlNet::ONE,
                        init_value: vec![Trit::Undef],
                        reset_value: vec![Trit::Undef],
                        clear_value: vec![clear_value],
                    })));
                    g.add(Kind::Output("q".into(), q));
                    let before = g.clone();
                    let mut after = g;
                    if map_sequentials(&mut after, &lib).is_err() {
                        continue;
                    }
                    mapped += 1;
                    let shape = format!("{tag}: clock {} clear {clear:?}", if clock_positive { "rising" } else { "falling" });
                    for a in &steps {
                        for b in &steps {
                            for e in &steps {
                                for f in &steps {
                                    let (mut r, mut m) = (Eval::new(&before), Eval::new(&after));
                                    for (k, s) in [a, b, e, f].into_iter().enumerate() {
                                        for x in [&mut r, &mut m] {
                                            x.set_input("d", &[s[1]]);
                                            x.set_input("c", &[s[2]]);
                                            x.clock("ck", &[s[0]]);
                                        }
                                        let (want, got) = (r.output("q")[0], m.output("q")[0]);
                                        assert!(
                                            want == Trit::Undef || want == got,
                                            "{shape}: step {k} of {:?}: register {want:?}, mapped {got:?}",
                                            [a, b, e, f]
                                        );
                                    }
                                }
                            }
                        }
                    }
                }
            }
            assert_eq!(mapped, 10, "{tag}: every register shape maps (the mapper complements clock and clear)");
        }
    }
}
