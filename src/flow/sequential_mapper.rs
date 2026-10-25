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
            inputs[mt.pins.data_in as usize] =
                if mt.data_negated { g.add(Kind::Not(vec![dff.data[i]]))[0] } else { dff.data[i] };
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
