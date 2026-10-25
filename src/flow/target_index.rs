// SPDX-License-Identifier: Apache-2.0
//! The library's combinational cells by NPN class, for mapping: every representative a cut's
//! function could canonicalize to, with the transform onto each cell's pins; the inverter; the
//! tie cells.

use std::collections::BTreeMap;
use std::sync::Arc;

use vyges_loom::liberty_func::Func;

use super::npn::{mask6, npn_semiclass_all_repr, Npn, Truth6};
use crate::ir::instance::{LibCell, LibDirection};
use crate::library::Libraries;

pub const CUT_MAXIMUM: usize = 6;

/// One cell for a class; `via` rewires the class's canonical inputs onto the cell's pins.
#[derive(Clone, Debug)]
pub struct MapTarget {
    pub cell: Arc<LibCell>,
    pub via: Npn,
}

#[derive(Default)]
pub struct TargetIndex {
    /// By (number of inputs, representative).
    pub classes: BTreeMap<(usize, Truth6), Vec<MapTarget>>,
    pub inverter: Option<Arc<LibCell>>,
    /// The cell and which of its outputs.
    pub tie_low: Option<(Arc<LibCell>, usize)>,
    pub tie_high: Option<(Arc<LibCell>, usize)>,
}

/// The function's truth table over `inputs` (a port not among them is never 1).
fn fexpr_eval(f: &Func, inputs: &[&str]) -> Truth6 {
    match f {
        Func::Port(p) => {
            let idx = inputs.iter().position(|i| i == p).unwrap_or(inputs.len());
            let mut ret = 0;
            for row in 0..1usize << inputs.len() {
                if row & 1 << idx != 0 {
                    ret |= 1u64 << row;
                }
            }
            ret
        }
        Func::Not(a) => mask6(inputs.len()) & !fexpr_eval(a, inputs),
        Func::Or(a, b) => fexpr_eval(a, inputs) | fexpr_eval(b, inputs),
        Func::And(a, b) => fexpr_eval(a, inputs) & fexpr_eval(b, inputs),
        Func::Xor(a, b) => fexpr_eval(a, inputs) ^ fexpr_eval(b, inputs),
        Func::One => mask6(inputs.len()),
        Func::Zero => 0,
    }
}

/// (area, name) smaller than the cell held, or none held.
fn smaller(cell: &LibCell, held: Option<&Arc<LibCell>>) -> bool {
    match held {
        None => true,
        Some(h) => cell.area < h.area || (cell.area == h.area && cell.name < h.name),
    }
}

/// Every library cell, libraries in read order and each one's cells by name: sequential cells and
/// cells with a pin other than input or output, or more than six inputs, skipped; tie cells (no
/// input; a 0 and a 1 output, or one constant output) noted, the smallest by (area, name), before
/// `dont_use` is looked at; then, of the rest with one output and its function, the smallest
/// inverter noted and the cell listed under every representative of its function. Each class then
/// keeps one cell per complement pattern: the smallest by (area, name), then the lowest pin order.
pub fn build_index(libs: &Libraries) -> TargetIndex {
    let mut index = TargetIndex::default();
    for cell in libs.cells() {
        if cell.is_sequential {
            continue;
        }
        let mut inputs = Vec::new();
        let mut outputs = Vec::new();
        let mut skip = false;
        for p in cell.ports.iter().filter(|p| !p.pwr_gnd) {
            match p.direction {
                LibDirection::Input => inputs.push(p),
                LibDirection::Output => outputs.push(p),
                _ => {
                    skip = true;
                    break;
                }
            }
        }
        if skip || inputs.len() > CUT_MAXIMUM {
            continue;
        }
        let names: Vec<&str> = inputs.iter().map(|p| p.name.as_str()).collect();
        let is_port = |n: &str| cell.ports.iter().any(|p| p.name == n);
        let function = |i: usize| -> Option<Truth6> {
            let text = outputs[i].function.as_deref()?;
            Some(fexpr_eval(&Func::parse_in(text, is_port)?, &names))
        };

        if inputs.is_empty() {
            if outputs.len() == 2 {
                if let (Some(f0), Some(f1)) = (function(0), function(1)) {
                    if (f0 == 0 && f1 == 1) || (f0 == 1 && f1 == 0) {
                        if smaller(cell, index.tie_low.as_ref().map(|t| &t.0)) {
                            index.tie_low = Some((cell.clone(), if f0 == 0 { 0 } else { 1 }));
                        }
                        if smaller(cell, index.tie_high.as_ref().map(|t| &t.0)) {
                            index.tie_high = Some((cell.clone(), if f0 == 1 { 0 } else { 1 }));
                        }
                    }
                }
            }
            if outputs.len() == 1 {
                if let Some(f0) = function(0) {
                    if f0 == 0 && smaller(cell, index.tie_low.as_ref().map(|t| &t.0)) {
                        index.tie_low = Some((cell.clone(), 0));
                    }
                    if f0 == 1 && smaller(cell, index.tie_high.as_ref().map(|t| &t.0)) {
                        index.tie_high = Some((cell.clone(), 0));
                    }
                }
            }
        }

        // ⚠️ After the tie cells: a library may mark its tie cells dont_use.
        if cell.dont_use {
            continue;
        }
        if outputs.len() != 1 {
            continue;
        }
        let Some(func) = function(0) else { continue };
        if inputs.len() == 1 && func == 0b01 && smaller(cell, index.inverter.as_ref()) {
            index.inverter = Some(cell.clone());
        }
        npn_semiclass_all_repr(func, inputs.len(), |repr, npn| {
            index.classes.entry((inputs.len(), repr)).or_default().push(MapTarget { cell: cell.clone(), via: npn.inv() });
        });
    }

    for targets in index.classes.values_mut() {
        targets.sort_by(|a, b| {
            a.via
                .c_fingerprint()
                .cmp(&b.via.c_fingerprint())
                .then(a.cell.area.partial_cmp(&b.cell.area).unwrap_or(std::cmp::Ordering::Equal))
                .then_with(|| a.cell.name.cmp(&b.cell.name))
                .then_with(|| a.via.permutation.cmp(&b.via.permutation))
        });
        targets.dedup_by_key(|t| t.via.c_fingerprint());
    }
    index
}

#[cfg(test)]
mod tests {
    use super::*;

    // Rule: a port's table has a 1 on every row where that input is 1; a port that is not an
    // input is never 1; NOT complements within the table's rows only.
    #[test]
    fn functions_evaluate_over_the_input_order() {
        let and = Func::parse_in("A1 & !A2", |_| true).unwrap();
        assert_eq!(fexpr_eval(&and, &["A1", "A2"]), 0b0010);
        assert_eq!(fexpr_eval(&and, &["A2", "A1"]), 0b0100);
        let q = Func::parse_in("!IQ", |_| true).unwrap();
        assert_eq!(fexpr_eval(&q, &["D"]), 0b11);
    }
}
