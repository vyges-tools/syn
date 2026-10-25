// SPDX-License-Identifier: Apache-2.0
//! Library cells the design instantiates (opaque `other` cells named after a Liberty cell) become
//! target cells.

use std::collections::BTreeMap;

use crate::elab::backend::ElabError;
use crate::ir::instance::{Kind, LibDirection, PortDirection};
use crate::ir::net::Net;
use crate::ir::Graph;
use crate::library::Libraries;

/// Normalizes, then turns every `other` cell that names a library cell into a target cell: its
/// input and inout values concatenated at the library's input offsets, its outputs taken from
/// the target's at the library's output offsets.
///
/// The library's offsets walk the cell's ports in its order, power and ground pins skipped: an
/// input or inout takes the next input bits, an output or inout the next output bits, any other
/// port none. Widths must agree with the instantiation, in total (SYN-0010/0011) and per port
/// (SYN-0036/0038); a port the library lacks is SYN-0035/0037.
pub fn import_targets(g: &mut Graph, libs: &Libraries) -> Result<(), ElabError> {
    g.normalize();
    let mut it = g.instances();
    while let Some(id) = it.next(g) {
        let Kind::Other(other) = &g.inst(id).kind else { continue };
        let Some(cell) = libs.find_cell(&other.cell_type) else { continue };
        let other = other.clone();
        let err = |code: u32, message: String| ElabError { code, message };

        let mut lib_input_offset: BTreeMap<&str, u32> = BTreeMap::new();
        let mut lib_output_offset: BTreeMap<&str, u32> = BTreeMap::new();
        let (mut lib_input_width, mut lib_output_width) = (0u32, 0u32);
        for port in cell.ports.iter().filter(|p| !p.pwr_gnd) {
            match port.direction {
                LibDirection::Input => {
                    lib_input_offset.insert(&port.name, lib_input_width);
                    lib_input_width += port.size;
                }
                LibDirection::Output => {
                    lib_output_offset.insert(&port.name, lib_output_width);
                    lib_output_width += port.size;
                }
                LibDirection::Bidirect => {
                    lib_input_offset.insert(&port.name, lib_input_width);
                    lib_output_offset.insert(&port.name, lib_output_width);
                    lib_input_width += port.size;
                    lib_output_width += port.size;
                }
                LibDirection::Other => {}
            }
        }

        let other_input_width: u32 =
            other.ports.iter().filter(|p| p.direction != PortDirection::Output).map(|p| p.width).sum();
        let other_output_width = other.output_width;
        if other_input_width != lib_input_width {
            return Err(err(
                10,
                format!(
                    "importTargets: cell '{}' input width mismatch: Verilog instantiation has {} bits, Liberty has {} bits.",
                    other.cell_type, other_input_width, lib_input_width
                ),
            ));
        }
        if other_output_width != lib_output_width {
            return Err(err(
                11,
                format!(
                    "importTargets: cell '{}' output width mismatch: Verilog instantiation has {} bits, Liberty has {} bits.",
                    other.cell_type, other_output_width, lib_output_width
                ),
            ));
        }

        let lib_port = |name: &str| cell.ports.iter().find(|p| p.name == name);
        let mut inputs = vec![Net::SENTINEL; lib_input_width as usize];
        for port in other.ports.iter().filter(|p| p.direction != PortDirection::Output) {
            let (Some(lp), Some(&offset)) = (lib_port(&port.name), lib_input_offset.get(port.name.as_str())) else {
                return Err(err(
                    35,
                    format!(
                        "importTargets: cell '{}' Liberty definition is missing port '{}' connected in Verilog instantiation.",
                        other.cell_type, port.name
                    ),
                ));
            };
            if lp.size != port.width {
                return Err(err(
                    36,
                    format!(
                        "importTargets: cell '{}' instantiated with mismatched width of port '{}': {} in Verilog vs {} in Liberty",
                        other.cell_type, port.name, port.width, lp.size
                    ),
                ));
            }
            for i in 0..port.width as usize {
                inputs[offset as usize + i] = port.value[i];
            }
        }

        let old_output = g.output(id);
        let target_output = g.add(Kind::Target(cell.clone(), inputs));
        let mut output_replacement = vec![Net::SENTINEL; lib_output_width as usize];
        let mut offset = 0usize;
        for port in other.ports.iter().filter(|p| p.direction != PortDirection::Input) {
            let (Some(lp), Some(&lib_offset)) = (lib_port(&port.name), lib_output_offset.get(port.name.as_str())) else {
                return Err(err(
                    37,
                    format!(
                        "importTargets: cell '{}' Liberty definition is missing port '{}' connected in Verilog instantiation.",
                        other.cell_type, port.name
                    ),
                ));
            };
            if lp.size != port.width {
                return Err(err(
                    38,
                    format!(
                        "importTargets: cell '{}' instantiated with mismatched width of port '{}': {} in Verilog vs {} in Liberty",
                        other.cell_type, port.name, port.width, lp.size
                    ),
                ));
            }
            for i in 0..port.width as usize {
                // ⚠️ A target's outputs are its OUTPUT ports only; an inout's offset can lie past
                // them, where the reference reads outside the bundle. No net there.
                output_replacement[offset + i] =
                    target_output.get(lib_offset as usize + i).copied().unwrap_or(Net::SENTINEL);
            }
            offset += port.width as usize;
        }

        g.force_replace(&old_output, &output_replacement);
        g.remove_instance(id);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::parse::parse;
    use vyges_loom::liberty::Lib;

    // Library order A, Y, PAD, B (and a power pin): inputs A, PAD, B; outputs Y, PAD.
    const LIB: &str = r#"library (t) {
      cell (IOB) {
        pg_pin (VDD) { pg_type : primary_power; }
        pin (A) { direction : input; }
        pin (Y) { direction : output; }
        pin (PAD) { direction : inout; }
        pin (B) { direction : input; }
      }
    }"#;

    fn imported(ir: &str) -> Result<(), ElabError> {
        let mut libs = Libraries::default();
        libs.add(&Lib::parse(LIB).unwrap());
        let mut g = parse(ir, None).expect("parses");
        import_targets(&mut g, &libs)
    }

    // Rule: an inout takes input AND output bits of the library's totals, a power pin neither;
    // an instantiation's inout counts toward its inputs only (its output width is its outputs').
    // ⟹ A cell with an inout never imports: the output totals differ by the inout's width, and
    // the check stops it before any offset is used.
    #[test]
    fn an_inout_counts_on_both_library_totals() {
        let ir = "%3:1 = input \"a\"\n%4:1 = input \"b\"\n%5:1 = input \"p\"\n%6:1 = other \"IOB\" {\n  input \"A\" = %3\n  input \"B\" = %4\n  %6:1 = io \"PAD\" = %5\n  %6:1 = output \"Y\"\n}\n%7:0 = output \"y\" %6\n";
        let e = imported(ir).unwrap_err();
        assert_eq!(e.code, 11);
        assert_eq!(
            e.message,
            "importTargets: cell 'IOB' output width mismatch: Verilog instantiation has 1 bits, Liberty has 2 bits."
        );
        // without the inout, the inputs are short by its bit
        let ir = "%3:1 = input \"a\"\n%4:1 = input \"b\"\n%6:1 = other \"IOB\" {\n  input \"A\" = %3\n  input \"B\" = %4\n  %6:1 = output \"Y\"\n}\n%7:0 = output \"y\" %6\n";
        let e = imported(ir).unwrap_err();
        assert_eq!((e.code, e.message.ends_with("has 2 bits, Liberty has 3 bits.")), (10, true));
    }
}
