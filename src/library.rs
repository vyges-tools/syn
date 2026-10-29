// SPDX-License-Identifier: Apache-2.0
//! The Liberty libraries a run reads, in the order it reads them, as synthesis sees their cells.

use std::collections::BTreeMap;
use std::sync::Arc;

use vyges_loom::liberty::{Lib, PortDirection};
use vyges_slang_lib::elab as fe;

use crate::ir::instance::{LibCell, LibDirection, LibPort, LibSeq};

/// One library's cells, by name (the order its cells are walked in).
struct Library {
    cells: BTreeMap<String, Arc<LibCell>>,
}

/// Every library read, in read order.
#[derive(Default)]
pub struct Libraries {
    libs: Vec<Library>,
}

fn lib_cell(c: &vyges_loom::liberty::Cell) -> LibCell {
    let ports = c
        .ports
        .iter()
        .map(|p| LibPort {
            name: p.name.clone(),
            direction: match p.direction {
                PortDirection::Input => LibDirection::Input,
                PortDirection::Output => LibDirection::Output,
                PortDirection::Bidirect => LibDirection::Bidirect,
                PortDirection::Tristate | PortDirection::Internal | PortDirection::Unknown => LibDirection::Other,
            },
            size: p.size,
            is_bus: p.bus.is_some(),
            bus: p.bus,
            pwr_gnd: p.pwr_gnd,
            function: if p.bus.is_none() { c.pins.get(&p.name).and_then(|pin| pin.function.clone()) } else { None },
        })
        .collect();
    let unquote = |v: &String| v.trim().trim_matches('"').to_string();
    // A latch's enable and data_in sit where a flip-flop's clocked_on and next_state do, as the
    // reference's one sequential record holds them.
    let seq = c.seq_group.as_ref().map(|s| LibSeq {
        latch: s.latch,
        iq: s.iq.clone(),
        clocked_on: s.attrs.get(if s.latch { "enable" } else { "clocked_on" }).map(unquote),
        next_state: s.attrs.get(if s.latch { "data_in" } else { "next_state" }).map(unquote),
        clear: s.attrs.get("clear").map(unquote),
        preset: s.attrs.get("preset").map(unquote),
    });
    LibCell {
        name: c.name.clone(),
        area: c.area as f32,
        is_macro: c.is_macro,
        is_sequential: c.is_seq,
        ports,
        dont_use: c.dont_use,
        seq,
    }
}

/// Every library, in read order, and in each its cells by name: the order the reference walks them.
impl Libraries {
    pub fn cells(&self) -> impl Iterator<Item = &Arc<LibCell>> {
        self.libs.iter().flat_map(|l| l.cells.values())
    }
}

/// A Liberty boolean expression that is one port, or the complement of one port: (non-inverted,
/// the port's name). `None` for anything else — a constant, an operator, a double complement.
/// Complements are `!` before and `'` after, parentheses anywhere around.
pub fn pin_expr(text: &str) -> Option<(bool, String)> {
    let mut negations = 0;
    let mut name: Option<String> = None;
    let b = text.as_bytes();
    let mut i = 0;
    while i < b.len() {
        match b[i] {
            b' ' | b'\t' | b'(' | b')' => i += 1,
            b'!' | b'\'' => {
                negations += 1;
                i += 1;
            }
            c if c.is_ascii_alphanumeric() || c == b'_' || c == b'[' || c == b']' || c == b'.' || c == b'$' || c == b':' => {
                if name.is_some() {
                    // a second operand: an operator, explicit or implied
                    return None;
                }
                let start = i;
                while i < b.len() && !matches!(b[i], b' ' | b'\t' | b'(' | b')' | b'!' | b'\'' | b'*' | b'&' | b'+' | b'|' | b'^') {
                    i += 1;
                }
                name = Some(text[start..i].to_string());
            }
            _ => return None,
        }
    }
    let name = name?;
    if name == "0" || name == "1" {
        return None;
    }
    match negations {
        0 => Some((true, name)),
        1 => Some((false, name)),
        _ => None,
    }
}

impl Libraries {
    /// Reads a Liberty file as one more library.
    pub fn read(&mut self, path: &str) -> Result<(), String> {
        let lib = Lib::load(path).map_err(|e| format!("{path}: {e}"))?;
        self.add(&lib);
        Ok(())
    }

    /// Adds a parsed library after those already read.
    pub fn add(&mut self, lib: &Lib) {
        let cells = lib.cells.iter().map(|(n, c)| (n.clone(), Arc::new(lib_cell(c)))).collect();
        self.libs.push(Library { cells });
    }

    /// Withhold every cell whose name matches `pattern` (`*` any run, `?` any one character) from
    /// mapping, as `set_dont_use` does: it sets the same flag as the Liberty `dont_use : true`
    /// attribute (OpenSTA `LibertyCell::setDontUse`), which is the one the mappers read. Returns
    /// how many cells it matched, across every library.
    pub fn set_dont_use(&mut self, pattern: &str) -> usize {
        let mut n = 0;
        for lib in &mut self.libs {
            for (name, cell) in lib.cells.iter_mut() {
                if vyges_rsz::job::glob_match(pattern, name) {
                    Arc::make_mut(cell).dont_use = true;
                    n += 1;
                }
            }
        }
        n
    }

    /// The cell of this name in the first library, in read order, that has one.
    pub fn find_cell(&self, name: &str) -> Option<Arc<LibCell>> {
        self.libs.iter().find_map(|l| l.cells.get(name).cloned())
    }

    /// Every library cell as a blackbox module the design may instantiate: libraries in read order,
    /// cells by name, ports in the cell's order — power and ground pins and ports that are neither
    /// input, output nor inout left out; a bus as wide as its bits, anything else one bit.
    pub fn blackboxes(&self) -> Vec<fe::BlackboxCell> {
        let mut out = Vec::new();
        for lib in &self.libs {
            for cell in lib.cells.values() {
                let ports = cell
                    .ports
                    .iter()
                    .filter(|p| !p.pwr_gnd)
                    .filter_map(|p| {
                        let direction = match p.direction {
                            LibDirection::Input => fe::Dir::Input,
                            LibDirection::Output => fe::Dir::Output,
                            LibDirection::Bidirect => fe::Dir::InOut,
                            LibDirection::Other => return None,
                        };
                        let width = if p.is_bus { p.size as i32 } else { 1 };
                        Some(fe::BlackboxPort { name: p.name.clone(), direction, width })
                    })
                    .collect();
                out.push(fe::BlackboxCell { name: cell.name.clone(), ports });
            }
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const LIB: &str = r#"library (l) {
  cell (inv_0) { area : 1; pin (A) { direction : input; } pin (Y) { direction : output; function : "!A"; } }
  cell (inv_1) { area : 2; pin (A) { direction : input; } pin (Y) { direction : output; function : "!A"; } }
  cell (buf_1) { area : 2; dont_use : true; pin (A) { direction : input; } pin (Y) { direction : output; function : "A"; } }
}"#;

    /// `set_dont_use` marks exactly the cells its pattern names and leaves a cell the library
    /// already withholds withheld; a pattern naming nothing reports 0 rather than failing.
    #[test]
    fn set_dont_use_marks_the_matching_cells_only() {
        let mut libs = Libraries::default();
        libs.add(&Lib::parse(LIB).unwrap());
        let du = |l: &Libraries, n: &str| l.find_cell(n).unwrap().dont_use;
        assert!(!du(&libs, "inv_0") && !du(&libs, "inv_1") && du(&libs, "buf_1"));
        assert_eq!(libs.set_dont_use("*_0"), 1);
        assert!(du(&libs, "inv_0") && !du(&libs, "inv_1") && du(&libs, "buf_1"));
        assert_eq!(libs.set_dont_use("inv_?"), 2);
        assert!(du(&libs, "inv_1"));
        assert_eq!(libs.set_dont_use("nand*"), 0);
    }
}
