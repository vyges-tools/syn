// SPDX-License-Identifier: Apache-2.0
//! The Liberty libraries a run reads, in the order it reads them, as synthesis sees their cells.

use std::collections::BTreeMap;
use std::sync::Arc;

use vyges_loom::liberty::{Lib, PortDirection};
use vyges_slang_lib::elab as fe;

use crate::ir::instance::{LibCell, LibDirection, LibPort};

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
            pwr_gnd: p.pwr_gnd,
        })
        .collect();
    LibCell { name: c.name.clone(), area: c.area as f32, is_macro: c.is_macro, is_sequential: c.is_seq, ports }
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
