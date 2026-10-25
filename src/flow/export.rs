// SPDX-License-Identifier: Apache-2.0
//! The mapped netlist into a design database: a port per input and output bit, an instance per
//! library cell, a net per graph net, named after the design's names where it has one.

use vyges_opendb::Db;

use crate::ir::instance::{LibCell, LibDirection};
use crate::ir::{Graph, Kind, Net};

/// Each net's name from the design's names: a vector name's bit `i` is `name[from + i]`; a name on
/// an inverter's output names the inverter's input with a `*` after it; the first name a net is
/// given wins, names in instance order.
fn collect_net_names(g: &Graph) -> Vec<String> {
    let mut net_names = vec![String::new(); g.table_size() as usize];
    for id in g.instance_list() {
        let Kind::Name(nm) = &g.inst(id).kind else { continue };
        for (i, &bit) in nm.value.iter().enumerate() {
            let mut net = bit;
            if net.is_const() {
                continue;
            }
            let mut suffix = "";
            let (producer, off) = g.resolve(net);
            if let Kind::Not(a) = &g.inst(producer).kind {
                net = a[off as usize];
                if net.is_const() {
                    continue;
                }
                suffix = "*";
            }
            let slot = &mut net_names[net.id() as usize];
            if !slot.is_empty() {
                continue;
            }
            *slot = if nm.is_vector { format!("{}[{}]{suffix}", nm.name, nm.from as usize + i) } else { format!("{}{suffix}", nm.name) };
        }
    }
    net_names
}

/// A port's pin names, lowest bit first: a bus's bits from its first index toward its last.
fn pin_names(port: &crate::ir::instance::LibPort) -> Vec<String> {
    match port.bus {
        Some((from, to)) if port.is_bus => (0..port.size as i64)
            .map(|j| format!("{}[{}]", port.name, if from < to { from + j } else { from - j }))
            .collect(),
        _ => (0..port.size).map(|_| port.name.clone()).collect(),
    }
}

struct Export<'a> {
    db: &'a mut Db,
    net_names: Vec<String>,
    /// Graph net id to its database net, made when first used; empty when it could not be made.
    net2db: Vec<Option<String>>,
    net_counter: u32,
    inst_counter: u32,
}

/// An error as the run reports it.
fn syn_error(code: u32, message: String) -> String {
    format!("[ERROR SYN-{code:04}] {message}")
}

fn odb_err(code: u32) -> impl Fn(vyges_opendb::Error) -> String {
    move |e| syn_error(code, format!("Export to ODB: {e}"))
}

/// A net that could not be made: a pin connected to it is an error, a port or a loop breaker on
/// it ends the reference's run on a signal.
fn require_net(net: String, what: &str) -> Result<String, String> {
    if net.is_empty() {
        return Err(syn_error(26, format!("Export to ODB: {what} on a net that could not be made")));
    }
    Ok(net)
}

impl Export<'_> {
    /// The net's database net, made on first use: named after the design's name for it, else
    /// `n<counter>`; a name already taken falls back to the next `n<counter>`, and when that is
    /// taken too the net is empty (none made) and stays so.
    fn get_or_create_net(&mut self, net: Net) -> Result<String, String> {
        let id = net.id() as usize;
        if let Some(n) = &self.net2db[id] {
            return Ok(n.clone());
        }
        if net.is_const() {
            return Err(syn_error(
                26,
                format!("Export to ODB: constant net (id={id}) used as instance pin; tie cells should have been inserted"),
            ));
        }
        let mut name = if self.net_names[id].is_empty() {
            self.net_counter += 1;
            format!("n{}", self.net_counter - 1)
        } else {
            self.net_names[id].clone()
        };
        if self.db.create_net(&name).is_err() {
            name = format!("n{}", self.net_counter);
            self.net_counter += 1;
            if self.db.create_net(&name).is_err() {
                name.clear();
            }
        }
        self.net2db[id] = Some(name.clone());
        Ok(name)
    }

    /// A loop breaker's output net merged into its input's: the output net's terminals move onto
    /// the input net (instance pins, then ports) and it is removed; the input net stands for both.
    fn loop_breaker(&mut self, out: &[Net], a: &[Net]) -> Result<(), String> {
        for (i, &o) in out.iter().enumerate() {
            let db_out = require_net(self.get_or_create_net(o)?, "a loop breaker")?;
            let db_in = require_net(self.get_or_create_net(a[i])?, "a loop breaker")?;
            if db_in != db_out {
                for iterm in self.db.net_get_i_terms(&db_out) {
                    let (inst, pin) = iterm.split_once('/').unwrap_or((&iterm, ""));
                    self.db.connect(inst, pin, &db_in).map_err(odb_err(26))?;
                }
                for bterm in self.db.net_get_b_terms(&db_out) {
                    self.db.bterm_connect(&bterm, &db_in).map_err(odb_err(26))?;
                }
                self.db.destroy_net(&db_out).map_err(odb_err(26))?;
            }
            self.net2db[o.id() as usize] = Some(db_in);
        }
        Ok(())
    }

    /// A net and an input port per bit, `name[i]` when wider than one bit.
    fn input(&mut self, name: &str, out: &[Net]) -> Result<(), String> {
        for (i, &o) in out.iter().enumerate() {
            let port = if out.len() > 1 { format!("{name}[{i}]") } else { name.to_string() };
            self.db.create_net(&port).map_err(odb_err(26))?;
            self.net2db[o.id() as usize] = Some(port.clone());
            self.db.create_bterm(&port, &port).map_err(odb_err(26))?;
            self.db.bterm_set_io_type(&port, "INPUT").map_err(odb_err(26))?;
        }
        Ok(())
    }

    /// An output port per bit on the net it reads.
    fn output(&mut self, name: &str, value: &[Net]) -> Result<(), String> {
        for (i, &v) in value.iter().enumerate() {
            let port = if value.len() > 1 { format!("{name}[{i}]") } else { name.to_string() };
            let net = require_net(self.get_or_create_net(v)?, "an output port")?;
            self.db.create_bterm(&net, &port).map_err(odb_err(26))?;
            self.db.bterm_set_io_type(&port, "OUTPUT").map_err(odb_err(26))?;
        }
        Ok(())
    }

    /// An instance `u<counter>` of the cell, its pins in the cell's port order (supply pins
    /// skipped), each input pin on the next input bit and each output pin on the next output bit.
    fn target(&mut self, cell: &LibCell, inputs: &[Net], out: &[Net]) -> Result<(), String> {
        let inst = format!("u{}", self.inst_counter);
        self.inst_counter += 1;
        self.db
            .create_inst(&cell.name, &inst)
            .map_err(|_| syn_error(27, format!("Export to ODB: no dbMaster for cell '{}'", cell.name)))?;
        let (mut input_idx, mut output_idx) = (0, 0);
        for port in cell.ports.iter().filter(|p| !p.pwr_gnd) {
            let (code, bits) = match port.direction {
                LibDirection::Input => (28, inputs),
                LibDirection::Output => (29, out),
                _ => continue,
            };
            for pin in pin_names(port) {
                let idx = if code == 28 { &mut input_idx } else { &mut output_idx };
                let Some(&bit) = bits.get(*idx) else {
                    return Err(syn_error(
                        34,
                        format!(
                            "Export to ODB: output index {} exceeds output width {} for cell '{}' instance '{inst}'",
                            *idx,
                            bits.len(),
                            cell.name
                        ),
                    ));
                };
                *idx += 1;
                let net = self.get_or_create_net(bit)?;
                if net.is_empty() {
                    // ⚠️ The database's own refusal, not the exporter's.
                    return Err(format!("[ERROR ODB-0440] Attempt to connect iterm {inst}/{pin} to a null net"));
                }
                self.db.connect(&inst, &pin, &net).map_err(|_| {
                    syn_error(code, format!("Export to ODB: cannot find mterm '{pin}' on master '{}'", cell.name))
                })?;
            }
        }
        Ok(())
    }
}

/// The graph into a fresh database's chip and block (the block named after the design, `syn` when
/// unnamed): names collected, then every instance in order (ties, names and inverters skipped).
/// `db` holds the LEFs read and no chip yet. An error comes back as the line the run reports.
pub fn export_to_odb(g: &mut Graph, db: &mut Db) -> Result<(), String> {
    g.normalize();
    // ⚠️ A die is refused without a technology: that is the no-LEF case.
    db.create_chip("", "", "DIE")
        .map_err(|_| syn_error(33, "Export to ODB: no tech in database; read LEF files first".into()))?;
    let block_name = if g.name.is_empty() { "syn".to_string() } else { g.name.clone() };
    db.create_chip_block("", &block_name).map_err(odb_err(33))?;

    let mut ex = Export {
        db,
        net_names: collect_net_names(g),
        net2db: vec![None; g.table_size() as usize],
        net_counter: 0,
        inst_counter: 0,
    };
    for id in g.instance_list() {
        let out = g.output(id);
        match &g.inst(id).kind {
            Kind::TieLow | Kind::TieHigh | Kind::TieX | Kind::Name(_) | Kind::Not(_) => {}
            Kind::LoopBreaker(a) => ex.loop_breaker(&out, a)?,
            Kind::Input(name, _) => ex.input(name, &out)?,
            Kind::Output(name, value) => ex.output(name, value)?,
            Kind::Target(cell, inputs) => ex.target(cell, inputs, &out)?,
            k => println!("[WARNING SYN-0030] Export to ODB: skipping unexpected instance type '{}'", k.keyword()),
        }
    }
    let ports = ex.db.bterm_names().len();
    println!(
        "[INFO SYN-0031] Export to ODB: created {} instances, {} nets, {ports} ports",
        ex.inst_counter, ex.net_counter
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::instance::LibPort;

    fn port(name: &str, size: u32, bus: Option<(i64, i64)>) -> LibPort {
        LibPort {
            name: name.into(),
            direction: LibDirection::Input,
            size,
            is_bus: bus.is_some(),
            bus,
            pwr_gnd: false,
            function: None,
        }
    }

    // Rule: a bus pin's bit j is the bus's first index plus j counting up, or minus j counting
    // down; a scalar pin is its name.
    #[test]
    fn bus_pins_count_from_the_first_index() {
        assert_eq!(pin_names(&port("A", 1, None)), ["A"]);
        assert_eq!(pin_names(&port("D", 3, Some((0, 2)))), ["D[0]", "D[1]", "D[2]"]);
        assert_eq!(pin_names(&port("D", 2, Some((3, 2)))), ["D[3]", "D[2]"]);
    }
}
