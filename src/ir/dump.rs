// SPDX-License-Identifier: Apache-2.0
//! The text form of the graph: one line per instance, `%<id>:<width> = <keyword> <operands>`.
//!
//! A value prints as constant bits (most significant first), as one run of an instance's outputs
//! (`%id`, `%id:w`, `%id+off`, `%id+off:w`), or as a `[ ... ]` concatenation of such runs, most
//! significant first. Tie cells are not printed.

use std::fmt::Write;

use super::graph::{Graph, InstId};
use super::instance::{Kind, LibDirection, PortDirection};
use super::net::{is_const, ControlNet, Net};

fn const_char(n: Net) -> char {
    match n {
        Net::ZERO => '0',
        Net::ONE => '1',
        _ => 'X',
    }
}

/// What drives `net` for printing: the instance (its identity, the bit, its output width). A slot
/// emptied under a reader still prints: the reference reads the empty slot as an instance of its
/// own, at bit 0 and of width 0, so it is its own one-bit run.
fn driver(g: &Graph, net: Net) -> (u64, u32, u32) {
    match g.try_resolve(net) {
        Some((id, off)) => (id as u64, off, g.inst(id).output_width()),
        None => (1 << 40 | net.0 as u64, 0, 0),
    }
}

pub fn write_net(os: &mut String, g: &Graph, net: Net) {
    match net {
        Net::ZERO => os.push('0'),
        Net::ONE => os.push('1'),
        Net::UNDEF => os.push('X'),
        Net::SENTINEL => os.push('E'),
        _ => {
            let (_, offset, _) = driver(g, net);
            let base = net.0 - offset;
            if offset > 0 {
                let _ = write!(os, "%{base}+{offset}");
            } else {
                let _ = write!(os, "%{base}");
            }
        }
    }
}

fn write_control(os: &mut String, g: &Graph, cn: ControlNet) {
    if !cn.positive {
        os.push('!');
    }
    write_net(os, g, cn.net);
}

pub fn write_value(os: &mut String, g: &Graph, bv: &[Net]) {
    if bv.is_empty() {
        os.push_str("[]");
        return;
    }
    if is_const(bv) {
        os.extend(bv.iter().rev().map(|&n| const_char(n)));
        return;
    }
    // One run of a single cell's consecutive outputs.
    let (_, off0, width0) = driver(g, bv[0]);
    let first = bv[0].0;
    let w = bv.len() as u32;
    let consecutive = off0 + w <= width0 && bv.iter().enumerate().all(|(i, n)| n.0 == first + i as u32);
    if consecutive {
        let base = first - off0;
        if w == 1 && off0 == 0 {
            let _ = write!(os, "%{base}");
        } else if off0 == 0 {
            let _ = write!(os, "%{base}:{w}");
        } else {
            let _ = write!(os, "%{base}+{off0}:{w}");
        }
        return;
    }
    // A concatenation: runs of constants, and runs of one cell's consecutive outputs.
    os.push_str("[ ");
    let mut i = bv.len() as i64 - 1;
    let mut first_part = true;
    while i >= 0 {
        if !first_part {
            os.push(' ');
        }
        first_part = false;
        let n = bv[i as usize];
        if n.is_const() {
            let start = i;
            while i >= 0 && bv[i as usize].is_const() {
                i -= 1;
            }
            let mut j = start;
            while j > i {
                os.push(const_char(bv[j as usize]));
                j -= 1;
            }
        } else {
            let (inst0, off0, _) = driver(g, n);
            let start = i;
            i -= 1;
            while i >= 0 {
                let (inst_i, off_i, _) = driver(g, bv[i as usize]);
                if inst_i != inst0 || off_i as i64 != off0 as i64 - (start - i) {
                    break;
                }
                i -= 1;
            }
            let run_len = (start - i) as u32;
            let run_offset = off0 + 1 - run_len;
            let base = bv[start as usize].0 - off0;
            if run_len > 1 {
                let _ = write!(os, "%{base}+{run_offset}:{run_len}");
            } else if off0 > 0 {
                let _ = write!(os, "%{base}+{off0}");
            } else {
                let _ = write!(os, "%{base}");
            }
        }
    }
    os.push_str(" ]");
}

fn write_operands(os: &mut String, g: &Graph, kind: &Kind, id: u32) {
    let v = |os: &mut String, b: &[Net]| {
        os.push(' ');
        write_value(os, g, b);
    };
    match kind {
        Kind::TieHigh | Kind::TieLow | Kind::TieX | Kind::Dangling(_) => {}
        Kind::Buffer(a) | Kind::Not(a) | Kind::LoopBreaker(a) => v(os, a),
        Kind::Bin(_, a, b) => {
            v(os, a);
            v(os, b);
        }
        Kind::Mux(sel, a, b) => {
            os.push(' ');
            write_net(os, g, *sel);
            v(os, a);
            v(os, b);
        }
        Kind::Adc(a, b, cin) => {
            v(os, a);
            v(os, b);
            os.push(' ');
            write_net(os, g, *cin);
        }
        Kind::Shift(_, a, b, stride) => {
            v(os, a);
            v(os, b);
            let _ = write!(os, " #{stride}");
        }
        Kind::Dff(d) => {
            v(os, &d.data);
            os.push_str(" clk=");
            write_control(os, g, d.clock);
            if !d.clear.is_always(false) {
                os.push_str(" clr=");
                write_control(os, g, d.clear);
            }
            if !d.reset.is_always(false) {
                os.push_str(" rst=");
                write_control(os, g, d.reset);
            }
            if !d.enable.is_always(true) {
                os.push_str(" en=");
                write_control(os, g, d.enable);
            }
        }
        Kind::Input(name, _) => {
            let _ = write!(os, " \"{name}\"");
        }
        Kind::Output(name, value) => {
            let _ = write!(os, " \"{name}\"");
            v(os, value);
        }
        Kind::Name(nm) => {
            let _ = write!(os, " \"{}\" {} {}", nm.name, nm.from, nm.to);
            if nm.tentative {
                os.push_str(" tentative");
            }
            if nm.is_vector {
                os.push_str(" vector");
            }
            v(os, &nm.value);
        }
        Kind::Target(cell, inputs) => {
            let _ = writeln!(os, " \"{}\" {{", cell.name);
            let (mut in_off, mut out_off) = (0usize, 0u32);
            for port in &cell.ports {
                if port.pwr_gnd {
                    continue;
                }
                let pw = port.size;
                match port.direction {
                    LibDirection::Input => {
                        let _ = write!(os, "  input \"{}\" = ", port.name);
                        write_value(os, g, &inputs[in_off..in_off + pw as usize]);
                        os.push('\n');
                        in_off += pw as usize;
                    }
                    LibDirection::Output => {
                        let _ = writeln!(os, "  %{}:{pw} = output \"{}\"", id + out_off, port.name);
                        out_off += pw;
                    }
                    LibDirection::Bidirect | LibDirection::Other => {}
                }
            }
            os.push('}');
        }
        Kind::Other(o) => {
            let _ = writeln!(os, " \"{}\" {{", o.cell_type);
            let mut out_off = 0u32;
            for port in &o.ports {
                match port.direction {
                    PortDirection::Input => {
                        let _ = write!(os, "  input \"{}\" = ", port.name);
                        write_value(os, g, &port.value);
                        os.push('\n');
                    }
                    PortDirection::Output => {
                        let _ = writeln!(os, "  %{}:{} = output \"{}\"", id + out_off, port.width, port.name);
                        out_off += port.width;
                    }
                    PortDirection::InOut => {
                        let _ = write!(os, "  %{}:{} = io \"{}\" = ", id + out_off, port.width, port.name);
                        write_value(os, g, &port.value);
                        os.push('\n');
                        out_off += port.width;
                    }
                }
            }
            os.push('}');
        }
    }
}

impl Graph {
    pub fn dump_instance(&self, os: &mut String, id: InstId) {
        let inst = self.inst(id);
        let _ = write!(os, "%{}:{} = {}", inst.base, inst.output_width(), inst.kind.keyword());
        write_operands(os, self, &inst.kind, inst.base);
    }

    /// Every instance but the ties, one per line, in slot order.
    pub fn dump(&self) -> String {
        let mut os = String::new();
        for id in self.instance_list() {
            if self.inst(id).kind.is_tie() {
                continue;
            }
            self.dump_instance(&mut os, id);
            os.push('\n');
        }
        os
    }
}

#[cfg(test)]
mod tests {
    use crate::ir::{Graph, Kind};

    // Rule: a slot emptied by removing its instance while something still reads it prints as
    // `%<slot>`, a one-bit run of its own (the reference resolves the empty slot to itself, at bit 0,
    // width 0). Mapping a two-bit register leaves its relocated output read by a dead forwarding
    // buffer: bit 0 is replaced at the first relocation, bit 1 only at the second.
    #[test]
    fn an_emptied_slot_prints_as_its_own_net() {
        let text = "%3:2 = input \"a\"\n%5:2 = dff %3:2 clk=%3\n%7:0 = output \"o\" %5:2\n";
        let mut g: Graph = crate::ir::parse::parse(text, None).unwrap();
        let mut it = g.instances();
        let mut dff = None;
        while let Some(id) = it.next(&g) {
            if matches!(g.inst(id).kind, Kind::Dff(_)) {
                dff = Some(id);
            }
        }
        let dff = dff.unwrap();
        for i in 0..2 {
            let old = g.output(dff)[i];
            g.force_replace(&[old], &[crate::ir::net::Net(3 + i as u32)]);
        }
        let last = g.output(dff)[0].0;
        g.remove_instance(dff);
        let dump = g.dump();
        // the second forwarding buffer: bit 1 the input, bit 0 the emptied slot
        assert!(dump.contains(&format!("buf [ %3+1 %{last} ]")), "{dump}");
    }
}
