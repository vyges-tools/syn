// SPDX-License-Identifier: Apache-2.0
//! Reading the text form back into a graph (the inverse of `dump`).
//!
//! Each line's declared `%id` is honoured by padding the table with empty slots, so a dump with
//! gaps in its id space reads back with the same ids. A `target` block is read as a library cell
//! when a library is given, and as an opaque `other` cell otherwise. Flip-flop initial, reset and
//! clear values are not in the text; they read back undefined.

use std::collections::HashMap;
use std::sync::Arc;

use super::graph::Graph;
use super::instance::{BinOp, Dff, Kind, LibCell, LibDirection, NameInst, OtherInst, OtherPort, PortDirection, ShiftOp};
use super::net::{consecutive, Bundle, ControlNet, Net, Trit};

/// Library cells by name, for `target` blocks.
pub type CellLookup<'a> = &'a dyn Fn(&str) -> Option<Arc<LibCell>>;

pub fn parse(text: &str, lib: Option<CellLookup>) -> Result<Graph, String> {
    let mut p = Parser { src: text.as_bytes(), pos: 0, line: 1, lib };
    let mut g = Graph::new();
    while p.pos < p.src.len() {
        p.skip_blanks();
        if p.at_end() {
            break;
        }
        if p.src[p.pos] == b'\n' {
            p.advance();
            continue;
        }
        p.parse_line(&mut g)?;
    }
    Ok(g)
}

struct Parser<'a> {
    src: &'a [u8],
    pos: usize,
    line: u32,
    lib: Option<CellLookup<'a>>,
}

type R<T> = Result<T, String>;

impl Parser<'_> {
    fn peek(&self) -> u8 {
        self.src.get(self.pos).copied().unwrap_or(0)
    }
    fn advance(&mut self) -> u8 {
        let c = self.src[self.pos];
        self.pos += 1;
        if c == b'\n' {
            self.line += 1;
        }
        c
    }
    fn at_end(&self) -> bool {
        self.pos >= self.src.len()
    }
    fn skip_spaces(&mut self) {
        while self.pos < self.src.len() && (self.src[self.pos] == b' ' || self.src[self.pos] == b'\t') {
            self.pos += 1;
        }
    }
    fn skip_comment(&mut self) {
        if self.peek() == b';' {
            while self.pos < self.src.len() && self.src[self.pos] != b'\n' {
                self.pos += 1;
            }
        }
    }
    fn skip_blanks(&mut self) {
        self.skip_spaces();
        self.skip_comment();
    }
    fn matches(&mut self, c: u8) -> bool {
        if !self.at_end() && self.src[self.pos] == c {
            self.advance();
            true
        } else {
            false
        }
    }
    fn expect(&mut self, c: u8) -> R<()> {
        if self.matches(c) {
            Ok(())
        } else {
            self.error(&format!("expected '{}'", c as char))
        }
    }
    fn expect_newline(&mut self) -> R<()> {
        self.skip_blanks();
        if self.at_end() {
            return Ok(());
        }
        if self.src[self.pos] == b'\n' {
            self.advance();
            return Ok(());
        }
        self.error("expected newline")
    }
    fn error<T>(&self, msg: &str) -> R<T> {
        Err(format!("Parse error at line {}: {msg}", self.line))
    }

    fn parse_uint(&mut self) -> R<u32> {
        if !self.peek().is_ascii_digit() {
            return self.error("expected integer");
        }
        let mut v: u32 = 0;
        while self.peek().is_ascii_digit() {
            v = v.wrapping_mul(10).wrapping_add((self.src[self.pos] - b'0') as u32);
            self.pos += 1;
        }
        Ok(v)
    }
    fn parse_hash_int(&mut self) -> R<u32> {
        self.skip_blanks();
        self.expect(b'#')?;
        self.parse_uint()
    }
    fn parse_string(&mut self) -> R<String> {
        self.skip_blanks();
        self.expect(b'"')?;
        let mut out = Vec::new();
        while !self.at_end() && self.src[self.pos] != b'"' {
            if self.src[self.pos] == b'\\' {
                self.pos += 1;
                if self.pos + 1 >= self.src.len() {
                    return self.error("incomplete escape sequence");
                }
                let hex = |c: u8| -> Option<u8> { (c as char).to_digit(16).map(|d| d as u8) };
                let (Some(hi), Some(lo)) = (hex(self.src[self.pos]), hex(self.src[self.pos + 1])) else {
                    return self.error("invalid hex digit in escape");
                };
                self.pos += 2;
                out.push((hi << 4) | lo);
            } else {
                out.push(self.src[self.pos]);
                self.pos += 1;
            }
        }
        self.expect(b'"')?;
        Ok(String::from_utf8_lossy(&out).into_owned())
    }
    fn parse_keyword(&mut self) -> R<String> {
        let start = self.pos;
        while !self.at_end() && (self.src[self.pos].is_ascii_alphanumeric() || self.src[self.pos] == b'_' || self.src[self.pos] == b'/') {
            self.pos += 1;
        }
        if start == self.pos {
            return self.error("expected keyword");
        }
        Ok(String::from_utf8_lossy(&self.src[start..self.pos]).into_owned())
    }

    /// `0`, `1`, `X`, `%id` or `%id+off`.
    fn parse_net_ref(&mut self) -> R<Net> {
        self.skip_blanks();
        if self.matches(b'%') {
            let id = self.parse_uint()?;
            if self.matches(b'+') {
                return Ok(Net(id + self.parse_uint()?));
            }
            return Ok(Net(id));
        }
        match self.peek() {
            b'0' => {
                self.pos += 1;
                Ok(Net::ZERO)
            }
            b'1' => {
                self.pos += 1;
                Ok(Net::ONE)
            }
            b'X' => {
                self.pos += 1;
                Ok(Net::UNDEF)
            }
            _ => self.error("expected net reference"),
        }
    }
    fn parse_const_bits(&mut self) -> R<Bundle> {
        let mut nets = Vec::new();
        loop {
            let n = match self.peek() {
                b'0' => Net::ZERO,
                b'1' => Net::ONE,
                b'X' => Net::UNDEF,
                _ => break,
            };
            self.pos += 1;
            nets.push(n);
        }
        if nets.is_empty() {
            return self.error("expected constant bits");
        }
        nets.reverse();
        Ok(nets)
    }
    fn parse_value_part(&mut self) -> R<Bundle> {
        self.skip_blanks();
        match self.peek() {
            b'%' => {
                self.advance();
                let id = self.parse_uint()?;
                let off = if self.matches(b'+') { self.parse_uint()? } else { 0 };
                if self.matches(b':') {
                    let w = self.parse_uint()?;
                    return Ok(consecutive(Net(id + off), w));
                }
                Ok(vec![Net(id + off)])
            }
            b'0' | b'1' | b'X' => self.parse_const_bits(),
            _ => self.error("expected value part"),
        }
    }
    /// A part, a `[ ... ]` concatenation (most significant part first), or `[]`.
    fn parse_value(&mut self) -> R<Bundle> {
        self.skip_blanks();
        if self.peek() != b'[' {
            return self.parse_value_part();
        }
        self.advance();
        self.skip_blanks();
        if self.peek() == b']' {
            self.advance();
            return Ok(Vec::new());
        }
        let mut parts = Vec::new();
        while self.peek() != b']' {
            parts.push(self.parse_value_part()?);
            self.skip_blanks();
        }
        self.expect(b']')?;
        Ok(parts.into_iter().rev().flatten().collect())
    }
    fn try_keyword_control(&mut self, keyword: &str, out: &mut ControlNet) -> R<()> {
        self.skip_blanks();
        let (saved, saved_line) = (self.pos, self.line);
        let start = self.pos;
        while !self.at_end() && (self.src[self.pos].is_ascii_alphanumeric() || self.src[self.pos] == b'_') {
            self.pos += 1;
        }
        if &self.src[start..self.pos] == keyword.as_bytes() && self.matches(b'=') {
            self.skip_blanks();
            let negated = self.matches(b'!');
            let net = self.parse_net_ref()?;
            *out = ControlNet::with_polarity(net, !negated);
            return Ok(());
        }
        self.pos = saved;
        self.line = saved_line;
        Ok(())
    }

    fn parse_line(&mut self, g: &mut Graph) -> R<()> {
        self.skip_blanks();
        if self.at_end() || self.peek() == b'\n' {
            if !self.at_end() {
                self.advance();
            }
            return Ok(());
        }
        self.expect(b'%')?;
        let id = self.parse_uint()?;
        self.expect(b':')?;
        let width = self.parse_uint()?;
        self.skip_blanks();
        self.expect(b'=')?;
        self.skip_blanks();
        g.pad_table_to(id);
        let keyword = self.parse_keyword()?;
        let bin = |k: &str| -> Option<BinOp> {
            Some(match k {
                "and" => BinOp::And,
                "or" => BinOp::Or,
                "andnot" => BinOp::Andnot,
                "xor" => BinOp::Xor,
                "eq" => BinOp::Eq,
                "ult" => BinOp::ULt,
                "slt" => BinOp::SLt,
                "mul" => BinOp::Mul,
                "udiv" => BinOp::UDiv,
                "umod" => BinOp::UMod,
                "sdiv_trunc" => BinOp::SDivTrunc,
                "sdiv_floor" => BinOp::SDivFloor,
                "smod_trunc" => BinOp::SModTrunc,
                "smod_floor" => BinOp::SModFloor,
                _ => return None,
            })
        };
        let shift = |k: &str| -> Option<ShiftOp> {
            Some(match k {
                "shl" => ShiftOp::Shl,
                "ushr" => ShiftOp::UShr,
                "sshr" => ShiftOp::SShr,
                "xshr" => ShiftOp::XShr,
                _ => return None,
            })
        };
        let kind = match keyword.as_str() {
            "buf" => Kind::Buffer(self.parse_value()?),
            "not" => Kind::Not(self.parse_value()?),
            k if bin(k).is_some() => {
                let a = self.parse_value()?;
                let b = self.parse_value()?;
                Kind::Bin(bin(k).unwrap(), a, b)
            }
            "mux" => {
                let sel = self.parse_net_ref()?;
                let a = self.parse_value()?;
                let b = self.parse_value()?;
                Kind::Mux(sel, a, b)
            }
            "adc" => {
                let a = self.parse_value()?;
                let b = self.parse_value()?;
                let cin = self.parse_net_ref()?;
                Kind::Adc(a, b, cin)
            }
            k if shift(k).is_some() => {
                let a = self.parse_value()?;
                let b = self.parse_value()?;
                let stride = self.parse_hash_int()?;
                Kind::Shift(shift(k).unwrap(), a, b, stride)
            }
            "dff" => {
                let data = self.parse_value()?;
                let (mut clk, mut clr, mut rst, mut en) = (ControlNet::ZERO, ControlNet::ZERO, ControlNet::ZERO, ControlNet::ONE);
                self.try_keyword_control("clk", &mut clk)?;
                self.try_keyword_control("clr", &mut clr)?;
                self.try_keyword_control("rst", &mut rst)?;
                self.try_keyword_control("en", &mut en)?;
                let undef = vec![Trit::Undef; width as usize];
                Kind::Dff(Box::new(Dff {
                    data,
                    clock: clk,
                    clear: clr,
                    reset: rst,
                    enable: en,
                    init_value: undef.clone(),
                    reset_value: undef.clone(),
                    clear_value: undef,
                }))
            }
            "loop_breaker" => Kind::LoopBreaker(self.parse_value()?),
            "input" => Kind::Input(self.parse_string()?, width),
            "dangling" => Kind::Dangling(width),
            "output" => {
                let name = self.parse_string()?;
                Kind::Output(name, self.parse_value()?)
            }
            "name" => {
                let name = self.parse_string()?;
                self.skip_blanks();
                let from = self.parse_uint()?;
                self.skip_blanks();
                let to = self.parse_uint()?;
                self.skip_blanks();
                let (mut tentative, mut is_vector) = (false, false);
                while matches!(self.peek(), b't' | b'v') {
                    let saved = self.pos;
                    match self.parse_keyword()?.as_str() {
                        "tentative" => tentative = true,
                        "vector" => is_vector = true,
                        _ => {
                            self.pos = saved;
                            break;
                        }
                    }
                    self.skip_blanks();
                }
                let value = self.parse_value()?;
                Kind::Name(Box::new(NameInst { name, value, from, to, tentative, is_vector }))
            }
            "target" if self.lib.is_some() => self.parse_target()?,
            "target" | "other" => self.parse_other()?,
            _ => return self.error(&format!("unknown cell keyword: {keyword}")),
        };
        g.add(kind);
        let expected = width.max(1);
        let produced = g.table_size() - id;
        if produced != expected {
            return self.error(&format!(
                "'{keyword}' declared output width {width} but produced {produced} slot{}",
                if produced == 1 { "" } else { "s" }
            ));
        }
        self.expect_newline()
    }

    fn parse_target(&mut self) -> R<Kind> {
        self.skip_blanks();
        let cell_name = self.parse_string()?;
        self.skip_blanks();
        self.expect(b'{')?;
        self.expect_newline()?;
        let Some(cell) = (self.lib.unwrap())(&cell_name) else {
            return self.error(&format!("unknown liberty cell: {cell_name}"));
        };
        let mut inputs: HashMap<String, Bundle> = HashMap::new();
        loop {
            self.skip_blanks();
            if self.peek() == b'}' {
                break;
            }
            if self.peek() == b'%' {
                self.advance();
                self.parse_uint()?;
                self.expect(b':')?;
                self.parse_uint()?;
                self.skip_blanks();
                self.expect(b'=')?;
                self.skip_blanks();
                if self.parse_keyword()? != "output" {
                    return self.error("expected 'output' in target cell block");
                }
                self.skip_blanks();
                self.parse_string()?;
            } else {
                if self.parse_keyword()? != "input" {
                    return self.error("expected 'input' in target cell block");
                }
                self.skip_blanks();
                let name = self.parse_string()?;
                self.skip_blanks();
                self.expect(b'=')?;
                let value = self.parse_value()?;
                inputs.insert(name, value);
            }
            self.expect_newline()?;
        }
        self.expect(b'}')?;
        // The inputs in the library's port order.
        let mut nets = Vec::new();
        for port in &cell.ports {
            if port.pwr_gnd || port.direction != LibDirection::Input {
                continue;
            }
            let Some(v) = inputs.get(&port.name) else {
                return self.error(&format!("missing input port '{}' for cell {cell_name}", port.name));
            };
            nets.extend_from_slice(v);
        }
        Ok(Kind::Target(cell, nets))
    }

    fn parse_other(&mut self) -> R<Kind> {
        self.skip_blanks();
        let cell_type = self.parse_string()?;
        self.skip_blanks();
        self.expect(b'{')?;
        self.expect_newline()?;
        let mut ports = Vec::new();
        loop {
            self.skip_blanks();
            if self.peek() == b'}' {
                break;
            }
            if self.peek() == b'%' {
                self.advance();
                self.parse_uint()?;
                self.expect(b':')?;
                let port_width = self.parse_uint()?;
                self.skip_blanks();
                self.expect(b'=')?;
                self.skip_blanks();
                match self.parse_keyword()?.as_str() {
                    "output" => {
                        self.skip_blanks();
                        let name = self.parse_string()?;
                        ports.push(OtherPort { name, direction: PortDirection::Output, width: port_width, value: Vec::new() });
                    }
                    "io" => {
                        self.skip_blanks();
                        let name = self.parse_string()?;
                        self.skip_blanks();
                        self.expect(b'=')?;
                        let value = self.parse_value()?;
                        ports.push(OtherPort { name, direction: PortDirection::InOut, width: port_width, value });
                    }
                    _ => return self.error("expected 'output' or 'io' in other cell block"),
                }
            } else {
                if self.parse_keyword()? != "input" {
                    return self.error("expected 'input' in other cell block");
                }
                self.skip_blanks();
                let name = self.parse_string()?;
                self.skip_blanks();
                self.expect(b'=')?;
                let value = self.parse_value()?;
                ports.push(OtherPort { name, direction: PortDirection::Input, width: value.len() as u32, value });
            }
            self.expect_newline()?;
        }
        self.expect(b'}')?;
        Ok(Kind::Other(Box::new(other(cell_type, ports))))
    }
}

/// An opaque cell; its output width is the sum of its OUTPUT port widths (inouts are numbered in
/// the text after the outputs before them but do not count).
pub fn other(cell_type: String, ports: Vec<OtherPort>) -> OtherInst {
    let output_width = ports.iter().filter(|p| p.direction == PortDirection::Output).map(|p| p.width).sum();
    OtherInst { cell_type, ports, output_width }
}
