// SPDX-License-Identifier: Apache-2.0
//! Instances: the graph's cells, one per run of table slots.
//!
//! An instance occupies `max(width, 1)` consecutive slots, its output bits. Small single-bit cells
//! (ties, one-bit buffer/not/and/or/andnot/xor, and `dangling` of any width) live INLINE in their
//! slot; everything else lives on the heap behind per-slot references. The split does not move ids,
//! but it decides how a replacement is made (an inline cell is overwritten in place by a buffer, a
//! heap cell is relocated and a buffer left behind), so it is recorded per instance.

use std::sync::Arc;

use super::net::{Bundle, Const, ControlNet, Net};

/// Two-operand operations. The first four are bitwise (sliceable, output as wide as `a`).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum BinOp {
    And,
    Or,
    Andnot,
    Xor,
    Eq,
    ULt,
    SLt,
    Mul,
    UDiv,
    UMod,
    SDivTrunc,
    SDivFloor,
    SModTrunc,
    SModFloor,
}

impl BinOp {
    pub fn keyword(self) -> &'static str {
        match self {
            BinOp::And => "and",
            BinOp::Or => "or",
            BinOp::Andnot => "andnot",
            BinOp::Xor => "xor",
            BinOp::Eq => "eq",
            BinOp::ULt => "ult",
            BinOp::SLt => "slt",
            BinOp::Mul => "mul",
            BinOp::UDiv => "udiv",
            BinOp::UMod => "umod",
            BinOp::SDivTrunc => "sdiv_trunc",
            BinOp::SDivFloor => "sdiv_floor",
            BinOp::SModTrunc => "smod_trunc",
            BinOp::SModFloor => "smod_floor",
        }
    }
    pub fn is_bitwise(self) -> bool {
        matches!(self, BinOp::And | BinOp::Or | BinOp::Andnot | BinOp::Xor)
    }
    /// A comparison: one output bit.
    pub fn is_compare(self) -> bool {
        matches!(self, BinOp::Eq | BinOp::ULt | BinOp::SLt)
    }
}

/// Shifts by `b` times `stride` bits.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum ShiftOp {
    Shl,
    UShr,
    SShr,
    XShr,
}

impl ShiftOp {
    pub fn keyword(self) -> &'static str {
        match self {
            ShiftOp::Shl => "shl",
            ShiftOp::UShr => "ushr",
            ShiftOp::SShr => "sshr",
            ShiftOp::XShr => "xshr",
        }
    }
}

#[derive(Clone, Debug)]
pub struct Dff {
    pub data: Bundle,
    pub clock: ControlNet,
    pub clear: ControlNet,
    pub reset: ControlNet,
    pub enable: ControlNet,
    pub init_value: Const,
    pub reset_value: Const,
    pub clear_value: Const,
}

#[derive(Clone, Debug)]
pub struct NameInst {
    pub name: String,
    pub value: Bundle,
    pub from: u32,
    pub to: u32,
    pub tentative: bool,
    pub is_vector: bool,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PortDirection {
    Input,
    Output,
    InOut,
}

#[derive(Clone, Debug)]
pub struct OtherPort {
    pub name: String,
    pub direction: PortDirection,
    pub width: u32,
    /// For inputs and inouts the driving signal; empty for outputs.
    pub value: Bundle,
}

#[derive(Clone, Debug)]
pub struct OtherInst {
    pub cell_type: String,
    pub ports: Vec<OtherPort>,
    pub output_width: u32,
}

/// A library cell's direction as the mapper sees it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LibDirection {
    Input,
    Output,
    /// `inout`: an input and an output to the importer, neither to the mapper.
    Bidirect,
    /// Tristate, internal, unknown, power or ground.
    Other,
}

#[derive(Clone, Debug)]
pub struct LibPort {
    pub name: String,
    pub direction: LibDirection,
    /// Bits: a bus's width, a bundle's member count, otherwise 1.
    pub size: u32,
    /// A bus (a bundle is not one: its blackbox port is one bit wide).
    pub is_bus: bool,
    pub pwr_gnd: bool,
    /// Its `function` as written (an output's; a bus's is not kept).
    pub function: Option<String>,
}

/// A cell's one `ff` or `latch` group, as written.
#[derive(Clone, Debug)]
pub struct LibSeq {
    pub latch: bool,
    /// The state variable the group's outputs read (`ff (IQ, IQN)`: `IQ`).
    pub iq: String,
    /// `clocked_on` (a latch: `enable`), `next_state` (a latch: `data_in`), `clear`, `preset`, as
    /// written.
    pub clocked_on: Option<String>,
    pub next_state: Option<String>,
    pub clear: Option<String>,
    pub preset: Option<String>,
}

/// What the IR needs of a library cell, ports in the library's declaration order.
#[derive(Clone, Debug)]
pub struct LibCell {
    pub name: String,
    pub area: f32,
    pub is_macro: bool,
    pub is_sequential: bool,
    pub ports: Vec<LibPort>,
    /// `dont_use : true`.
    pub dont_use: bool,
    /// Its one `ff` / `latch` group, when it has exactly one (and no bank or `statetable`).
    pub seq: Option<LibSeq>,
}

#[derive(Clone, Debug)]
pub enum Kind {
    TieHigh,
    TieLow,
    TieX,
    Buffer(Bundle),
    Not(Bundle),
    Bin(BinOp, Bundle, Bundle),
    Mux(Net, Bundle, Bundle),
    Adc(Bundle, Bundle, Net),
    Shift(ShiftOp, Bundle, Bundle, u32),
    Dff(Box<Dff>),
    LoopBreaker(Bundle),
    Input(String, u32),
    Dangling(u32),
    Output(String, Bundle),
    Name(Box<NameInst>),
    Target(Arc<LibCell>, Bundle),
    Other(Box<OtherInst>),
}

/// Where an input net sits inside an instance, in visit order.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Pin {
    Sel,
    A(u32),
    B(u32),
    Cin,
    /// Dff controls: 0 clock, 1 clear, 2 reset, 3 enable.
    Ctl(u8),
    /// The single bundle of buffer / not / loop breaker / output / name / target.
    V(u32),
    /// An Other cell's port `p`, bit `i`.
    Port(u32, u32),
}

impl Kind {
    pub fn keyword(&self) -> &'static str {
        match self {
            Kind::TieHigh | Kind::TieLow | Kind::TieX => "?",
            Kind::Buffer(_) => "buf",
            Kind::Not(_) => "not",
            Kind::Bin(op, ..) => op.keyword(),
            Kind::Mux(..) => "mux",
            Kind::Adc(..) => "adc",
            Kind::Shift(op, ..) => op.keyword(),
            Kind::Dff(_) => "dff",
            Kind::LoopBreaker(_) => "loop_breaker",
            Kind::Input(..) => "input",
            Kind::Dangling(_) => "dangling",
            Kind::Output(..) => "output",
            Kind::Name(_) => "name",
            Kind::Target(..) => "target",
            Kind::Other(_) => "other",
        }
    }

    pub fn output_width(&self) -> u32 {
        match self {
            Kind::TieHigh | Kind::TieLow | Kind::TieX => 1,
            Kind::Buffer(a) | Kind::Not(a) | Kind::LoopBreaker(a) => a.len() as u32,
            Kind::Bin(op, a, _) => {
                if op.is_compare() {
                    1
                } else {
                    a.len() as u32
                }
            }
            Kind::Mux(_, a, _) => a.len() as u32,
            Kind::Adc(a, _, _) => a.len() as u32 + 1,
            Kind::Shift(_, a, _, _) => a.len() as u32,
            Kind::Dff(d) => d.data.len() as u32,
            Kind::Input(_, w) | Kind::Dangling(w) => *w,
            Kind::Output(..) | Kind::Name(_) => 0,
            Kind::Target(cell, _) => cell.ports.iter().filter(|p| p.direction == LibDirection::Output).map(|p| p.size).sum(),
            Kind::Other(o) => o.output_width,
        }
    }

    /// The single-bit form fits a table slot (see the module note). A one-bit operation built
    /// from wide operands, or a buffer made to forward a relocated cell, is a heap cell.
    pub fn fits_inline(&self) -> bool {
        match self {
            Kind::TieHigh | Kind::TieLow | Kind::TieX | Kind::Dangling(_) => true,
            Kind::Buffer(a) | Kind::Not(a) => a.len() == 1,
            Kind::Bin(op, a, b) => op.is_bitwise() && a.len() == 1 && b.len() == 1,
            _ => false,
        }
    }

    /// Observable: ports, names that are not tentative, macros.
    pub fn has_effects(&self) -> bool {
        match self {
            Kind::Output(..) | Kind::Other(_) => true,
            Kind::Target(cell, _) => cell.is_macro,
            Kind::Name(n) => !n.tentative,
            _ => false,
        }
    }

    pub fn has_state(&self) -> bool {
        match self {
            Kind::Dff(_) | Kind::Other(_) => true,
            Kind::Target(cell, _) => cell.is_sequential,
            _ => false,
        }
    }

    /// A bitwise cell: output bit `i` depends on input bit `i` (and a mux's select) only.
    pub fn is_sliceable(&self) -> bool {
        match self {
            Kind::Buffer(_) | Kind::Not(_) | Kind::Mux(..) | Kind::LoopBreaker(_) | Kind::Dangling(_) => true,
            Kind::Bin(op, ..) => op.is_bitwise(),
            _ => false,
        }
    }

    pub fn is_mapped(&self) -> bool {
        matches!(self, Kind::Target(..) | Kind::Input(..) | Kind::Output(..) | Kind::Other(_) | Kind::LoopBreaker(_))
    }

    pub fn is_tie(&self) -> bool {
        matches!(self, Kind::TieHigh | Kind::TieLow | Kind::TieX)
    }

    /// Every input pin, in visit order.
    pub fn pins(&self) -> Vec<Pin> {
        let mut v = Vec::new();
        let n = |b: &Bundle| 0..b.len() as u32;
        match self {
            Kind::TieHigh | Kind::TieLow | Kind::TieX | Kind::Input(..) | Kind::Dangling(_) => {}
            Kind::Buffer(a) | Kind::Not(a) | Kind::LoopBreaker(a) | Kind::Output(_, a) | Kind::Target(_, a) => v.extend(n(a).map(Pin::V)),
            Kind::Name(nm) => v.extend(n(&nm.value).map(Pin::V)),
            Kind::Bin(_, a, b) | Kind::Shift(_, a, b, _) => {
                v.extend(n(a).map(Pin::A));
                v.extend(n(b).map(Pin::B));
            }
            Kind::Mux(_, a, b) => {
                v.push(Pin::Sel);
                v.extend(n(a).map(Pin::A));
                v.extend(n(b).map(Pin::B));
            }
            Kind::Adc(a, b, _) => {
                v.extend(n(a).map(Pin::A));
                v.extend(n(b).map(Pin::B));
                v.push(Pin::Cin);
            }
            Kind::Dff(d) => {
                v.extend(n(&d.data).map(Pin::V));
                v.extend((0..4).map(Pin::Ctl));
            }
            Kind::Other(o) => {
                for (p, port) in o.ports.iter().enumerate() {
                    if port.direction != PortDirection::Output {
                        v.extend(n(&port.value).map(|i| Pin::Port(p as u32, i)));
                    }
                }
            }
        }
        v
    }

    /// The input pins output bit `i` depends on: the bit-`i` operands of a bitwise cell, all
    /// inputs otherwise.
    pub fn slice_pins(&self, i: u32) -> Vec<Pin> {
        match self {
            Kind::Buffer(_) | Kind::Not(_) | Kind::LoopBreaker(_) => vec![Pin::V(i)],
            Kind::Bin(op, ..) if op.is_bitwise() => vec![Pin::A(i), Pin::B(i)],
            Kind::Mux(..) => vec![Pin::Sel, Pin::A(i), Pin::B(i)],
            _ => self.pins(),
        }
    }

    pub fn get(&self, pin: Pin) -> Net {
        match (self, pin) {
            (Kind::Buffer(a) | Kind::Not(a) | Kind::LoopBreaker(a) | Kind::Output(_, a) | Kind::Target(_, a), Pin::V(i)) => a[i as usize],
            (Kind::Name(nm), Pin::V(i)) => nm.value[i as usize],
            (Kind::Dff(d), Pin::V(i)) => d.data[i as usize],
            (Kind::Dff(d), Pin::Ctl(c)) => [d.clock, d.clear, d.reset, d.enable][c as usize].net,
            (Kind::Bin(_, a, _) | Kind::Shift(_, a, _, _) | Kind::Mux(_, a, _) | Kind::Adc(a, _, _), Pin::A(i)) => a[i as usize],
            (Kind::Bin(_, _, b) | Kind::Shift(_, _, b, _) | Kind::Mux(_, _, b) | Kind::Adc(_, b, _), Pin::B(i)) => b[i as usize],
            (Kind::Mux(s, ..), Pin::Sel) => *s,
            (Kind::Adc(_, _, c), Pin::Cin) => *c,
            (Kind::Other(o), Pin::Port(p, i)) => o.ports[p as usize].value[i as usize],
            _ => panic!("pin {pin:?} on {}", self.keyword()),
        }
    }

    pub fn set(&mut self, pin: Pin, net: Net) {
        let keyword = self.keyword();
        let slot: &mut Net = match (self, pin) {
            (Kind::Buffer(a) | Kind::Not(a) | Kind::LoopBreaker(a) | Kind::Output(_, a) | Kind::Target(_, a), Pin::V(i)) => &mut a[i as usize],
            (Kind::Name(nm), Pin::V(i)) => &mut nm.value[i as usize],
            (Kind::Dff(d), Pin::V(i)) => &mut d.data[i as usize],
            (Kind::Dff(d), Pin::Ctl(c)) => match c {
                0 => &mut d.clock.net,
                1 => &mut d.clear.net,
                2 => &mut d.reset.net,
                _ => &mut d.enable.net,
            },
            (Kind::Bin(_, a, _) | Kind::Shift(_, a, _, _) | Kind::Mux(_, a, _) | Kind::Adc(a, _, _), Pin::A(i)) => &mut a[i as usize],
            (Kind::Bin(_, _, b) | Kind::Shift(_, _, b, _) | Kind::Mux(_, _, b) | Kind::Adc(_, b, _), Pin::B(i)) => &mut b[i as usize],
            (Kind::Mux(s, ..), Pin::Sel) => s,
            (Kind::Adc(_, _, c), Pin::Cin) => c,
            (Kind::Other(o), Pin::Port(p, i)) => &mut o.ports[p as usize].value[i as usize],
            _ => panic!("pin {pin:?} on {keyword}"),
        };
        *slot = net;
    }

    /// Every input net, in visit order.
    pub fn inputs(&self) -> Vec<Net> {
        self.pins().into_iter().map(|p| self.get(p)).collect()
    }

    pub fn map_inputs(&mut self, mut f: impl FnMut(Net) -> Net) {
        for p in self.pins() {
            let n = self.get(p);
            self.set(p, f(n));
        }
    }
}

/// One cell of the graph.
#[derive(Clone, Debug)]
pub struct Instance {
    pub kind: Kind,
    /// The first slot of its output range.
    pub base: u32,
    pub inline: bool,
    pub metadata: u32,
}

impl Instance {
    pub fn output_width(&self) -> u32 {
        self.kind.output_width()
    }
    /// Slots taken: at least one, so a zero-width cell still has an id.
    pub fn slots(&self) -> u32 {
        self.output_width().max(1)
    }
}
