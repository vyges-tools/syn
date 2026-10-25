// SPDX-License-Identifier: Apache-2.0
//! The graph builder the SystemVerilog frontend drives: one method per node kind it asks for.
//!
//! Values are bundles of nets, least significant first. Operators with only constant operands are
//! folded here instead of built; the rest become graph cells. Signals are created as buffers of
//! undefined bits (placeholders) and wired to their drivers later with `connect`.

use crate::ir::constant as k;
use crate::ir::instance::{Dff, NameInst, OtherPort, PortDirection};
use crate::ir::net::{is_const, Bundle, ControlNet, Net, Trit};
use crate::ir::parse::other;
use crate::ir::{BinOp, Graph, Kind, ShiftOp};

/// SystemVerilog unary operators.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum UnaryOp {
    Plus,
    Minus,
    BitwiseNot,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
    BitwiseNand,
    BitwiseNor,
    BitwiseXnor,
    LogicalNot,
    /// Anything else the frontend may pass (increments and the like).
    Other,
}

/// SystemVerilog binary operators.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BinaryOp {
    Add,
    Subtract,
    Multiply,
    Divide,
    Mod,
    BinaryAnd,
    BinaryOr,
    BinaryXor,
    BinaryXnor,
    Equality,
    Inequality,
    CaseEquality,
    CaseInequality,
    GreaterThanEqual,
    GreaterThan,
    LessThanEqual,
    LessThan,
    LogicalAnd,
    LogicalOr,
    LogicalShiftLeft,
    LogicalShiftRight,
    ArithmeticShiftLeft,
    ArithmeticShiftRight,
    Other,
}

/// A failure the elaboration stops on: its message id and text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ElabError {
    pub code: u32,
    pub message: String,
}

fn err<T>(code: u32, message: &str) -> Result<T, ElabError> {
    Err(ElabError { code, message: message.to_string() })
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PortDir {
    Input,
    Output,
    InOut,
}

pub struct PortConnection {
    pub name: String,
    pub direction: PortDir,
    pub value: Bundle,
}

pub type R = Result<Bundle, ElabError>;

fn to_const(b: &[Net]) -> Vec<Trit> {
    b.iter().map(|n| n.const_trit()).collect()
}

fn from_const(c: &[Trit]) -> Bundle {
    c.iter().map(|&t| Net::from_trit(t)).collect()
}

/// A constant cut or padded to `w` bits: sign-padded (with the top bit, even an undefined one)
/// when signed, zero-padded otherwise.
fn extend_const(c: &[Trit], signed: bool, w: u64) -> Vec<Trit> {
    let w = w as usize;
    if c.len() >= w {
        return c[..w].to_vec();
    }
    let fill = if signed && !c.is_empty() { *c.last().unwrap() } else { Trit::Zero };
    let mut v = c.to_vec();
    v.resize(w, fill);
    v
}

fn zero_extend(b: &[Net], w: u64) -> Bundle {
    assert!(w as usize >= b.len(), "zero extension narrows");
    let mut v = b.to_vec();
    v.resize(w as usize, Net::ZERO);
    v
}

fn sign_extend(b: &[Net], w: u64) -> Bundle {
    assert!(w as usize >= b.len() && !b.is_empty(), "sign extension narrows or of an empty value");
    let mut v = b.to_vec();
    v.resize(w as usize, *b.last().unwrap());
    v
}

fn extend_to(b: &[Net], signed: bool, w: u64) -> Bundle {
    if signed {
        sign_extend(b, w)
    } else {
        zero_extend(b, w)
    }
}

/// Widen (never narrow) to `w`.
fn widen(v: &mut Bundle, signed: bool, w: u64) {
    if (v.len() as u64) < w {
        *v = extend_to(v, signed, w);
    }
}

fn fold_or(c: &[Trit]) -> Trit {
    c[1..].iter().fold(c[0], |acc, &t| k::or(acc, t))
}

pub struct Backend {
    pub graph: Graph,
}

impl Default for Backend {
    fn default() -> Self {
        Self::new()
    }
}

impl Backend {
    pub fn new() -> Self {
        Backend { graph: Graph::new() }
    }

    fn add(&mut self, kind: Kind) -> Bundle {
        self.graph.add(kind)
    }

    fn not(&mut self, a: Bundle) -> Bundle {
        self.add(Kind::Not(a))
    }

    fn bin(&mut self, op: BinOp, a: Bundle, b: Bundle) -> Bundle {
        self.add(Kind::Bin(op, a, b))
    }

    pub fn unop(&mut self, op: UnaryOp, a: Bundle, a_signed: bool, y_width: u64) -> R {
        use UnaryOp::*;
        if y_width == 0 {
            return Ok(Vec::new());
        }
        if is_const(&a) {
            let ac = to_const(&a);
            let ext = extend_const(&ac, a_signed, y_width);
            match op {
                Plus => return Ok(from_const(&ext)),
                Minus => {
                    let n = k::adc(&k::c_not(&ext), &vec![Trit::Zero; y_width as usize], Trit::One);
                    return Ok(from_const(&n[..y_width as usize]));
                }
                BitwiseNot => return Ok(from_const(&k::c_not(&ext))),
                BitwiseAnd | BitwiseOr | BitwiseXor | BitwiseNand | BitwiseNor | BitwiseXnor => {
                    if ac.is_empty() {
                        return Ok(from_const(&vec![Trit::Undef; y_width as usize]));
                    }
                    let mut r = ac[0];
                    for &t in &ac[1..] {
                        r = match op {
                            BitwiseAnd | BitwiseNand => k::and(r, t),
                            BitwiseOr | BitwiseNor => k::or(r, t),
                            _ => k::xor(r, t),
                        };
                    }
                    if matches!(op, BitwiseNand | BitwiseNor | BitwiseXnor) {
                        r = k::not(r);
                    }
                    return Ok(from_const(&extend_const(&[r], false, y_width)));
                }
                LogicalNot => {
                    if ac.is_empty() {
                        return Ok(from_const(&extend_const(&[Trit::One], false, y_width)));
                    }
                    return Ok(from_const(&extend_const(&[k::not(fold_or(&ac))], false, y_width)));
                }
                Other => {}
            }
        }
        match op {
            // Identity; widened when the result is wider, never cut.
            Plus => {
                if y_width > a.len() as u64 {
                    return Ok(extend_to(&a, a_signed, y_width));
                }
                Ok(a)
            }
            // Two's complement: ~a + 1 over the widened operand.
            Minus => {
                let ext = extend_to(&a, a_signed, y_width);
                let inv = self.not(ext);
                let sum = self.add(Kind::Adc(inv, vec![Net::ZERO; y_width as usize], Net::ONE));
                Ok(sum[..y_width as usize].to_vec())
            }
            BitwiseNot => {
                let ext = extend_to(&a, a_signed, y_width);
                Ok(self.not(ext))
            }
            // Reductions: a chain of two-input cells, least significant bit first.
            BitwiseAnd | BitwiseOr | BitwiseXor | BitwiseNand | BitwiseNor | BitwiseXnor => {
                if a.is_empty() {
                    return Ok(vec![Net::UNDEF]);
                }
                let gate = match op {
                    BitwiseAnd | BitwiseNand => BinOp::And,
                    BitwiseOr | BitwiseNor => BinOp::Or,
                    _ => BinOp::Xor,
                };
                let mut r = a[0];
                for &bit in &a[1..] {
                    r = self.bin(gate, vec![r], vec![bit])[0];
                }
                if matches!(op, BitwiseNand | BitwiseNor | BitwiseXnor) {
                    r = self.not(vec![r])[0];
                }
                Ok(zero_extend(&[r], y_width))
            }
            LogicalNot => {
                if a.is_empty() {
                    // Vacuously true, cut or padded to the result.
                    let mut v = vec![Net::ONE];
                    v.resize(y_width as usize, Net::ZERO);
                    return Ok(v);
                }
                let mut any = a[0];
                for &bit in &a[1..] {
                    any = self.bin(BinOp::Or, vec![any], vec![bit])[0];
                }
                let r = self.not(vec![any])[0];
                Ok(zero_extend(&[r], y_width))
            }
            Other => err(70, "Unsupported unary operator"),
        }
    }

    pub fn biop(&mut self, op: BinaryOp, a: Bundle, b: Bundle, a_signed: bool, b_signed: bool, y_width: u64) -> R {
        use BinaryOp::*;
        if is_const(&a) && is_const(&b) {
            if let Some(v) = Self::fold(op, &to_const(&a), &to_const(&b), a_signed, b_signed, y_width) {
                return Ok(from_const(&v));
            }
        }
        let (mut a, mut b) = (a, b);
        let both_signed = a_signed && b_signed;
        let y = y_width;
        let cmp_w = |a: &Bundle, b: &Bundle| a.len().max(b.len()) as u64;
        let r = match op {
            BinaryAnd | BinaryOr | BinaryXor | BinaryXnor => {
                widen(&mut a, a_signed, y);
                widen(&mut b, b_signed, y);
                match op {
                    BinaryAnd => self.bin(BinOp::And, a, b),
                    BinaryOr => self.bin(BinOp::Or, a, b),
                    BinaryXor => self.bin(BinOp::Xor, a, b),
                    _ => {
                        let x = self.bin(BinOp::Xor, a, b);
                        self.not(x)
                    }
                }
            }
            Add => {
                widen(&mut a, a_signed, y);
                widen(&mut b, b_signed, y);
                self.add(Kind::Adc(a, b, Net::ZERO))[..y as usize].to_vec()
            }
            // a + ~b + 1
            Subtract => {
                widen(&mut a, a_signed, y);
                widen(&mut b, b_signed, y);
                let nb = self.not(b);
                self.add(Kind::Adc(a, nb, Net::ONE))[..y as usize].to_vec()
            }
            Multiply => {
                let w = (a.len() as u64).max(b.len() as u64).max(y);
                widen(&mut a, a_signed, w);
                widen(&mut b, b_signed, w);
                let mut r = self.bin(BinOp::Mul, a, b);
                r.truncate(y as usize);
                r
            }
            Divide | Mod => {
                widen(&mut a, a_signed, y);
                widen(&mut b, b_signed, y);
                let signed = a_signed || b_signed;
                let cell = match (op, signed) {
                    (Divide, true) => BinOp::SDivTrunc,
                    (Divide, false) => BinOp::UDiv,
                    (_, true) => BinOp::SModTrunc,
                    (_, false) => BinOp::UMod,
                };
                self.bin(cell, a, b)
            }
            Equality | CaseEquality | Inequality | CaseInequality => {
                let w = cmp_w(&a, &b);
                widen(&mut a, a_signed, w);
                widen(&mut b, b_signed, w);
                let mut r = self.bin(BinOp::Eq, a, b);
                if matches!(op, Inequality | CaseInequality) {
                    r = self.not(r);
                }
                zero_extend(&r, y)
            }
            // a < b; a <= b is !(b < a); a > b is b < a; a >= b is !(a < b).
            LessThan | LessThanEqual | GreaterThan | GreaterThanEqual => {
                let w = cmp_w(&a, &b);
                widen(&mut a, a_signed, w);
                widen(&mut b, b_signed, w);
                let lt = if both_signed { BinOp::SLt } else { BinOp::ULt };
                let r = match op {
                    LessThan => self.bin(lt, a, b),
                    LessThanEqual => {
                        let gt = self.bin(lt, b, a);
                        self.not(gt)
                    }
                    GreaterThan => self.bin(lt, b, a),
                    _ => {
                        let l = self.bin(lt, a, b);
                        self.not(l)
                    }
                };
                zero_extend(&r, y)
            }
            // Each side reduced to a bool by an OR chain (the left first), then combined.
            LogicalAnd | LogicalOr => {
                let mut a_bool = a[0];
                for &bit in &a[1..] {
                    a_bool = self.bin(BinOp::Or, vec![a_bool], vec![bit])[0];
                }
                let mut b_bool = b[0];
                for &bit in &b[1..] {
                    b_bool = self.bin(BinOp::Or, vec![b_bool], vec![bit])[0];
                }
                let gate = if op == LogicalAnd { BinOp::And } else { BinOp::Or };
                let r = self.bin(gate, vec![a_bool], vec![b_bool]);
                zero_extend(&r, y)
            }
            LogicalShiftLeft | LogicalShiftRight | ArithmeticShiftLeft | ArithmeticShiftRight => {
                widen(&mut a, a_signed, y);
                let s = match op {
                    LogicalShiftLeft | ArithmeticShiftLeft => ShiftOp::Shl,
                    ArithmeticShiftRight if a_signed => ShiftOp::SShr,
                    _ => ShiftOp::UShr,
                };
                self.add(Kind::Shift(s, a, b, 1))
            }
            Other => return err(71, "Unsupported binary operator"),
        };
        Ok(r)
    }

    /// Both operands constant: the folded result, or none for an operator not folded here.
    fn fold(op: BinaryOp, ac: &[Trit], bc: &[Trit], a_signed: bool, b_signed: bool, y: u64) -> Option<Vec<Trit>> {
        use BinaryOp::*;
        let ext = extend_const;
        let w = ac.len().max(bc.len()) as u64;
        let both = a_signed && b_signed;
        let bit = |t: Trit| extend_const(&[t], false, y);
        let lt = |x: &[Trit], z: &[Trit]| if both { k::slt(x, z) } else { k::ult(x, z) };
        Some(match op {
            BinaryAnd => k::c_and(&ext(ac, a_signed, y), &ext(bc, b_signed, y)),
            BinaryOr => k::c_or(&ext(ac, a_signed, y), &ext(bc, b_signed, y)),
            BinaryXor => k::c_xor(&ext(ac, a_signed, y), &ext(bc, b_signed, y)),
            BinaryXnor => k::c_not(&k::c_xor(&ext(ac, a_signed, y), &ext(bc, b_signed, y))),
            Add => k::adc(&ext(ac, a_signed, y), &ext(bc, b_signed, y), Trit::Zero)[..y as usize].to_vec(),
            Subtract => k::adc(&ext(ac, a_signed, y), &k::c_not(&ext(bc, b_signed, y)), Trit::One)[..y as usize].to_vec(),
            Multiply => k::mul(&ext(ac, a_signed, y), &ext(bc, b_signed, y)),
            Equality | CaseEquality => bit(k::eq(&ext(ac, a_signed, w), &ext(bc, b_signed, w))),
            Inequality | CaseInequality => bit(k::not(k::eq(&ext(ac, a_signed, w), &ext(bc, b_signed, w)))),
            LessThan => bit(lt(&ext(ac, a_signed, w), &ext(bc, b_signed, w))),
            LessThanEqual => bit(k::not(lt(&ext(bc, b_signed, w), &ext(ac, a_signed, w)))),
            GreaterThan => bit(lt(&ext(bc, b_signed, w), &ext(ac, a_signed, w))),
            GreaterThanEqual => bit(k::not(lt(&ext(ac, a_signed, w), &ext(bc, b_signed, w)))),
            LogicalAnd => bit(k::and(fold_or(ac), fold_or(bc))),
            LogicalOr => bit(k::or(fold_or(ac), fold_or(bc))),
            LogicalShiftLeft | ArithmeticShiftLeft => k::shl(&ext(ac, a_signed, y), bc, 1),
            LogicalShiftRight => k::ushr(&ext(ac, a_signed, y), bc, 1),
            ArithmeticShiftRight if a_signed => k::sshr(&ext(ac, a_signed, y), bc, 1),
            ArithmeticShiftRight => k::ushr(&ext(ac, a_signed, y), bc, 1),
            _ => return None,
        })
    }

    /// The frontend selects `a` on 0; the cell selects its first operand on 1: swapped.
    pub fn mux(&mut self, a: Bundle, b: Bundle, s: Net) -> R {
        Ok(self.add(Kind::Mux(s, b, a)))
    }

    fn shift_right(&mut self, op: ShiftOp, a: Bundle, s: Bundle, width: u64) -> R {
        let w = (width as usize).max(a.len()) as u64;
        let a = zero_extend(&a, w);
        let r = self.add(Kind::Shift(op, a, s, 1));
        Ok(r[..width as usize].to_vec())
    }

    pub fn shift(&mut self, a: Bundle, s: Bundle, _s_signed: bool, width: u64) -> R {
        self.shift_right(ShiftOp::UShr, a, s, width)
    }

    pub fn shiftx(&mut self, a: Bundle, s: Bundle, _s_signed: bool, width: u64) -> R {
        self.shift_right(ShiftOp::XShr, a, s, width)
    }

    /// `a` placed in slot `s` of `2^|s|` slots: a left shift by `s` times `|a|`.
    pub fn demux(&mut self, a: Bundle, s: Bundle) -> R {
        let out_width = (a.len() as u64) << s.len();
        let stride = a.len() as u32;
        let a = zero_extend(&a, out_width);
        Ok(self.add(Kind::Shift(ShiftOp::Shl, a, s, stride)))
    }

    /// A mux per run of bits sharing one select net.
    pub fn bwmux(&mut self, a: Bundle, b: Bundle, s: Bundle) -> R {
        let mut out = Vec::with_capacity(a.len());
        let mut base = 0;
        while base < a.len() {
            let mut width = 1;
            while base + width < s.len() && s[base + width] == s[base] {
                width += 1;
            }
            let m = self.mux(a[base..base + width].to_vec(), b[base..base + width].to_vec(), s[base])?;
            out.extend(m);
            base += width;
        }
        Ok(out)
    }

    /// Slot `s` of `a` cut into `2^|s|` slots: a right shift by `s` times the slot width.
    pub fn bmux(&mut self, a: Bundle, s: Bundle) -> R {
        let width = a.len() >> s.len();
        let r = self.add(Kind::Shift(ShiftOp::UShr, a, s, width as u32));
        Ok(r[..width].to_vec())
    }

    /// A buffer of undefined bits, wired later; named when the name is public.
    pub fn add_placeholder_signal(&mut self, width: u64, name: &str, public_name: bool) -> R {
        let sig = self.add(Kind::Buffer(vec![Net::UNDEF; width as usize]));
        if public_name && !name.is_empty() {
            let w = sig.len() as u32;
            self.add(Kind::Name(Box::new(NameInst { name: name.to_string(), value: sig.clone(), from: 0, to: w, tentative: false, is_vector: w > 1 })));
        }
        Ok(sig)
    }

    pub fn add_input(&mut self, name: &str, signal: Bundle) -> Result<(), ElabError> {
        let input = self.add(Kind::Input(name.to_string(), signal.len() as u32));
        self.connect(&signal, &input)
    }

    pub fn add_output(&mut self, name: &str, signal: Bundle) -> Result<(), ElabError> {
        self.add(Kind::Output(name.to_string(), signal));
        Ok(())
    }

    /// An opaque cell; its output ports' placeholders are wired to its outputs in port order.
    pub fn add_instance(&mut self, cell_type: &str, ports: Vec<PortConnection>) -> Result<(), ElabError> {
        let cell_ports = ports
            .iter()
            .map(|pc| {
                let width = pc.value.len() as u32;
                let (direction, value) = match pc.direction {
                    PortDir::Input => (PortDirection::Input, pc.value.clone()),
                    PortDir::Output => (PortDirection::Output, Vec::new()),
                    PortDir::InOut => (PortDirection::InOut, pc.value.clone()),
                };
                OtherPort { name: pc.name.clone(), direction, width, value }
            })
            .collect();
        let outputs = self.add(Kind::Other(Box::new(other(cell_type.to_string(), cell_ports))));
        let mut off = 0;
        for pc in &ports {
            if pc.direction == PortDir::Output {
                let w = pc.value.len();
                self.connect(&pc.value, &outputs[off..off + w])?;
                off += w;
            }
        }
        Ok(())
    }

    /// Point each placeholder bit's buffer at its driver.
    pub fn connect(&mut self, target: &[Net], source: &[Net]) -> Result<(), ElabError> {
        for (i, &t) in target.iter().enumerate() {
            let (id, offset) = self.graph.resolve(t);
            let inst = self.graph.inst_mut(id);
            assert!(matches!(inst.kind, Kind::Buffer(_)), "connect to a non-placeholder");
            inst.kind.set(crate::ir::instance::Pin::V(offset), source[i]);
        }
        Ok(())
    }

    fn dff(&mut self, d: &[Net], clock: ControlNet, clear: ControlNet, enable: ControlNet, clear_value: Vec<Trit>, q: &[Net]) -> Result<(), ElabError> {
        let w = d.len();
        let out = self.add(Kind::Dff(Box::new(Dff {
            data: d.to_vec(),
            clock,
            clear,
            reset: ControlNet::ZERO,
            enable,
            init_value: vec![Trit::Undef; w],
            reset_value: vec![Trit::Undef; w],
            clear_value,
        })));
        self.connect(q, &out)
    }

    pub fn add_dff(&mut self, clk: &[Net], d: &[Net], q: &[Net], clk_polarity: bool) -> Result<(), ElabError> {
        let clock = ControlNet::with_polarity(as_net(clk), clk_polarity);
        self.dff(d, clock, ControlNet::ZERO, ControlNet::ONE, vec![Trit::Undef; d.len()], q)
    }

    pub fn add_dffe(&mut self, clk: &[Net], en: &[Net], d: &[Net], q: &[Net], clk_polarity: bool, en_polarity: bool) -> Result<(), ElabError> {
        let clock = ControlNet::with_polarity(as_net(clk), clk_polarity);
        let enable = ControlNet::with_polarity(as_net(en), en_polarity);
        self.dff(d, clock, ControlNet::ZERO, enable, vec![Trit::Undef; d.len()], q)
    }

    /// An asynchronous load of a constant is a clear to that constant.
    #[allow(clippy::too_many_arguments)]
    pub fn add_aldff(&mut self, clk: &[Net], aload: &[Net], d: &[Net], q: &[Net], ad: &[Net], clk_polarity: bool, aload_polarity: bool) -> Result<(), ElabError> {
        let clock = ControlNet::with_polarity(as_net(clk), clk_polarity);
        let clear = ControlNet::with_polarity(as_net(aload), aload_polarity);
        if !is_const(ad) {
            return err(91, "Flops with non-constant asynchronous load unsupported");
        }
        self.dff(d, clock, clear, ControlNet::ONE, to_const(ad), q)
    }

    pub fn add_dual_edge_aldff(&mut self) -> Result<(), ElabError> {
        err(72, "Flops with a dual-edge asynchronous load are unsupported")
    }
}

fn as_net(v: &[Net]) -> Net {
    assert_eq!(v.len(), 1, "a one-bit value");
    v[0]
}
