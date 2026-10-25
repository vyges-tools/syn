// SPDX-License-Identifier: Apache-2.0
//! Constant folding: combinational cells with constant (or absorbing) operands become the value
//! they compute, flip-flops that can only ever hold one constant become that constant. Repeated
//! with a normalize in between until no flip-flop changes.
//!
//! Every cell is looked at once per round, in slot order; cells added during a round (the slices
//! a partly-constant flip-flop is cut into) wait for the next.

use crate::ir::constant as k;
use crate::ir::graph::{Equivalence, InstId};
use crate::ir::instance::{BinOp, Dff, ShiftOp};
use crate::ir::net::{Bundle, Const, ControlNet, Net, Trit};
use crate::ir::{Graph, Kind};

/// The net a buffer chain forwards.
fn strip_buffers(g: &Graph, mut net: Net) -> Net {
    loop {
        let (id, off) = g.resolve(net);
        match &g.inst(id).kind {
            Kind::Buffer(a) => net = a[off as usize],
            _ => return net,
        }
    }
}

/// Every bit through its buffers, when all are constants.
fn lookup_const(g: &Graph, b: &[Net]) -> Option<Const> {
    b.iter()
        .map(|&n| {
            let n = strip_buffers(g, n);
            n.is_const().then(|| n.const_trit())
        })
        .collect()
}

/// The value as an unsigned integer (bits past 64 shift out), none with an undefined bit.
fn const_to_uint(c: &[Trit]) -> Option<u64> {
    if k::has_undef(c) {
        return None;
    }
    Some(c.iter().rev().fold(0u64, |v, &t| (v << 1) | (t == Trit::One) as u64))
}

/// The exponent of a power of two.
fn log2_exact(v: u64) -> Option<u32> {
    (v != 0 && v & (v - 1) == 0).then(|| v.trailing_zeros())
}

/// The position of the only 1 bit (other bits 0 or x), none for no 1 or several.
fn single_one(c: &[Trit]) -> Option<u64> {
    let mut at = None;
    for (i, &t) in c.iter().enumerate() {
        if t == Trit::One {
            if at.is_some() {
                return None;
            }
            at = Some(i as u64);
        }
    }
    at
}

fn from_const(c: &[Trit]) -> Bundle {
    c.iter().map(|&t| Net::from_trit(t)).collect()
}

/// A bitwise rule per bit: the replacement, or the output bit itself when it does not apply.
fn per_bit(g: &Graph, a: &[Net], b: &[Net], out: &[Net], rule: fn(Net, Net) -> Option<Net>) -> (Bundle, bool) {
    let mut changed = false;
    let r = (0..out.len())
        .map(|i| {
            let r = rule(strip_buffers(g, a[i]), strip_buffers(g, b[i])).unwrap_or(out[i]);
            changed |= r != out[i];
            r
        })
        .collect();
    (r, changed)
}

fn both_const(a: Net, b: Net, f: fn(Trit, Trit) -> Trit) -> Option<Net> {
    (a.is_const() && b.is_const()).then(|| Net::from_trit(f(a.const_trit(), b.const_trit())))
}

fn fold_and(a: Net, b: Net) -> Option<Net> {
    if a == Net::ZERO || b == Net::ZERO {
        Some(Net::ZERO)
    } else if a == Net::ONE {
        Some(b)
    } else if b == Net::ONE || a == b {
        Some(a)
    } else {
        both_const(a, b, k::and)
    }
}

fn fold_or(a: Net, b: Net) -> Option<Net> {
    if a == Net::ONE || b == Net::ONE {
        Some(Net::ONE)
    } else if a == Net::ZERO {
        Some(b)
    } else if b == Net::ZERO || a == b {
        Some(a)
    } else {
        both_const(a, b, k::or)
    }
}

fn fold_xor(a: Net, b: Net) -> Option<Net> {
    if a == Net::ZERO {
        Some(b)
    } else if b == Net::ZERO {
        Some(a)
    } else if a == b {
        Some(Net::ZERO)
    } else {
        both_const(a, b, k::xor)
    }
}

fn fold_andnot(a: Net, b: Net) -> Option<Net> {
    if a == Net::ZERO || b == Net::ONE {
        Some(Net::ZERO)
    } else if b == Net::ZERO {
        Some(a)
    } else {
        both_const(a, b, |x, y| k::and(x, k::not(y)))
    }
}

/// `out[i]` = `a[i - shift]` (0 below), for a constant left shift.
fn wire_left(g: &Graph, a: &[Net], width: usize, shift: u64) -> Bundle {
    (0..width as u64)
        .map(|i| if i >= shift && i - shift < a.len() as u64 { strip_buffers(g, a[(i - shift) as usize]) } else { Net::ZERO })
        .collect()
}

/// `out[i]` = `a[i + shift]` (`fill` past the top), for a constant right shift.
fn wire_right(g: &Graph, a: &[Net], width: usize, shift: u64, fill: Net) -> Bundle {
    (0..width as u64)
        .map(|i| {
            let j = i.wrapping_add(shift);
            if j < a.len() as u64 { strip_buffers(g, a[j as usize]) } else { fill }
        })
        .collect()
}

/// The replacement for one combinational cell's output, if it folds.
fn fold_one(g: &Graph, id: InstId, out: &[Net]) -> Option<Bundle> {
    let width = out.len();
    let fit = |c: Vec<Trit>| -> Bundle { from_const(&c[..width]) };
    match &g.inst(id).kind {
        Kind::Not(a) => {
            let mut any = false;
            let r = (0..width)
                .map(|i| {
                    let x = strip_buffers(g, a[i]);
                    if x.is_const() {
                        any = true;
                        Net::from_trit(k::not(x.const_trit()))
                    } else {
                        out[i]
                    }
                })
                .collect();
            any.then_some(r)
        }
        Kind::Bin(op @ (BinOp::And | BinOp::Or | BinOp::Xor | BinOp::Andnot), a, b) => {
            let rule = match op {
                BinOp::And => fold_and,
                BinOp::Or => fold_or,
                BinOp::Xor => fold_xor,
                _ => fold_andnot,
            };
            let (r, changed) = per_bit(g, a, b, out, rule);
            changed.then_some(r)
        }
        Kind::Mux(s, a, b) => {
            let sel = strip_buffers(g, *s);
            let mut changed = false;
            let r = (0..width)
                .map(|i| {
                    let (ai, bi) = (strip_buffers(g, a[i]), strip_buffers(g, b[i]));
                    let r = if sel == Net::ONE {
                        ai
                    } else if sel == Net::ZERO || ai == bi {
                        if sel == Net::ZERO { bi } else { ai }
                    } else if sel.is_const() && ai.is_const() && bi.is_const() {
                        Net::from_trit(k::mux(sel.const_trit(), ai.const_trit(), bi.const_trit()))
                    } else if ai == Net::UNDEF {
                        bi
                    } else if bi == Net::UNDEF {
                        ai
                    } else if ai == Net::ONE && bi == Net::ZERO {
                        sel
                    } else {
                        out[i]
                    };
                    changed |= r != out[i];
                    r
                })
                .collect();
            changed.then_some(r)
        }
        Kind::Adc(a, b, cin) => {
            let (ac, bc) = (lookup_const(g, a)?, lookup_const(g, b)?);
            let cin = strip_buffers(g, *cin);
            cin.is_const().then(|| fit(k::adc(&ac, &bc, cin.const_trit())))
        }
        Kind::Bin(op @ (BinOp::Eq | BinOp::ULt | BinOp::SLt), a, b) => {
            let (ac, bc) = (lookup_const(g, a)?, lookup_const(g, b)?);
            let t = match op {
                BinOp::Eq => k::eq(&ac, &bc),
                BinOp::ULt => k::ult(&ac, &bc),
                _ => k::slt(&ac, &bc),
            };
            Some(vec![Net::from_trit(t)])
        }
        Kind::Shift(op, a, b, stride) => {
            let bc = lookup_const(g, b)?;
            if let Some(ac) = lookup_const(g, a) {
                return Some(fit(match op {
                    ShiftOp::Shl => k::shl(&ac, &bc, *stride),
                    ShiftOp::UShr => k::ushr(&ac, &bc, *stride),
                    ShiftOp::SShr => k::sshr(&ac, &bc, *stride),
                    ShiftOp::XShr => k::xshr(&ac, &bc, *stride),
                }));
            }
            // A constant amount: the bits are wired straight through.
            let shift = const_to_uint(&bc)?.wrapping_mul(*stride as u64);
            Some(match op {
                ShiftOp::Shl => wire_left(g, a, width, shift),
                ShiftOp::UShr => wire_right(g, a, width, shift, Net::ZERO),
                ShiftOp::SShr => wire_right(g, a, width, shift, strip_buffers(g, a[a.len() - 1])),
                ShiftOp::XShr => wire_right(g, a, width, shift, Net::UNDEF),
            })
        }
        Kind::Bin(op @ (BinOp::Mul | BinOp::UDiv | BinOp::UMod), a, b) => {
            let bc = lookup_const(g, b)?;
            if let Some(ac) = lookup_const(g, a) {
                return Some(fit(match op {
                    BinOp::Mul => k::mul(&ac, &bc),
                    BinOp::UDiv => k::udiv(&ac, &bc),
                    _ => k::umod(&ac, &bc),
                }));
            }
            match op {
                // Times a power of two: a left shift.
                BinOp::Mul => Some(wire_left(g, a, width, log2_exact(const_to_uint(&bc)?)? as u64)),
                // By a power of two (its only 1 bit; x bits do not count): a right shift.
                BinOp::UDiv => Some(wire_right(g, a, width, single_one(&bc)?, Net::ZERO)),
                // Modulo a power of two: the bits below it.
                _ => {
                    let shift = single_one(&bc)?;
                    Some((0..width).map(|i| if (i as u64) < shift { strip_buffers(g, a[i]) } else { Net::ZERO }).collect())
                }
            }
        }
        _ => None,
    }
}

fn fold_combinationals(g: &mut Graph) {
    let mut it = g.instances();
    while let Some(id) = it.next(g) {
        let out = g.output(id);
        if let Some(r) = fold_one(g, id, &out) {
            let support = support_through(g, id, strip_buffers);
            g.replace(&out, &r, Equivalence::Refinement, &support);
        }
    }
}

/// The cell's inputs, each through `f` (what the replacement is checked against).
fn support_through(g: &Graph, id: InstId, f: impl Fn(&Graph, Net) -> Net) -> Bundle {
    g.inst(id).kind.inputs().into_iter().map(|n| f(g, n)).collect()
}

/// Two values that must agree: the defined one, or none when they fight or either is unknown.
fn refine(a: Option<Trit>, b: Option<Trit>) -> Option<Trit> {
    let (a, b) = (a?, b?);
    if a != Trit::Undef && b != Trit::Undef && a != b {
        return None;
    }
    Some(if a != Trit::Undef { a } else { b })
}

/// A control through its buffers and inverters, the inverters folded into its polarity.
fn absorb_nots(g: &Graph, mut cn: ControlNet) -> ControlNet {
    loop {
        let n = strip_buffers(g, cn.net);
        if n.is_const() {
            return ControlNet::with_polarity(n, cn.positive);
        }
        let (drv, off) = g.resolve(n);
        match &g.inst(drv).kind {
            Kind::Not(a) => cn = ControlNet::with_polarity(a[off as usize], !cn.positive),
            _ => return ControlNet::with_polarity(n, cn.positive),
        }
    }
}

/// A new flip-flop for bits `base..base + width` of `d`, with its controls.
fn slice_dff(g: &mut Graph, d: &Dff, base: usize, width: usize) -> Bundle {
    assert!(width > 0);
    let r = base..base + width;
    g.add(Kind::Dff(Box::new(Dff {
        data: d.data[r.clone()].to_vec(),
        clock: d.clock,
        clear: d.clear,
        reset: d.reset,
        enable: d.enable,
        init_value: d.init_value[r.clone()].to_vec(),
        reset_value: d.reset_value[r.clone()].to_vec(),
        clear_value: d.clear_value[r].to_vec(),
    })))
}

/// The value bit `i` of a flip-flop holds whatever happens, if one constant: its data `d` (none
/// for feedback) agreeing with its initial value and, where those can act, its clear and reset
/// values.
fn held_value(dff: &Dff, i: usize, start: Option<Trit>) -> Option<Trit> {
    let mut v = start;
    if !dff.clear.is_always(false) {
        v = refine(v, Some(dff.clear_value[i]));
    }
    if !dff.reset.is_always(false) {
        v = refine(v, Some(dff.reset_value[i]));
    }
    v
}

fn fold_sequentials(g: &mut Graph) -> bool {
    let mut changed = false;
    let mut it = g.instances();
    while let Some(id) = it.next(g) {
        if !matches!(g.inst(id).kind, Kind::Dff(_)) {
            continue;
        }
        // Inverters on the controls fold into their polarity, whether or not the flop folds.
        let Kind::Dff(d) = &g.inst(id).kind else { unreachable!() };
        let (clock, clear, reset, enable) =
            (absorb_nots(g, d.clock), absorb_nots(g, d.clear), absorb_nots(g, d.reset), absorb_nots(g, d.enable));
        let Kind::Dff(d) = &mut g.inst_mut(id).kind else { unreachable!() };
        d.clock = clock;
        d.clear = clear;
        d.reset = reset;
        d.enable = enable;
        let Kind::Dff(dff) = &g.inst(id).kind else { unreachable!() };
        let dff = (**dff).clone();

        let out = g.output(id);
        let mut new_out = out.clone();
        let mut any = false;
        for i in 0..out.len() {
            let d = strip_buffers(g, dff.data[i]);
            // Feedback: the flop never leaves its initial / clear / reset value.
            if d == out[i] {
                if let Some(v) = held_value(&dff, i, Some(dff.init_value[i])) {
                    new_out[i] = Net::from_trit(v);
                    any = true;
                    continue;
                }
            }
            // A constant input that its initial / clear / reset values agree with.
            if d.is_const() {
                if let Some(v) = held_value(&dff, i, refine(Some(dff.init_value[i]), Some(d.const_trit()))) {
                    new_out[i] = Net::from_trit(v);
                    any = true;
                }
            }
        }
        if !any {
            continue;
        }
        let support = support_through(g, id, |g, n| absorb_nots(g, ControlNet::pos(n)).net);
        // The bits that stay are kept by new flip-flops, one per run.
        let mut i = 0;
        while i < out.len() {
            if new_out[i] == out[i] {
                let mut w = 1;
                while i + w < out.len() && new_out[i + w] == out[i + w] {
                    w += 1;
                }
                let slice = slice_dff(g, &dff, i, w);
                new_out[i..i + w].copy_from_slice(&slice);
                i += w;
            } else {
                i += 1;
            }
        }
        g.replace(&out, &new_out, Equivalence::Refinement, &support);
        changed = true;
        g.remove_instance(id);
    }
    changed
}

/// Folds to a fixed point: normalize, fold the combinational cells, fold the flip-flops; again
/// until no flip-flop folds.
pub fn constant_fold(g: &mut Graph) {
    loop {
        g.normalize();
        fold_combinationals(g);
        if !fold_sequentials(g) {
            break;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::parse::parse;

    fn folded(ir: &str) -> String {
        let mut g = parse(ir, None).expect("parses");
        constant_fold(&mut g);
        g.normalize();
        g.dump()
    }

    #[test]
    fn and_of_a_net_with_itself_is_the_net() {
        assert_eq!(folded("%3:2 = input \"a\"\n%5:2 = and %3:2 %3:2\n%7:0 = output \"y\" %5:2\n"),
                   "%3:2 = input \"a\"\n%5:0 = output \"y\" %3:2\n");
    }

    #[test]
    fn mux_choosing_one_or_zero_is_its_select() {
        // sel ? 1 : 0 = sel; the cell takes (select, on-1, on-0).
        assert_eq!(folded("%3:1 = input \"s\"\n%4:1 = mux %3 1 0\n%5:0 = output \"y\" %4\n"),
                   "%3:1 = input \"s\"\n%4:0 = output \"y\" %3\n");
    }

    #[test]
    fn a_flop_fed_back_with_no_clear_or_reset_holds_its_initial_value() {
        // D = Q: the flop never changes; its initial value (x, as parsed) is what it holds.
        assert_eq!(folded("%3:1 = input \"clk\"\n%4:1 = dff %4 clk=%3\n%5:0 = output \"q\" %4\n"),
                   "%3:1 = input \"clk\"\n%4:0 = output \"q\" X\n");
    }

    #[test]
    fn division_by_a_constant_with_one_1_bit_ignores_its_x_bits() {
        // The divisor 0b0X10 has one 1 bit (x bits are not counted): a right shift by 1.
        assert_eq!(folded("%3:4 = input \"a\"\n%7:4 = udiv %3:4 0X10\n%11:0 = output \"y\" %7:4\n"),
                   "%3:4 = input \"a\"\n%7:0 = output \"y\" [ 0 %3+1:3 ]\n");
    }
}
