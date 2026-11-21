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

/// An adder's carry chain cut where it can be (OpenROAD #12080, after prjunnamed's rule). Walking
/// the stages from the bottom with the carry into the next unemitted stage (at first the carry
/// in, through its buffers):
///
/// - equal summands at stage `i` (through their buffers) cut the chain: the pending stages below
///   become a new adder on the ORIGINAL summand bits with that carry in (none pending: the carry
///   itself), whose carry out is stage `i`'s sum bit; the carry out of stage `i` is the summand;
/// - else, with no stage pending, a summand equal to the carry makes the sum bit the other
///   summand, the carry unchanged.
///
/// Once anything is emitted, the pending stages and the carry out become one more adder (the
/// carry when none are pending). Nothing emitted: no fold — an all-constant adder folds through
/// these rules, the old whole-adder constant evaluation is gone. The new adders are added during
/// the walk and wait for the next round.
fn fold_adc(g: &mut Graph, a: &[Net], b: &[Net], cin: Net) -> Option<Bundle> {
    let width = a.len() + 1;
    let mut out = Vec::with_capacity(width);
    let mut carry = strip_buffers(g, cin);
    let batch = |g: &mut Graph, out: &mut Vec<Net>, upto: usize, carry: Net| {
        let from = out.len();
        let value = if upto > from { g.add(Kind::Adc(a[from..upto].to_vec(), b[from..upto].to_vec(), carry)) } else { vec![carry] };
        out.extend(value);
    };
    for i in 0..width - 1 {
        let (ai, bi) = (strip_buffers(g, a[i]), strip_buffers(g, b[i]));
        if ai == bi {
            batch(g, &mut out, i, carry);
            carry = ai;
        } else if out.len() == i {
            if ai == carry {
                out.push(bi);
            } else if bi == carry {
                out.push(ai);
            }
        }
    }
    if out.is_empty() {
        return None;
    }
    batch(g, &mut out, width - 1, carry);
    Some(out)
}

fn fold_combinationals(g: &mut Graph) {
    let mut it = g.instances();
    while let Some(id) = it.next(g) {
        let out = g.output(id);
        let folded = match &g.inst(id).kind {
            Kind::Adc(a, b, cin) => {
                let (a, b, cin) = (a.clone(), b.clone(), *cin);
                fold_adc(g, &a, &b, cin)
            }
            _ => fold_one(g, id, &out),
        };
        if let Some(r) = folded {
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

    use crate::ir::eval::{all_values, Eval};

    /// An operand bit drawn from: the constants 0, 1, X, or bit `i` of input `p` or `q`.
    #[derive(Clone, Copy)]
    enum Src {
        K(Trit),
        P,
        Q,
    }
    const SRCS: [Src; 5] = [Src::K(Trit::Zero), Src::K(Trit::One), Src::K(Trit::Undef), Src::P, Src::Q];

    fn bits(srcs: &[Src], p: &[Net], q: &[Net]) -> Bundle {
        srcs.iter()
            .enumerate()
            .map(|(i, s)| match s {
                Src::K(t) => Net::from_trit(*t),
                Src::P => p[i],
                Src::Q => q[i],
            })
            .collect()
    }

    /// Every operand choice in `choices` of `n` bits each.
    fn operands(n: usize, choices: &[Src]) -> Vec<Vec<Src>> {
        let mut out = vec![Vec::new()];
        for _ in 0..n {
            out = out.into_iter().flat_map(|v| choices.iter().map(move |&c| [v.clone(), vec![c]].concat())).collect();
        }
        out
    }

    /// Builds a cell on two operand bundles in a graph.
    type MakeOn<'a> = dyn Fn(&mut Graph, &[Net], &[Net]) -> Bundle + 'a;
    /// A cell on two operands and a carry-in.
    type MakeCarry = Box<dyn Fn(Bundle, Bundle, Net) -> Kind>;

    /// `constant_fold` replaces a cell under `Equivalence::Refinement`: wherever the cell's value
    /// is defined, the replacement must have that value. Checked by evaluating the graph before
    /// and after the pass (`ir::eval`, the reference `TritModel`'s meaning) on every assignment
    /// of the inputs, X included. Returns the first counterexample.
    fn refines(make: &MakeOn<'_>, w: u32) -> Result<(), String> {
        let mut g = Graph::new();
        let p = g.add(Kind::Input("p".into(), w));
        let q = g.add(Kind::Input("q".into(), w));
        let y = make(&mut g, &p, &q);
        g.add(Kind::Output("y".into(), y));
        let before = g.clone();
        let mut after = g;
        constant_fold(&mut after);
        let (mut e0, mut e1) = (Eval::new(&before), Eval::new(&after));
        for pv in all_values(w as usize, true) {
            for qv in all_values(w as usize, true) {
                for e in [&mut e0, &mut e1] {
                    e.set_input("p", &pv);
                    e.set_input("q", &qv);
                }
                let (y0, y1) = (e0.output("y"), e1.output("y"));
                let bad = y0.iter().zip(&y1).any(|(&a, &b)| a != Trit::Undef && a != b);
                if bad {
                    return Err(format!("p={pv:?} q={qv:?}: before {y0:?}, after {y1:?}\n{}", before.dump()));
                }
            }
        }
        Ok(())
    }

    /// The bitwise and mux folds, one bit, every operand drawn from 0, 1, X, p, q: each fold
    /// refines the cell (`Equivalence::Refinement`, as the reference replaces it).
    #[test]
    fn bitwise_and_mux_folds_refine_the_cell() {
        for op in [BinOp::And, BinOp::Or, BinOp::Xor, BinOp::Andnot] {
            for a in SRCS {
                for b in SRCS {
                    let make = |g: &mut Graph, p: &[Net], q: &[Net]| {
                        let (x, y) = (bits(&[a], p, q), bits(&[b], p, q));
                        g.add(Kind::Bin(op, x, y))
                    };
                    refines(&make, 1).unwrap_or_else(|e| panic!("{}: {e}", op.keyword()));
                }
            }
        }
        for s in SRCS {
            for a in SRCS {
                for b in SRCS {
                    let make = |g: &mut Graph, p: &[Net], q: &[Net]| {
                        let sel = bits(&[s], p, q)[0];
                        let (x, y) = (bits(&[a], p, q), bits(&[b], p, q));
                        g.add(Kind::Mux(sel, x, y))
                    };
                    refines(&make, 1).unwrap_or_else(|e| panic!("mux: {e}"));
                }
            }
        }
        let make = |g: &mut Graph, p: &[Net], _: &[Net]| {
            let x = bits(&[Src::P], p, p);
            g.add(Kind::Not(x))
        };
        refines(&make, 1).unwrap_or_else(|e| panic!("not: {e}"));
    }

    /// The word cells' folds (all constant operands; a constant amount, multiplier or divisor),
    /// each operand bit drawn from 0, 1, X and an input bit: every 2-bit mix, and at 3 bits an
    /// input word against every constant and every constant pair.
    #[test]
    fn word_folds_refine_the_cell() {
        let cells: Vec<(&str, MakeCarry)> = vec![
            ("adc", Box::new(Kind::Adc)),
            ("eq", Box::new(|a, b, _| Kind::Bin(BinOp::Eq, a, b))),
            ("ult", Box::new(|a, b, _| Kind::Bin(BinOp::ULt, a, b))),
            ("slt", Box::new(|a, b, _| Kind::Bin(BinOp::SLt, a, b))),
            ("mul", Box::new(|a, b, _| Kind::Bin(BinOp::Mul, a, b))),
            ("udiv", Box::new(|a, b, _| Kind::Bin(BinOp::UDiv, a, b))),
            ("umod", Box::new(|a, b, _| Kind::Bin(BinOp::UMod, a, b))),
            ("shl", Box::new(|a, b, _| Kind::Shift(ShiftOp::Shl, a, b, 1))),
            ("ushr", Box::new(|a, b, _| Kind::Shift(ShiftOp::UShr, a, b, 1))),
            ("sshr", Box::new(|a, b, _| Kind::Shift(ShiftOp::SShr, a, b, 1))),
            ("xshr", Box::new(|a, b, _| Kind::Shift(ShiftOp::XShr, a, b, 1))),
            ("shl2", Box::new(|a, b, _| Kind::Shift(ShiftOp::Shl, a, b, 2))),
        ];
        let k3 = [Src::K(Trit::Zero), Src::K(Trit::One), Src::K(Trit::Undef)];
        let with_p: Vec<Src> = [k3.as_slice(), &[Src::P]].concat();
        let with_q: Vec<Src> = [k3.as_slice(), &[Src::Q]].concat();
        for (name, cell) in &cells {
            let mut cases: Vec<(u32, Vec<Src>, Vec<Src>, Src)> = Vec::new();
            for a in operands(2, &with_p) {
                for b in operands(2, &with_q) {
                    for c in [k3[0], k3[2], Src::P] {
                        cases.push((2, a.clone(), b.clone(), c));
                    }
                }
            }
            for b in operands(3, &k3) {
                cases.push((3, vec![Src::P; 3], b.clone(), k3[0]));
                for a in operands(3, &k3) {
                    cases.push((3, a, b.clone(), k3[1]));
                }
            }
            for (w, a, b, c) in cases {
                let make = |_: &mut Graph, p: &[Net], q: &[Net]| (bits(&a, p, q), bits(&b, p, q), bits(&[c], p, q)[0]);
                let make = |g: &mut Graph, p: &[Net], q: &[Net]| {
                    let (x, y, ci) = make(g, p, q);
                    g.add(cell(x, y, ci))
                };
                refines(&make, w).unwrap_or_else(|e| panic!("{name}: {e}"));
            }
        }
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

    /// The adders left in `g`, by summand width.
    fn adc_widths(g: &Graph) -> Vec<usize> {
        let mut w: Vec<usize> = g.instance_list().into_iter().filter_map(|id| match &g.inst(id).kind {
            Kind::Adc(a, _, _) => Some(a.len()),
            _ => None,
        }).collect();
        w.sort();
        w
    }

    /// `a` + `b` + carry on two `w`-bit inputs `a`, `b` and a one-bit input `cin`, `wire` editing
    /// the operands first; folded, checked EQUAL to the unfolded graph on every defined input
    /// (the upstream tests' `equivalenceCheck(inputsDefined, no refinement)`), and returned.
    fn adder_folded(w: u32, wire: impl Fn(&mut Bundle, &mut Bundle, &mut Net)) -> Graph {
        let mut g = Graph::new();
        let mut a = g.add(Kind::Input("a".into(), w));
        let mut b = g.add(Kind::Input("b".into(), w));
        let mut c = g.add(Kind::Input("cin".into(), 1))[0];
        wire(&mut a, &mut b, &mut c);
        let y = g.add(Kind::Adc(a, b, c));
        g.add(Kind::Output("y".into(), y));
        let before = g.clone();
        constant_fold(&mut g);
        g.normalize();
        let (mut e0, mut e1) = (Eval::new(&before), Eval::new(&g));
        for av in all_values(w as usize, false) {
            for bv in all_values(w as usize, false) {
                for cv in all_values(1, false) {
                    for e in [&mut e0, &mut e1] {
                        e.set_input("a", &av);
                        e.set_input("b", &bv);
                        e.set_input("cin", &cv);
                    }
                    assert_eq!(e0.output("y"), e1.output("y"), "a={av:?} b={bv:?} cin={cv:?}\n{}", g.dump());
                }
            }
        }
        g
    }

    // Rule (OpenROAD #12080, upstream test AdcEqualSummandsBreaksCarryChain): equal summands at a
    // middle stage cut the chain there — the stage's sum is the carry into it, its carry out the
    // summand — so one adder becomes one below and one above the cut.
    #[test]
    fn equal_summands_cut_the_carry_chain() {
        let g = adder_folded(6, |a, b, _| b[2] = a[2]);
        assert_eq!(adc_widths(&g), [2, 3]);
        // at the bottom stage: nothing pending below, the carry in is the low sum bit
        assert_eq!(adc_widths(&adder_folded(4, |a, b, _| b[0] = a[0])), [3]);
        // at the top stage: the upper adder is empty, the carry out is the summand
        assert_eq!(adc_widths(&adder_folded(4, |a, b, _| b[3] = a[3])), [3]);
    }

    // Rule (#12080, upstream test AdcCarryInEqualsSummand): a summand equal to the carry into a
    // stage with nothing pending makes the sum the other summand, the carry passing through.
    #[test]
    fn a_summand_equal_to_the_carry_drops_its_stage() {
        let g = adder_folded(5, |a, _, c| *c = a[0]);
        assert_eq!(adc_widths(&g), [4]);
        // the other summand too, and stage after stage while the carry is unchanged
        assert_eq!(adc_widths(&adder_folded(5, |_, b, c| *c = b[0])), [4]);
        assert_eq!(adc_widths(&adder_folded(5, |a, b, c| { *c = a[0]; b[1] = a[0]; })), [3]);
        // with a stage pending, no: the carry into the later stage is not the carry held
        assert_eq!(adc_widths(&adder_folded(3, |a, _, c| *c = a[1])), [3]);
    }

    // Rule (#12080): the whole-adder constant evaluation is gone; constants fold only through the
    // stage rules. An all-constant adder with a defined carry folds away; one whose carry is X and
    // whose low summands differ stays.
    #[test]
    fn a_constant_adder_folds_through_the_stage_rules_only() {
        let one = adder_folded(2, |a, b, c| { *a = vec![Net::ONE, Net::ZERO]; *b = vec![Net::ZERO, Net::ONE]; *c = Net::ZERO; });
        assert_eq!(adc_widths(&one), Vec::<usize>::new());
        let mut g = Graph::new();
        let y = g.add(Kind::Adc(vec![Net::ONE], vec![Net::ZERO], Net::UNDEF));
        g.add(Kind::Output("y".into(), y));
        constant_fold(&mut g);
        g.normalize();
        assert_eq!(adc_widths(&g), [1]);
    }
}
