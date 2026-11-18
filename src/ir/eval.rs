// SPDX-License-Identifier: Apache-2.0
//! A three-valued evaluator of the graph, for tests: the reference meaning of every cell, to check
//! a pass by evaluating the graph before and after it on the same inputs.
//!
//! Crate-internal and test-only. It is written from the reference's `TritModel` (the SAT
//! encoding the reference uses to reason about a cone; `ir/TritModel.cc`), not from our passes,
//! so that a pass is checked against something it does not share code with: `ir::constant` is
//! the constant folder's arithmetic and is deliberately not called here.
//!
//! Per bit, a value is 0, 1 or X. Where `TritModel` says when a result is defined:
//! - bitwise: 0 decides AND (and `a & !b` on either side), 1 decides OR; XOR needs both;
//! - mux: a defined select picks its side; an X select keeps a bit both sides agree on;
//! - `eq`: a defined mismatch anywhere is 0, else any X is X;
//! - `ult` / `slt`, `mul`: any X input is X everywhere;
//! - `adc`: bit i is defined when every operand bit up to i and the carry in are;
//! - shifts: by a defined amount (times the stride) the bits move, X bits with them; vacated
//!   bits are 0 (`shl`, `ushr`), the sign bit (`sshr`), X (`xshr`);
//! - a library cell without state whose outputs all have a function: the function, defined when
//!   every input is; any other library cell, and a black box, is X.
//!
//! Where we depart from `TritModel`, and why:
//! - division and modulo, signed or not: any X operand bit, or a zero divisor, gives X
//!   everywhere, else the integer result (signed: truncating or flooring as our bit-blast D1
//!   builds it, `flow::bitblast::divmod`). That is the reference's constant arithmetic
//!   (`Const::udiv` / `umod`, what its constant folder computes) and Verilog's rule for
//!   arithmetic on x bits and a zero divisor. `TritModel` disagrees with `Const` here: its
//!   restoring encoding calls `x / 0` defined (all ones, remainder `x`, the value Yosys and D1
//!   build) and some quotient bits defined beside an X operand bit; it leaves signed division
//!   free. Both of those are refinements of X, so a pass may produce them, and a check must
//!   compare by refinement (where the cell is defined), never by equality;
//! - a shift amount with any X bit gives X everywhere (`Const`'s shifts, Verilog's rule);
//!   `TritModel`'s barrel calls a bit defined when every stage that moves it is (a 2-bit value
//!   shifted by `1X` is 0 there);
//! - a shift amount past the width vacates every bit (`TritModel` computes stride * 2^k in 32 bits);
//! - a loop breaker is a buffer; a value that depends on itself is X;
//! - a register holds its state: [`Eval::step`] is one active clock edge for every register, the
//!   output follows an active asynchronous clear at once. A synchronous reset is not modelled (the
//!   frontend never builds one): such a register panics.

use std::collections::{HashMap, HashSet};

use vyges_loom::liberty_func::Func;

use super::instance::LibDirection;
use super::net::{ControlNet, Net, Trit};
use super::{BinOp, Graph, InstId, Kind, ShiftOp};

use Trit::{One, Undef as X, Zero};

/// The graph evaluated on one assignment of its inputs and registers.
pub(crate) struct Eval<'g> {
    g: &'g Graph,
    inputs: HashMap<String, Vec<Trit>>,
    state: HashMap<InstId, Vec<Trit>>,
    /// A library flip-flop's state variable (`IQ`), X until it is clocked.
    ff: HashMap<InstId, Trit>,
    memo: HashMap<u32, Trit>,
    busy: HashSet<u32>,
}

impl<'g> Eval<'g> {
    /// Inputs X, registers at their initial values.
    pub(crate) fn new(g: &'g Graph) -> Self {
        let mut state = HashMap::new();
        for id in g.instance_list() {
            if let Kind::Dff(d) = &g.inst(id).kind {
                state.insert(id, d.init_value.clone());
            }
        }
        Eval { g, inputs: HashMap::new(), state, ff: HashMap::new(), memo: HashMap::new(), busy: HashSet::new() }
    }

    /// Drive input port `name`, least significant bit first.
    pub(crate) fn set_input(&mut self, name: &str, bits: &[Trit]) {
        self.inputs.insert(name.to_string(), bits.to_vec());
        self.memo.clear();
    }

    /// Drive input port `name` with the low bits of `v`.
    pub(crate) fn set_input_u64(&mut self, name: &str, width: u32, v: u64) {
        let bits: Vec<Trit> = (0..width).map(|i| trit((v >> i) & 1 == 1)).collect();
        self.set_input(name, &bits);
    }

    /// Set register `id`'s state.
    pub(crate) fn set_register(&mut self, id: InstId, bits: &[Trit]) {
        self.state.insert(id, bits.to_vec());
        self.memo.clear();
    }

    /// Output port `name`'s bits.
    pub(crate) fn output(&mut self, name: &str) -> Vec<Trit> {
        let g = self.g;
        let found = g.instance_list().into_iter().find_map(|id| match &g.inst(id).kind {
            Kind::Output(n, v) if n == name => Some(v.clone()),
            _ => None,
        });
        let v = found.unwrap_or_else(|| panic!("the graph has no output {name}"));
        self.bundle(&v)
    }

    pub(crate) fn bundle(&mut self, v: &[Net]) -> Vec<Trit> {
        v.iter().map(|&n| self.net(n)).collect()
    }

    /// One active clock edge for every register (its clock net is not read): each takes its data
    /// where its enable is active, holds where it is not, and is X where the enable is X and the
    /// two differ. A register held by an active clear keeps the clear value.
    pub(crate) fn step(&mut self) {
        let g = self.g;
        let mut next = Vec::new();
        for (&id, q) in &self.state {
            let Kind::Dff(d) = &g.inst(id).kind else { unreachable!("state is kept for registers only") };
            assert!(d.reset.is_always(false), "a synchronous reset is not modelled (the frontend never builds one)");
            let data: Vec<Net> = d.data.clone();
            next.push((id, data, d.enable, q.clone()));
        }
        let mut new_state = Vec::new();
        for (id, data, enable, q) in next {
            let en = self.control(enable);
            let dv = self.bundle(&data);
            let v: Vec<Trit> = dv.iter().zip(&q).map(|(&d, &q)| mux(en, d, q)).collect();
            new_state.push((id, v));
        }
        for (id, v) in new_state {
            self.state.insert(id, v);
        }
        self.memo.clear();
        // an active clear wins over the edge
        let ids: Vec<InstId> = self.state.keys().copied().collect();
        for id in ids {
            let Kind::Dff(d) = &g.inst(id).kind else { continue };
            let clear = self.control(d.clear);
            let q = self.state[&id].clone();
            let v: Vec<Trit> = q.iter().zip(&d.clear_value).map(|(&q, &c)| mux(clear, c, q)).collect();
            self.state.insert(id, v);
        }
        self.memo.clear();
    }

    /// Drive input `name` as a clock: the registers whose clock goes from inactive to active
    /// take their data (as it was before the edge), and so do the library flip-flops whose
    /// `clocked_on` rises; an X transition is X where the two values differ. Asynchronous clears
    /// and presets act on the outputs as levels.
    pub(crate) fn clock(&mut self, name: &str, bits: &[Trit]) {
        let g = self.g;
        let ids = g.instance_list();
        // before the edge: each register's clock level and data, each flip-flop's clock and data
        let mut regs = Vec::new();
        let mut ffs = Vec::new();
        for &id in &ids {
            match &g.inst(id).kind {
                Kind::Dff(d) => {
                    assert!(d.reset.is_always(false), "a synchronous reset is not modelled (the frontend never builds one)");
                    let level = self.control(d.clock);
                    let en = self.control(d.enable);
                    let data = self.bundle(&d.data);
                    regs.push((id, level, en, data));
                }
                Kind::Target(cell, inputs) if cell.seq.as_ref().is_some_and(|q| !q.latch) => {
                    let ins = self.bundle(inputs);
                    let seq = cell.seq.as_ref().expect("matched a flip-flop");
                    let clk = seq_expr(cell, &ins, seq.clocked_on.as_deref());
                    let next = seq_expr(cell, &ins, seq.next_state.as_deref());
                    ffs.push((id, clk, next));
                }
                _ => {}
            }
        }
        self.set_input(name, bits);
        for (id, before, en, data) in regs {
            let Kind::Dff(d) = &g.inst(id).kind else { unreachable!("collected as a register") };
            let after = self.control(d.clock);
            let edge = rising(before, after);
            let q = self.state[&id].clone();
            let v: Vec<Trit> = data.iter().zip(&q).map(|(&d, &q)| mux(edge, mux(en, d, q), q)).collect();
            self.state.insert(id, v);
        }
        for (id, before, next) in ffs {
            let Kind::Target(cell, inputs) = &g.inst(id).kind else { unreachable!("collected as a flip-flop") };
            let ins = self.bundle(inputs);
            let seq = cell.seq.as_ref().expect("collected as a flip-flop");
            let after = seq_expr(cell, &ins, seq.clocked_on.as_deref());
            let iq = self.ff.get(&id).copied().unwrap_or(X);
            self.ff.insert(id, mux(rising(before, after), next, iq));
        }
        self.memo.clear();
        // an asynchronous clear or preset holds the state while active
        for &id in &ids {
            if let Kind::Dff(d) = &g.inst(id).kind {
                let clear = self.control(d.clear);
                let q = self.state[&id].clone();
                let v: Vec<Trit> = q.iter().zip(&d.clear_value).map(|(&q, &c)| mux(clear, c, q)).collect();
                self.state.insert(id, v);
            }
            if let Kind::Target(cell, inputs) = &g.inst(id).kind {
                if cell.seq.as_ref().is_some_and(|q| !q.latch) {
                    let ins = self.bundle(inputs);
                    let iq = self.ff.get(&id).copied().unwrap_or(X);
                    self.ff.insert(id, async_state(cell, &ins, iq));
                }
            }
        }
        self.memo.clear();
    }

    /// A control's level, active = 1.
    fn control(&mut self, c: ControlNet) -> Trit {
        let v = self.net(c.net);
        if c.positive {
            v
        } else {
            not(v)
        }
    }

    /// One bit's value.
    pub(crate) fn net(&mut self, net: Net) -> Trit {
        match net {
            Net::ZERO => return Zero,
            Net::ONE => return One,
            Net::UNDEF => return X,
            _ => {}
        }
        if let Some(&v) = self.memo.get(&net.0) {
            return v;
        }
        if !self.busy.insert(net.0) {
            // the value depends on itself
            return X;
        }
        let (id, off) = self.g.resolve(net);
        let v = self.compute(id, off);
        self.busy.remove(&net.0);
        self.memo.insert(net.0, v);
        v
    }

    fn compute(&mut self, id: InstId, off: u32) -> Trit {
        let g = self.g;
        let o = off as usize;
        match &g.inst(id).kind {
            Kind::TieHigh => One,
            Kind::TieLow => Zero,
            Kind::TieX | Kind::Dangling(_) | Kind::Other(_) => X,
            Kind::Input(name, _) => self.inputs.get(name).and_then(|v| v.get(o).copied()).unwrap_or(X),
            Kind::Buffer(a) | Kind::LoopBreaker(a) => self.net(a[o]),
            Kind::Not(a) => not(self.net(a[o])),
            Kind::Bin(op, a, b) if op.is_bitwise() => {
                let (x, y) = (self.net(a[o]), self.net(b[o]));
                match op {
                    BinOp::And => and(x, y),
                    BinOp::Or => or(x, y),
                    BinOp::Andnot => and(x, not(y)),
                    _ => xor(x, y),
                }
            }
            Kind::Mux(s, a, b) => {
                let s = self.net(*s);
                let (x, y) = (self.net(a[o]), self.net(b[o]));
                mux(s, x, y)
            }
            Kind::Dff(d) => {
                let clear = self.control(d.clear);
                let q = self.state[&id][o];
                mux(clear, d.clear_value[o], q)
            }
            Kind::Bin(op, a, b) => {
                let (a, b) = (self.bundle(a), self.bundle(b));
                let n = g.inst(id).kind.output_width() as usize;
                word(*op, &a, &b, n)[o]
            }
            Kind::Adc(a, b, c) => {
                let (a, b, c) = (self.bundle(a), self.bundle(b), self.net(*c));
                adc(&a, &b, c)[o]
            }
            Kind::Shift(op, a, b, stride) => {
                let (a, b) = (self.bundle(a), self.bundle(b));
                shift(*op, &a, &b, *stride)[o]
            }
            Kind::Target(cell, inputs) if cell.seq.as_ref().is_some_and(|q| !q.latch) => {
                let ins = self.bundle(inputs);
                let iq = async_state(cell, &ins, self.ff.get(&id).copied().unwrap_or(X));
                ff_output(cell, iq, o)
            }
            Kind::Target(cell, inputs) => {
                let ins = self.bundle(inputs);
                target(cell, &ins, o)
            }
            Kind::Output(..) | Kind::Name(_) => unreachable!("an output or a name drives no net"),
        }
    }
}

fn trit(b: bool) -> Trit {
    if b {
        One
    } else {
        Zero
    }
}

fn not(a: Trit) -> Trit {
    match a {
        Zero => One,
        One => Zero,
        X => X,
    }
}

fn and(a: Trit, b: Trit) -> Trit {
    match (a, b) {
        (Zero, _) | (_, Zero) => Zero,
        (One, One) => One,
        _ => X,
    }
}

fn or(a: Trit, b: Trit) -> Trit {
    not(and(not(a), not(b)))
}

fn xor(a: Trit, b: Trit) -> Trit {
    match (a, b) {
        (X, _) | (_, X) => X,
        _ => trit(a != b),
    }
}

fn mux(s: Trit, a: Trit, b: Trit) -> Trit {
    match s {
        One => a,
        Zero => b,
        X if a == b => a,
        X => X,
    }
}

fn defined(v: &[Trit]) -> Option<Vec<bool>> {
    v.iter().map(|&t| (t != X).then_some(t == One)).collect()
}

fn from_bools(v: &[bool]) -> Vec<Trit> {
    v.iter().map(|&b| trit(b)).collect()
}

/// `adc`: ripple carry; bit i is defined while every operand bit up to i and the carry in are.
fn adc(a: &[Trit], b: &[Trit], c: Trit) -> Vec<Trit> {
    let mut out = Vec::with_capacity(a.len() + 1);
    let mut carry = c;
    for (&x, &y) in a.iter().zip(b) {
        if carry == X || x == X || y == X {
            carry = X;
            out.push(X);
            continue;
        }
        let (x, y, cv) = (x == One, y == One, carry == One);
        out.push(trit(x ^ y ^ cv));
        carry = trit((x & y) | (x & cv) | (y & cv));
    }
    out.push(carry);
    out
}

/// Word comparisons and arithmetic.
fn word(op: BinOp, a: &[Trit], b: &[Trit], n: usize) -> Vec<Trit> {
    match op {
        BinOp::Eq => {
            let mismatch = a.iter().zip(b).any(|(&x, &y)| x != X && y != X && x != y);
            let undef = a.iter().chain(b).any(|&t| t == X);
            vec![if mismatch {
                Zero
            } else if undef {
                X
            } else {
                One
            }]
        }
        BinOp::ULt | BinOp::SLt => {
            let (Some(x), Some(y)) = (defined(a), defined(b)) else { return vec![X] };
            vec![trit(less(&x, &y, op == BinOp::SLt))]
        }
        BinOp::Mul => {
            let (Some(x), Some(y)) = (defined(a), defined(b)) else { return vec![X; n] };
            from_bools(&mul(&x, &y, n))
        }
        _ => {
            let (Some(x), Some(y)) = (defined(a), defined(b)) else { return vec![X; n] };
            if !y.contains(&true) {
                return vec![X; n];
            }
            from_bools(&divmod(op, &x, &y, n))
        }
    }
}

/// `a < b`, most significant bit deciding; signed compares the sign bits the other way round.
fn less(a: &[bool], b: &[bool], signed: bool) -> bool {
    let n = a.len();
    for i in (0..n).rev() {
        let (mut x, mut y) = (a[i], b[i]);
        if signed && i == n - 1 {
            (x, y) = (!x, !y);
        }
        if x != y {
            return y;
        }
    }
    false
}

/// `a * b` to `n` bits, schoolbook.
fn mul(a: &[bool], b: &[bool], n: usize) -> Vec<bool> {
    let mut acc = vec![false; n];
    for (k, &bk) in b.iter().enumerate().take(n) {
        if !bk {
            continue;
        }
        let mut carry = false;
        for (j, slot) in acc.iter_mut().enumerate().skip(k) {
            let p = a.get(j - k).copied().unwrap_or(false);
            let s = *slot ^ p ^ carry;
            carry = (*slot & p) | (*slot & carry) | (p & carry);
            *slot = s;
        }
    }
    acc
}

/// Division and modulo of defined operands and a divisor that is not zero: unsigned, or signed
/// truncating or flooring (the D1 rule, `flow::bitblast::divmod`), to `n` bits.
fn divmod(op: BinOp, a: &[bool], b: &[bool], n: usize) -> Vec<bool> {
    assert!(a.len().max(b.len()).max(n) <= 64, "division is evaluated up to 64 bits");
    let signed = !matches!(op, BinOp::UDiv | BinOp::UMod);
    let value = |v: &[bool]| -> i128 {
        let u = v.iter().enumerate().fold(0i128, |acc, (i, &bit)| acc | (i128::from(bit) << i));
        if signed && v.last() == Some(&true) {
            u - (1i128 << v.len())
        } else {
            u
        }
    };
    let (sa, sb) = (value(a), value(b));
    let (tq, tr) = (sa / sb, sa % sb);
    let floor = tr != 0 && ((sa < 0) != (sb < 0));
    let r: i128 = match op {
        BinOp::UDiv | BinOp::SDivTrunc => tq,
        BinOp::UMod | BinOp::SModTrunc => tr,
        BinOp::SDivFloor => tq - i128::from(floor),
        _ => {
            if floor {
                tr + sb
            } else {
                tr
            }
        }
    };
    (0..n).map(|i| (r >> i.min(127)) & 1 == 1).collect()
}

/// The barrel shifter, stage k moving by stride * 2^k, for an amount with no X bit.
fn shift(op: ShiftOp, a: &[Trit], amt: &[Trit], stride: u32) -> Vec<Trit> {
    let n = a.len();
    let fill = match op {
        ShiftOp::Shl | ShiftOp::UShr => Zero,
        ShiftOp::SShr => a.last().copied().unwrap_or(Zero),
        ShiftOp::XShr => X,
    };
    if amt.contains(&X) {
        return vec![X; n];
    }
    let mut cur = a.to_vec();
    for (k, &s) in amt.iter().enumerate() {
        let amount = 1u64.checked_shl(k as u32).and_then(|p| p.checked_mul(u64::from(stride))).unwrap_or(u64::MAX);
        let next: Vec<Trit> = (0..n)
            .map(|i| {
                let picked = if op == ShiftOp::Shl {
                    if (i as u64) >= amount {
                        cur[i - amount as usize]
                    } else {
                        fill
                    }
                } else if (i as u64).saturating_add(amount) < n as u64 {
                    cur[i + amount as usize]
                } else {
                    fill
                };
                mux(s, picked, cur[i])
            })
            .collect();
        cur = next;
    }
    cur
}

/// A library cell's output bit `o`: its function on the inputs when the cell has no state and
/// every output has one; defined only when every input is.
fn target(cell: &super::instance::LibCell, ins: &[Trit], o: usize) -> Trit {
    if cell.is_sequential || cell.seq.is_some() {
        return X;
    }
    let mut in_names: Vec<&str> = Vec::new();
    let mut outs: Vec<(&str, Option<&str>)> = Vec::new();
    for p in cell.ports.iter().filter(|p| !p.pwr_gnd) {
        let bits = p.size as usize;
        if matches!(p.direction, LibDirection::Input | LibDirection::Bidirect) {
            in_names.extend(std::iter::repeat_n(p.name.as_str(), bits));
        }
        if matches!(p.direction, LibDirection::Output | LibDirection::Bidirect) {
            let f = if p.is_bus { None } else { p.function.as_deref() };
            outs.extend(std::iter::repeat_n((p.name.as_str(), f), bits));
        }
    }
    if outs.iter().any(|(_, f)| f.is_none()) || ins.contains(&X) {
        return X;
    }
    let Some(&(_, Some(text))) = outs.get(o) else { return X };
    let Some(f) = Func::parse_in(text, |p| in_names.contains(&p)) else { return X };
    let value = |p: &str| in_names.iter().position(|&n| n == p).map(|i| ins[i] == One);
    match eval_func(&f, &value) {
        Some(v) => trit(v),
        None => X,
    }
}

/// 0 to 1, 1; no edge, 0; X otherwise.
fn rising(before: Trit, after: Trit) -> Trit {
    match (before, after) {
        (Zero, One) => One,
        (One, _) | (_, Zero) => Zero,
        _ => X,
    }
}

/// The input bits of a library cell by port name, in the `Target`'s input order.
fn input_names(cell: &super::instance::LibCell) -> Vec<&str> {
    let mut names = Vec::new();
    for p in cell.ports.iter().filter(|p| !p.pwr_gnd) {
        if matches!(p.direction, LibDirection::Input | LibDirection::Bidirect) {
            names.extend(std::iter::repeat_n(p.name.as_str(), p.size as usize));
        }
    }
    names
}

/// A flip-flop group's expression (`clocked_on`, `next_state`, `clear`, `preset`) on the inputs;
/// absent: 0.
fn seq_expr(cell: &super::instance::LibCell, ins: &[Trit], text: Option<&str>) -> Trit {
    let Some(text) = text else { return Zero };
    let names = input_names(cell);
    let Some(f) = Func::parse_in(text, |p| names.contains(&p)) else { return X };
    let value = |p: &str| names.iter().position(|&n| n == p).map(|i| ins[i]);
    eval_func3(&f, &value)
}

/// The state after an active clear (0) or preset (1); both active, or either X where it would
/// change the state, X.
fn async_state(cell: &super::instance::LibCell, ins: &[Trit], iq: Trit) -> Trit {
    let seq = cell.seq.as_ref().expect("a flip-flop");
    let clear = seq_expr(cell, ins, seq.clear.as_deref());
    let preset = seq_expr(cell, ins, seq.preset.as_deref());
    if clear == One && preset == One {
        return X;
    }
    mux(preset, One, mux(clear, Zero, iq))
}

/// Output bit `o` of a library flip-flop: its function of the state variable and its complement.
fn ff_output(cell: &super::instance::LibCell, iq: Trit, o: usize) -> Trit {
    let seq = cell.seq.as_ref().expect("a flip-flop");
    let outs: Vec<&super::instance::LibPort> =
        cell.ports.iter().filter(|p| !p.pwr_gnd && matches!(p.direction, LibDirection::Output | LibDirection::Bidirect)).collect();
    let Some(text) = outs.get(o).and_then(|p| p.function.as_deref()) else { return X };
    let iqn = format!("{}N", seq.iq);
    let Some(f) = Func::parse_in(text, |p| p == seq.iq || p == iqn) else { return X };
    let value = |p: &str| Some(if p == seq.iq { iq } else { not(iq) });
    eval_func3(&f, &value)
}

/// A Liberty expression, three-valued.
fn eval_func3(f: &Func, value: &dyn Fn(&str) -> Option<Trit>) -> Trit {
    match f {
        Func::Port(p) => value(p).unwrap_or(X),
        Func::Not(a) => not(eval_func3(a, value)),
        Func::And(a, b) => and(eval_func3(a, value), eval_func3(b, value)),
        Func::Or(a, b) => or(eval_func3(a, value), eval_func3(b, value)),
        Func::Xor(a, b) => xor(eval_func3(a, value), eval_func3(b, value)),
        Func::One => One,
        Func::Zero => Zero,
    }
}

fn eval_func(f: &Func, value: &dyn Fn(&str) -> Option<bool>) -> Option<bool> {
    Some(match f {
        Func::Port(p) => value(p)?,
        Func::Not(a) => !eval_func(a, value)?,
        Func::And(a, b) => eval_func(a, value)? & eval_func(b, value)?,
        Func::Or(a, b) => eval_func(a, value)? | eval_func(b, value)?,
        Func::Xor(a, b) => eval_func(a, value)? ^ eval_func(b, value)?,
        Func::One => true,
        Func::Zero => false,
    })
}

/// Every assignment of `width` bits drawn from 0, 1 (and X when `with_x`), least significant first.
pub(crate) fn all_values(width: usize, with_x: bool) -> Vec<Vec<Trit>> {
    let base: &[Trit] = if with_x { &[Zero, One, X] } else { &[Zero, One] };
    let mut out = vec![Vec::new()];
    for _ in 0..width {
        out = out.into_iter().flat_map(|v| base.iter().map(move |&t| [v.clone(), vec![t]].concat())).collect();
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Bundle, Const};

    fn input(g: &mut Graph, name: &str, width: u32) -> Bundle {
        g.add(Kind::Input(name.into(), width))
    }

    fn num(v: &[Trit]) -> Option<u64> {
        v.iter().enumerate().try_fold(0u64, |acc, (i, &t)| match t {
            X => None,
            t => Some(acc | (u64::from(t == One) << i)),
        })
    }

    /// One cell `y = op(a, b)` on inputs a and b of width w.
    fn binary(kind: impl Fn(Bundle, Bundle) -> Kind, w: u32) -> Graph {
        let mut g = Graph::new();
        let a = input(&mut g, "a", w);
        let b = input(&mut g, "b", w);
        let y = g.add(kind(a, b));
        g.add(Kind::Output("y".into(), y));
        g
    }

    /// Hand-computed: the dominance rules (`TritModel`: AND is 0 if either side is a defined 0,
    /// OR 1 if either is a defined 1, XOR needs both) and the mux's agreeing bits.
    #[test]
    fn bitwise_and_mux_follow_the_trit_model() {
        let g = binary(|a, b| Kind::Bin(BinOp::And, a, b), 1);
        let mut e = Eval::new(&g);
        e.set_input("a", &[Zero]);
        assert_eq!(e.output("y"), [Zero], "0 & X");
        e.set_input("a", &[One]);
        assert_eq!(e.output("y"), [X], "1 & X");
        let g = binary(|a, b| Kind::Bin(BinOp::Or, a, b), 1);
        let mut e = Eval::new(&g);
        e.set_input("b", &[One]);
        assert_eq!(e.output("y"), [One], "X | 1");
        let g = binary(|a, b| Kind::Bin(BinOp::Andnot, a, b), 1);
        let mut e = Eval::new(&g);
        e.set_input("b", &[One]);
        assert_eq!(e.output("y"), [Zero], "X & !1");
        let g = binary(|a, b| Kind::Bin(BinOp::Xor, a, b), 1);
        let mut e = Eval::new(&g);
        e.set_input("a", &[One]);
        assert_eq!(e.output("y"), [X], "1 ^ X");
        // mux with an X select: the bits both sides agree on
        let mut g = Graph::new();
        let s = input(&mut g, "s", 1);
        let a = input(&mut g, "a", 2);
        let b = input(&mut g, "b", 2);
        let y = g.add(Kind::Mux(s[0], a, b));
        g.add(Kind::Output("y".into(), y));
        let mut e = Eval::new(&g);
        e.set_input("a", &[One, Zero]);
        e.set_input("b", &[One, One]);
        assert_eq!(e.output("y"), [One, X]);
        e.set_input("s", &[Zero]);
        assert_eq!(e.output("y"), [One, One]);
    }

    /// Hand-computed: `eq` is 0 on a defined mismatch even beside an X; `adc` is defined below the
    /// first X; a shift by an X amount bit is X; `xshr` vacates X.
    #[test]
    fn word_cells_follow_the_trit_model() {
        let g = binary(|a, b| Kind::Bin(BinOp::Eq, a, b), 2);
        let mut e = Eval::new(&g);
        e.set_input("a", &[One, X]);
        e.set_input("b", &[Zero, Zero]);
        assert_eq!(e.output("y"), [Zero]);
        e.set_input("b", &[One, Zero]);
        assert_eq!(e.output("y"), [X]);
        let g = binary(|a, b| Kind::Adc(a, b, Net::ONE), 3);
        let mut e = Eval::new(&g);
        e.set_input("a", &[One, Zero, X]);
        e.set_input("b", &[Zero, One, Zero]);
        // 1 + 0 + 1 = 0 carry 1; 0 + 1 + 1 = 0 carry 1; then X
        assert_eq!(e.output("y"), [Zero, Zero, X, X]);
        // an X carry in makes every bit X, defined operands or not
        let g = binary(|a, b| Kind::Adc(a, b, Net::UNDEF), 2);
        let mut e = Eval::new(&g);
        e.set_input("a", &[One, Zero]);
        e.set_input("b", &[Zero, Zero]);
        assert_eq!(e.output("y"), [X, X, X]);
        let g = binary(|a, b| Kind::Shift(ShiftOp::XShr, a, b, 1), 4);
        let mut e = Eval::new(&g);
        e.set_input_u64("a", 4, 0b1011);
        e.set_input_u64("b", 4, 1);
        assert_eq!(e.output("y"), [One, Zero, One, X]);
        e.set_input("b", &[X, Zero, Zero, Zero]);
        assert_eq!(e.output("y"), [X, X, X, X]);
    }

    /// Every defined 4-bit pair against Rust's integers: compare, multiply, divide (a zero divisor
    /// giving X), shifts with stride 1 and 2, add with carry.
    #[test]
    fn word_cells_on_defined_inputs_are_integer_arithmetic() {
        const W: u32 = 4;
        let m = (1u64 << W) - 1;
        let sx = |v: u64| ((v << 60) as i64) >> 60;
        type Cell = Box<dyn Fn(Bundle, Bundle) -> Kind>;
        type Model = Box<dyn Fn(u64, u64) -> Option<u64>>;
        let cases: Vec<(&str, Cell, Model)> = vec![
            ("ult", Box::new(|a, b| Kind::Bin(BinOp::ULt, a, b)), Box::new(|a, b| Some(u64::from(a < b)))),
            ("slt", Box::new(|a, b| Kind::Bin(BinOp::SLt, a, b)), Box::new(move |a, b| Some(u64::from(sx(a) < sx(b))))),
            ("mul", Box::new(|a, b| Kind::Bin(BinOp::Mul, a, b)), Box::new(move |a, b| Some((a * b) & m))),
            ("udiv", Box::new(|a, b| Kind::Bin(BinOp::UDiv, a, b)), Box::new(|a, b| a.checked_div(b))),
            ("umod", Box::new(|a, b| Kind::Bin(BinOp::UMod, a, b)), Box::new(|a, b| a.checked_rem(b))),
            ("shl", Box::new(|a, b| Kind::Shift(ShiftOp::Shl, a, b, 1)), Box::new(move |a, b| Some(a.checked_shl(b as u32).unwrap_or(0) & m))),
            ("ushr2", Box::new(|a, b| Kind::Shift(ShiftOp::UShr, a, b, 2)), Box::new(|a, b| Some(a.checked_shr(2 * b as u32).unwrap_or(0)))),
            ("sshr", Box::new(|a, b| Kind::Shift(ShiftOp::SShr, a, b, 1)), Box::new(move |a, b| Some((sx(a) >> b.min(63)) as u64 & m))),
            ("adc", Box::new(|a, b| Kind::Adc(a, b, Net::ZERO)), Box::new(|a, b| Some(a + b))),
        ];
        for (name, kind, want) in cases {
            let g = binary(kind, W);
            let mut e = Eval::new(&g);
            for a in 0..=m {
                for b in 0..=m {
                    e.set_input_u64("a", W, a);
                    e.set_input_u64("b", W, b);
                    assert_eq!(num(&e.output("y")), want(a, b), "{name} a={a} b={b}");
                }
            }
        }
    }

    /// The evaluator against the D1 model (`flow::bitblast`'s exhaustive divmod test): every
    /// division and modulo cell, every 4-bit pair, before and after `bitblast_divmod`. Equal where
    /// the cell is defined; a zero divisor (X here) is bit-blasted to Yosys's values.
    #[test]
    fn division_agrees_with_its_bitblast() {
        const W: u32 = 4;
        let ops = [BinOp::UDiv, BinOp::UMod, BinOp::SDivTrunc, BinOp::SModTrunc, BinOp::SDivFloor, BinOp::SModFloor];
        for op in ops {
            let g = binary(|a, b| Kind::Bin(op, a, b), W);
            let mut lowered = g.clone();
            assert_eq!(crate::flow::bitblast::bitblast_divmod(&mut lowered), 1);
            let (mut e, mut l) = (Eval::new(&g), Eval::new(&lowered));
            for a in 0..1u64 << W {
                for b in 0..1u64 << W {
                    for x in [&mut e, &mut l] {
                        x.set_input_u64("a", W, a);
                        x.set_input_u64("b", W, b);
                    }
                    let (want, got) = (e.output("y"), l.output("y"));
                    assert!(got.iter().all(|&t| t != X), "{} a={a} b={b}: the bit-blast is defined", op.keyword());
                    if b == 0 {
                        assert_eq!(want, vec![X; W as usize], "{} a={a} by zero", op.keyword());
                    } else {
                        assert_eq!(want, got, "{} a={a} b={b}", op.keyword());
                    }
                }
            }
        }
    }

    /// A register: initial value, takes its data on a step, holds when disabled, follows an active
    /// clear at once; a loop through a breaker settles to X.
    #[test]
    fn registers_step_and_loops_are_x() {
        let mut g = Graph::new();
        let d = input(&mut g, "d", 1);
        let en = input(&mut g, "en", 1);
        let clr = input(&mut g, "clr", 1);
        let q = g.add(Kind::Dff(Box::new(crate::ir::instance::Dff {
            data: d,
            clock: ControlNet::pos(Net::UNDEF),
            clear: ControlNet::neg(clr[0]),
            reset: ControlNet::ZERO,
            enable: ControlNet::pos(en[0]),
            init_value: Const::from([Zero]),
            reset_value: Const::from([X]),
            clear_value: Const::from([One]),
        })));
        g.add(Kind::Output("q".into(), q));
        let mut e = Eval::new(&g);
        e.set_input("clr", &[One]);
        e.set_input("en", &[One]);
        e.set_input("d", &[One]);
        assert_eq!(e.output("q"), [Zero], "the initial value");
        e.step();
        assert_eq!(e.output("q"), [One]);
        e.set_input("en", &[Zero]);
        e.set_input("d", &[Zero]);
        e.step();
        assert_eq!(e.output("q"), [One], "held");
        e.set_input("en", &[One]);
        e.step();
        assert_eq!(e.output("q"), [Zero]);
        e.set_input("clr", &[Zero]);
        assert_eq!(e.output("q"), [One], "the clear value, at once");
        // y = a | (y & b) through a loop breaker: 1 when a is, else X (it depends on itself)
        let mut g = Graph::new();
        let a = input(&mut g, "a", 1);
        let b = input(&mut g, "b", 1);
        let lb = g.add(Kind::LoopBreaker(vec![Net::UNDEF]));
        let and = g.add(Kind::Bin(BinOp::And, lb.clone(), b));
        let y = g.add(Kind::Bin(BinOp::Or, a, and));
        let (id, _) = g.resolve(lb[0]);
        g.inst_mut(id).kind = Kind::LoopBreaker(y.clone());
        g.add(Kind::Output("y".into(), y));
        let mut e = Eval::new(&g);
        e.set_input("b", &[One]);
        e.set_input("a", &[One]);
        assert_eq!(e.output("y"), [One]);
        e.set_input("a", &[Zero]);
        assert_eq!(e.output("y"), [X]);
        e.set_input("b", &[Zero]);
        assert_eq!(e.output("y"), [Zero], "the loop's AND is 0");
    }

    /// The truth-table helper enumerates 3^w assignments with X.
    #[test]
    fn all_values_counts() {
        assert_eq!(all_values(3, true).len(), 27);
        assert_eq!(all_values(4, false).len(), 16);
    }
}
