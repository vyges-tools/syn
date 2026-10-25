// SPDX-License-Identifier: Apache-2.0
//! Liveness: which values a net can ever take, four-valued, and registers (optionally any cell)
//! that can never carry anything replaced by a constant.
//!
//! Every net starts at U (only ever X); inputs, dangling nets and opaque or library cells' outputs
//! are A (anything). Values propagate through the cells, in slot order and in place, until a sweep
//! changes nothing.

use crate::ir::instance::{BinOp, Dff, ShiftOp};
use crate::ir::net::{Net, Trit};
use crate::ir::{Graph, Kind};

/// What a net can be: bit 0 "can be 0", bit 1 "can be 1"; X always.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
enum State {
    U = 0,
    Zero = 1,
    One = 2,
    A = 3,
}

impl State {
    fn from_bits(b: u8) -> State {
        match b & 3 {
            0 => State::U,
            1 => State::Zero,
            2 => State::One,
            _ => State::A,
        }
    }
    fn can(self, s: State) -> bool {
        self as u8 & s as u8 != 0
    }
    fn join(self, o: State) -> State {
        State::from_bits(self as u8 | o as u8)
    }
}

fn not(a: State) -> State {
    match a {
        State::Zero => State::One,
        State::One => State::Zero,
        s => s,
    }
}

fn and(a: State, b: State) -> State {
    let can_be_1 = a.can(State::One) && b.can(State::One);
    let can_be_0 = a.can(State::Zero) || b.can(State::Zero);
    State::from_bits((can_be_1 as u8) << 1 | can_be_0 as u8)
}

fn or(a: State, b: State) -> State {
    not(and(not(a), not(b)))
}

fn andnot(a: State, b: State) -> State {
    and(a, not(b))
}

fn xor(a: State, b: State) -> State {
    let (a0, a1, b0, b1) = (a.can(State::Zero), a.can(State::One), b.can(State::Zero), b.can(State::One));
    let can_be_0 = (a0 && b0) || (a1 && b1);
    let can_be_1 = (a0 && b1) || (a1 && b0);
    State::from_bits((can_be_1 as u8) << 1 | can_be_0 as u8)
}

/// select 1 chooses `a`, 0 chooses `b`.
fn mux(s: State, a: State, b: State) -> State {
    let (s0, s1) = (s.can(State::Zero), s.can(State::One));
    let can_be_0 = (s1 && a.can(State::Zero)) || (s0 && b.can(State::Zero)) || (a.can(State::Zero) && b.can(State::Zero));
    let can_be_1 = (s1 && a.can(State::One)) || (s0 && b.can(State::One)) || (a.can(State::One) && b.can(State::One));
    State::from_bits((can_be_1 as u8) << 1 | can_be_0 as u8)
}

fn trit_net(t: Trit) -> Net {
    Net::from_trit(t)
}

struct LivenessAnalysis {
    values: Vec<State>,
}

/// Cells whose outputs are pinned at A: the design's inputs, dangling nets, opaque and library cells.
fn is_boundary(kind: &Kind) -> bool {
    matches!(kind, Kind::Input(..) | Kind::Dangling(_) | Kind::Other(_) | Kind::Target(..))
}

impl LivenessAnalysis {
    fn new(g: &Graph) -> Self {
        let mut values = vec![State::U; g.table_size() as usize];
        values[0] = State::Zero;
        values[1] = State::One;
        values[2] = State::U;
        let mut it = g.instances();
        while let Some(id) = it.next(g) {
            if is_boundary(&g.inst(id).kind) {
                for n in g.output(id) {
                    values[n.0 as usize] = State::A;
                }
            }
        }
        LivenessAnalysis { values }
    }

    fn value_of(&self, n: Net) -> State {
        self.values[n.0 as usize]
    }

    fn run(&mut self, g: &Graph) {
        while self.step_once(g) {}
    }

    /// One sweep; whether any value changed.
    fn step_once(&mut self, g: &Graph) -> bool {
        let mut changed = false;
        let mut it = g.instances();
        while let Some(id) = it.next(g) {
            self.compute_outputs(g, id, &mut changed);
        }
        changed
    }

    fn compute_outputs(&mut self, g: &Graph, id: crate::ir::graph::InstId, changed: &mut bool) {
        let kind = &g.inst(id).kind;
        if is_boundary(kind) || matches!(kind, Kind::TieLow | Kind::TieHigh | Kind::TieX) {
            return;
        }
        let out = g.output(id);
        if out.is_empty() {
            return;
        }
        // ⚠️ Each bit is written as it is computed: a later bit of the same cell reads the new
        // value of an earlier one (a register's Q feeding its own D, a loop breaker).
        match kind {
            Kind::Buffer(a) | Kind::LoopBreaker(a) => self.set_each(&out, changed, |s, i| s.value_of(a[i])),
            Kind::Not(a) => self.set_each(&out, changed, |s, i| not(s.value_of(a[i]))),
            Kind::Bin(op @ (BinOp::And | BinOp::Or | BinOp::Andnot | BinOp::Xor), a, b) => {
                let f = match op {
                    BinOp::And => and,
                    BinOp::Or => or,
                    BinOp::Andnot => andnot,
                    _ => xor,
                };
                self.set_each(&out, changed, |s, i| f(s.value_of(a[i]), s.value_of(b[i])))
            }
            Kind::Mux(sel, a, b) => {
                let sel = self.value_of(*sel);
                self.set_each(&out, changed, |s, i| mux(sel, s.value_of(a[i]), s.value_of(b[i])))
            }
            Kind::Shift(op @ (ShiftOp::UShr | ShiftOp::XShr | ShiftOp::SShr), a, b, stride) => {
                let cur = self.compute_shr(*op, a, b, *stride, out.len());
                self.set_each(&out, changed, |_, i| cur[i])
            }
            Kind::Dff(dff) => self.set_each(&out, changed, |s, i| s.dff_bit(dff, &out, i)),
            // over-approximated: anything that can be other than X makes the output anything
            _ => {
                let merged = kind.inputs().iter().fold(State::U, |r, &n| r.join(self.value_of(n)));
                let v = if merged == State::U { State::U } else { State::A };
                self.set_each(&out, changed, |_, _| v)
            }
        }
    }

    fn set_each(&mut self, out: &[Net], changed: &mut bool, f: impl Fn(&Self, usize) -> State) {
        for (i, n) in out.iter().enumerate() {
            let v = f(self, i);
            let slot = &mut self.values[n.0 as usize];
            if *slot != v {
                *slot = v;
                *changed = true;
            }
        }
    }

    fn compute_shr(&self, op: ShiftOp, a: &[Net], b: &[Net], stride: u32, n: usize) -> Vec<State> {
        let fill = match op {
            ShiftOp::UShr => State::Zero,
            ShiftOp::XShr => State::U,
            _ => a.last().map_or(State::U, |&s| self.value_of(s)),
        };
        let mut cur: Vec<State> = (0..n).map(|i| if i < a.len() { self.value_of(a[i]) } else { fill }).collect();
        for (k, &bk) in b.iter().enumerate() {
            let s = self.value_of(bk);
            // a 32-bit amount, its shift count taken mod 32 as the machine does
            let amount = stride.wrapping_mul(1u32.wrapping_shl(k as u32)) as u64;
            cur = (0..n).map(|i| mux(s, if i as u64 + amount < n as u64 { cur[i + amount as usize] } else { fill }, cur[i])).collect();
        }
        cur
    }

    /// Q joins its old value, D, the initial value, and the reset and clear values when they can fire.
    fn dff_bit(&self, dff: &Dff, out: &[Net], i: usize) -> State {
        let mut v = self.value_of(out[i]);
        v = v.join(dff.data.get(i).map_or(State::U, |&d| self.value_of(d)));
        v = v.join(self.value_of(trit_net(dff.init_value[i])));
        if !dff.reset.is_always(false) {
            v = v.join(self.value_of(trit_net(dff.reset_value[i])));
        }
        if !dff.clear.is_always(false) {
            v = v.join(self.value_of(trit_net(dff.clear_value[i])));
        }
        v
    }
}

fn net_for_state(v: State) -> Option<Net> {
    match v {
        State::U => Some(Net::UNDEF),
        State::Zero => Some(Net::ZERO),
        State::One => Some(Net::ONE),
        State::A => None,
    }
}

/// Normalizes, runs the analysis, then ties every register bit (and, with `replace_combinational`,
/// every other cell's bit) that can never be anything to the constant it can be — registers first,
/// each list in slot order — and normalizes again if anything was tied. Returns the counts tied:
/// (register bits, combinational bits).
pub fn liveness_opt(g: &mut Graph, replace_combinational: bool) -> (usize, usize) {
    g.normalize();
    let mut analysis = LivenessAnalysis::new(g);
    analysis.run(g);

    let mut reg_repls = Vec::new();
    let mut comb_repls = Vec::new();
    let mut it = g.instances();
    while let Some(id) = it.next(g) {
        let kind = &g.inst(id).kind;
        if matches!(
            kind,
            Kind::Input(..)
                | Kind::Dangling(_)
                | Kind::Output(..)
                | Kind::Name(_)
                | Kind::TieLow
                | Kind::TieHigh
                | Kind::TieX
                | Kind::Other(_)
        ) {
            continue;
        }
        let is_register = match kind {
            Kind::Dff(_) => true,
            Kind::Target(cell, _) => cell.is_sequential,
            _ => false,
        };
        if !is_register && !replace_combinational {
            continue;
        }
        for n in g.output(id) {
            let Some(rep) = net_for_state(analysis.value_of(n)) else { continue };
            if n == rep {
                continue;
            }
            if is_register {
                reg_repls.push((n, rep));
            } else {
                comb_repls.push((n, rep));
            }
        }
    }
    for &(t, r) in reg_repls.iter().chain(&comb_repls) {
        g.force_replace(&[t], &[r]);
    }
    if !reg_repls.is_empty() || !comb_repls.is_empty() {
        g.normalize();
    }
    (reg_repls.len(), comb_repls.len())
}

#[cfg(test)]
mod tests {
    use super::*;

    // Rule: the four values are "can be 0" / "can be 1" bit sets with X always possible; AND can be
    // 1 only when both can, 0 when either can; XOR by the four input pairs; a mux takes the
    // selected side, and a value both sides share whatever the select.
    #[test]
    fn four_valued_operators() {
        use State::*;
        assert_eq!(and(One, A), A);
        assert_eq!(and(Zero, A), Zero);
        assert_eq!(and(U, A), Zero);
        assert_eq!(and(U, U), U);
        assert_eq!(or(One, U), One);
        assert_eq!(xor(One, One), Zero);
        assert_eq!(xor(One, A), A);
        assert_eq!(xor(U, A), U);
        assert_eq!(mux(U, One, One), One);
        assert_eq!(mux(U, One, Zero), U);
        assert_eq!(mux(One, Zero, One), Zero);
        assert_eq!(andnot(One, Zero), One);
    }
}
