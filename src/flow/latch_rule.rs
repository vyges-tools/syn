// SPDX-License-Identifier: Apache-2.0
//! The latch rule: a variable whose next value is a mux tree that can select the variable itself
//! holds its value under the selects that lead there, and is transparent otherwise.
//!
//! This is the rule of Yosys `proc_dlatch` (`passes/proc/proc_dlatch.cc`): `find_mux_feedback`
//! walks the mux tree driving an assignment, from the assigned value down through mux inputs only
//! (never through a select), looking for the assigned signal itself; each path that reaches it is
//! the conjunction of the selects along it (a mux's `B` side matched as 1, its `A` side as 0, a
//! `$pmux`/slot select matched as its slot's value). `make_hold` builds the disjunction of the
//! paths: the hold condition. The latch is then `$dlatch(EN = !hold, D = rhs, Q = lhs)`, the
//! feedback inputs set to `x`, and `fixup_mux` drops each mux input that became all `x`, so the
//! data input is the value the tree takes when it does not hold. The slang frontend the reference
//! flow runs (non-mux-lowering build) creates the same `$dlatch` itself for an `always_latch`.
//!
//! Our frontend is built with mux lowering, which emits the latch as the feedback mux tree; this
//! module turns that tree back into the hold condition and the data input. It depends on nothing
//! but `std`, so the formal harness copies it verbatim (see `latch_inference` for the graph side).
//! Two differences from the letter of Yosys, neither visible in the latch's behaviour: the data
//! input is BUILT (new cells along the feedback paths) rather than the tree edited in place, so a
//! tree another signal also reads is never changed (Yosys keeps such a feedback input instead of
//! `x`, `sigusers > 1`); and the slot form (`bmux`, a right shift by a select) is walked as a
//! `$pmux` whose slot `k` is matched as `sel == k`, as mux lowering builds an `if`/`case` that way.

/// What drives a net, as the walk sees it.
pub enum Node<N> {
    /// The signal the assignment drives (the feedback).
    Needle,
    /// Passes its one input through (a placeholder or a buffer: Yosys `sigmap` sees one net).
    Alias(N),
    /// `sel ? one : zero`.
    Mux { sel: N, one: N, zero: N },
    /// Slot `k` of `slots` when `sel` (least significant first) equals `k`.
    Slots { sel: Vec<N>, slots: Vec<N> },
    /// Anything else: the walk stops here.
    Leaf,
}

/// The graph the rule reads and builds into.
pub trait LatchGraph {
    type Net: Copy + Ord;
    fn node(&self, net: Self::Net) -> Node<Self::Net>;
    fn one(&self) -> Self::Net;
    fn undef(&self) -> Self::Net;
    fn not(&mut self, a: Self::Net) -> Self::Net;
    fn and(&mut self, a: Self::Net, b: Self::Net) -> Self::Net;
    fn or(&mut self, a: Self::Net, b: Self::Net) -> Self::Net;
    /// `sel == k`, one bit.
    fn eq_const(&mut self, sel: &[Self::Net], k: usize) -> Self::Net;
    fn mux(&mut self, sel: Self::Net, one: Self::Net, zero: Self::Net) -> Self::Net;
    fn slots(&mut self, sel: &[Self::Net], slots: &[Self::Net]) -> Self::Net;
}

/// A latch: it holds while `hold` is 1, and passes `data` while it is 0.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Latch<N> {
    pub hold: N,
    pub data: N,
}

/// One search: each net's result, sorted by net (a plain sorted `Vec`, so the formal harness's
/// bounded model checker need not model a tree map), and the nets on the current path (a cycle
/// that does not pass through the needle reaches nothing).
struct Search<N> {
    memo: Vec<(N, Option<(N, N)>)>,
    on_path: Vec<N>,
}

/// `proc_dlatch` for one assigned bit: the latch when the tree driving it (`rhs`) can select the
/// bit itself, `None` when it cannot (no latch: the assignment is combinational).
pub fn proc_dlatch<G: LatchGraph>(g: &mut G, rhs: G::Net) -> Option<Latch<G::Net>> {
    let mut s = Search { memo: Vec::new(), on_path: Vec::new() };
    let (hold, data) = find_mux_feedback(g, &mut s, rhs)?;
    Some(Latch { hold, data })
}

/// `find_mux_feedback` + `make_hold` + `fixup_mux` in one walk: for `net`, when some mux path
/// from it reaches the needle, the hold condition of those paths and the value `net` takes when
/// none of them is selected (`undef` where it is the needle itself).
fn find_mux_feedback<G: LatchGraph>(g: &mut G, s: &mut Search<G::Net>, net: G::Net) -> Option<(G::Net, G::Net)> {
    if let Ok(i) = s.memo.binary_search_by(|e| e.0.cmp(&net)) {
        return s.memo[i].1;
    }
    if s.on_path.contains(&net) {
        return None;
    }
    s.on_path.push(net);
    let r = match g.node(net) {
        Node::Needle => Some((g.one(), g.undef())),
        Node::Leaf => None,
        Node::Alias(a) => find_mux_feedback(g, s, a),
        Node::Mux { sel, one, zero } => {
            let f1 = find_mux_feedback(g, s, one);
            let f0 = find_mux_feedback(g, s, zero);
            if f1.is_none() && f0.is_none() {
                None
            } else {
                let mut terms = Vec::new();
                if let Some((h, _)) = f1 {
                    terms.push(make_inner(g, sel, h));
                }
                if let Some((h, _)) = f0 {
                    let ns = g.not(sel);
                    terms.push(make_inner(g, ns, h));
                }
                let hold = make_or(g, &terms);
                let d1 = f1.map_or(one, |f| f.1);
                let d0 = f0.map_or(zero, |f| f.1);
                let undef = g.undef();
                let data = if d1 == undef {
                    d0
                } else if d0 == undef || d1 == d0 {
                    d1
                } else {
                    g.mux(sel, d1, d0)
                };
                Some((hold, data))
            }
        }
        Node::Slots { sel, slots } => {
            let found: Vec<Option<(G::Net, G::Net)>> = slots.iter().map(|&x| find_mux_feedback(g, s, x)).collect();
            if found.iter().all(|f| f.is_none()) {
                None
            } else {
                let mut terms = Vec::new();
                for (k, f) in found.iter().enumerate() {
                    if let Some((h, _)) = *f {
                        let eq = g.eq_const(&sel, k);
                        terms.push(make_inner(g, eq, h));
                    }
                }
                let hold = make_or(g, &terms);
                let data: Vec<G::Net> = slots.iter().zip(&found).map(|(&x, f)| f.map_or(x, |f| f.1)).collect();
                Some((hold, fixup_slots(g, &sel, &data)))
            }
        }
    };
    s.on_path.pop();
    // not there yet: a net is entered once, and a re-entry on its own path is not memoized
    let at = s.memo.binary_search_by(|e| e.0.cmp(&net)).unwrap_or_else(|i| i);
    s.memo.insert(at, (net, r));
    r
}

/// A path's condition: `cond` and the hold below it (`make_hold`'s AND of a rule node).
fn make_inner<G: LatchGraph>(g: &mut G, cond: G::Net, below: G::Net) -> G::Net {
    if below == g.one() {
        cond
    } else {
        g.and(cond, below)
    }
}

/// The paths' disjunction (`make_hold`'s `ReduceOr` of a node's children); never empty.
fn make_or<G: LatchGraph>(g: &mut G, terms: &[G::Net]) -> G::Net {
    let mut acc = terms[0];
    for &t in &terms[1..] {
        acc = g.or(acc, t);
    }
    acc
}

/// `fixup_mux` for the slot form: slots that are `undef` dropped, filled with a valid slot (as
/// `fixup_mux` gives an all-`x` `A` a valid `B`); one valid value left is that value.
fn fixup_slots<G: LatchGraph>(g: &mut G, sel: &[G::Net], data: &[G::Net]) -> G::Net {
    let undef = g.undef();
    let mut valid = data.iter().copied().filter(|&d| d != undef);
    let Some(first) = valid.next() else { return undef };
    if valid.all(|d| d == first) {
        return first;
    }
    let filled: Vec<G::Net> = data.iter().map(|&d| if d == undef { first } else { d }).collect();
    g.slots(sel, &filled)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A tiny arena: inputs, the needle, constants, and the cells the rule builds.
    #[derive(Clone)]
    enum C {
        In(usize),
        Needle,
        One,
        Zero,
        Undef,
        Not(usize),
        And(usize, usize),
        Or(usize, usize),
        Eq(Vec<usize>, usize),
        Mux(usize, usize, usize),
        Slots(Vec<usize>, Vec<usize>),
    }
    struct A(Vec<C>);
    impl A {
        fn push(&mut self, c: C) -> usize {
            self.0.push(c);
            self.0.len() - 1
        }
        /// The value at `n`: inputs from `ins`, the needle `q`, `undef` as 0 (the test asks only
        /// where it does not matter).
        fn eval(&self, n: usize, ins: &[bool], q: bool) -> bool {
            match &self.0[n] {
                C::In(i) => ins[*i],
                C::Needle => q,
                C::One => true,
                C::Zero | C::Undef => false,
                C::Not(a) => !self.eval(*a, ins, q),
                C::And(a, b) => self.eval(*a, ins, q) && self.eval(*b, ins, q),
                C::Or(a, b) => self.eval(*a, ins, q) || self.eval(*b, ins, q),
                C::Eq(s, k) => s.iter().enumerate().all(|(i, &b)| self.eval(b, ins, q) == ((k >> i) & 1 == 1)),
                C::Mux(s, a, b) => if self.eval(*s, ins, q) { self.eval(*a, ins, q) } else { self.eval(*b, ins, q) },
                C::Slots(s, v) => {
                    let k = s.iter().enumerate().fold(0, |acc, (i, &b)| acc | (usize::from(self.eval(b, ins, q)) << i));
                    self.eval(v[k], ins, q)
                }
            }
        }
    }
    impl LatchGraph for A {
        type Net = usize;
        fn node(&self, n: usize) -> Node<usize> {
            match &self.0[n] {
                C::Needle => Node::Needle,
                C::Mux(s, a, b) => Node::Mux { sel: *s, one: *a, zero: *b },
                C::Slots(s, v) => Node::Slots { sel: s.clone(), slots: v.clone() },
                _ => Node::Leaf,
            }
        }
        fn one(&self) -> usize {
            2
        }
        fn undef(&self) -> usize {
            4
        }
        fn not(&mut self, a: usize) -> usize {
            self.push(C::Not(a))
        }
        fn and(&mut self, a: usize, b: usize) -> usize {
            self.push(C::And(a, b))
        }
        fn or(&mut self, a: usize, b: usize) -> usize {
            self.push(C::Or(a, b))
        }
        fn eq_const(&mut self, sel: &[usize], k: usize) -> usize {
            self.push(C::Eq(sel.to_vec(), k))
        }
        fn mux(&mut self, s: usize, a: usize, b: usize) -> usize {
            self.push(C::Mux(s, a, b))
        }
        fn slots(&mut self, sel: &[usize], v: &[usize]) -> usize {
            self.push(C::Slots(sel.to_vec(), v.to_vec()))
        }
    }
    /// 0..3 inputs, 4 the needle... laid out so `one()`/`undef()` above hold.
    fn arena() -> A {
        A(vec![C::In(0), C::In(1), C::One, C::Zero, C::Undef, C::Needle, C::In(2), C::In(3)])
    }

    /// Yosys `proc_dlatch` rule, on the ClockGate form mux lowering emits for
    /// `always_latch if (!clk) q = d;`: slot 1 (`!clk` true) is `d`, slot 0 the feedback. The
    /// hold is `!clk == 0`, the data `d`, not the tree (`fixup_mux`: the `x` slot is dropped).
    /// Then over every input and previous value, the latch equals the tree read with the
    /// previous value at the feedback.
    #[test]
    fn clock_gate_slots_hold_on_the_feedback_slot_and_pass_the_other() {
        let mut a = arena();
        let nclk = a.push(C::Not(0));
        let tree = a.push(C::Slots(vec![nclk], vec![5, 1]));
        let l = proc_dlatch(&mut a, tree).expect("a latch");
        assert_eq!(l.data, 1, "data is d itself");
        for v in 0..8u32 {
            let ins = [v & 1 == 1, v & 2 == 2, false, false];
            let q = v & 4 == 4;
            let latched = if a.eval(l.hold, &ins, q) { q } else { a.eval(l.data, &ins, q) };
            assert_eq!(latched, a.eval(tree, &ins, q), "clk={} d={} q={q}", ins[0], ins[1]);
        }
    }

    /// Yosys `find_mux_feedback`: a nested if (`if (a) begin if (b) q = c; end`) holds on both
    /// paths to the feedback (`!a`, and `a & !b`), and passes `c` otherwise.
    #[test]
    fn nested_mux_holds_on_every_path_to_the_feedback() {
        let mut a = arena();
        let inner = a.push(C::Mux(1, 6, 5));
        let tree = a.push(C::Mux(0, inner, 5));
        let l = proc_dlatch(&mut a, tree).expect("a latch");
        assert_eq!(l.data, 6);
        for v in 0..16u32 {
            let ins = [v & 1 == 1, v & 2 == 2, v & 4 == 4, false];
            let q = v & 8 == 8;
            let latched = if a.eval(l.hold, &ins, q) { q } else { a.eval(l.data, &ins, q) };
            assert_eq!(latched, a.eval(tree, &ins, q));
            assert_eq!(a.eval(l.hold, &ins, q), !(ins[0] && ins[1]));
        }
    }

    /// Yosys: a tree that never selects the signal itself infers no latch.
    #[test]
    fn no_feedback_no_latch() {
        let mut a = arena();
        let tree = a.push(C::Mux(0, 1, 6));
        assert!(proc_dlatch(&mut a, tree).is_none());
    }
}
