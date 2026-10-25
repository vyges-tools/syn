// SPDX-License-Identifier: Apache-2.0
//! Bitblasting: arithmetic, comparisons, shifts, muxes and the wide bitwise cells become one-bit
//! AND / ANDNOT / OR gates (and inverters where a literal is used negated).
//!
//! Gates are built through one structurally hashed AND over literals (a net and a polarity), with
//! the two-level AIG rewrite rules of Brummayer & Biere (MEMICS'06, Table 2) applied first. The
//! hash is shared by every cell of the pass. A literal is used as its net, an inverter added each
//! time a negative one is used.

use std::collections::BTreeMap;

use crate::ir::graph::Equivalence;
use crate::ir::instance::{BinOp, ShiftOp};
use crate::ir::net::{Bundle, ControlNet as Literal, Net};
use crate::ir::{Graph, Kind};

type LitPair = (Literal, Literal);

fn not(l: Literal) -> Literal {
    Literal::with_polarity(l.net, !l.positive)
}

/// A literal that is the output of an AND (as an And, Andnot or Or gate): its two children and
/// whether the literal is the AND's complement.
struct AndDec {
    left: Literal,
    right: Literal,
    neg: bool,
}

/// One cell, bitblasted: its replacement nets, built into `g`.
struct Bitblasted<'a> {
    g: &'a mut Graph,
    and_cache: &'a mut BTreeMap<LitPair, Literal>,
    replacement: Bundle,
}

impl Bitblasted<'_> {
    fn decompose(&self, lit: Literal) -> Option<AndDec> {
        let (id, off) = self.g.resolve(lit.net);
        let off = off as usize;
        match &self.g.inst(id).kind {
            Kind::Bin(BinOp::And, a, b) => {
                Some(AndDec { left: Literal::pos(a[off]), right: Literal::pos(b[off]), neg: !lit.positive })
            }
            Kind::Bin(BinOp::Andnot, a, b) => {
                Some(AndDec { left: Literal::pos(a[off]), right: Literal::neg(b[off]), neg: !lit.positive })
            }
            // Or(a, b) = NOT(AND(NOT a, NOT b))
            Kind::Bin(BinOp::Or, a, b) => {
                Some(AndDec { left: Literal::neg(a[off]), right: Literal::neg(b[off]), neg: lit.positive })
            }
            _ => None,
        }
    }

    #[allow(non_snake_case)]
    fn AND(&mut self, a: Literal, b: Literal) -> Literal {
        // ---- level 1: single-level rules ----
        if a.is_always(false) || b.is_always(false) {
            return Literal::ZERO;
        }
        if a.is_always(true) {
            return b;
        }
        if b.is_always(true) {
            return a;
        }
        if a == not(b) {
            return Literal::ZERO;
        }
        if a == b {
            return a;
        }

        // ---- level 2: two-level rules ----
        let da = self.decompose(a);
        let db = self.decompose(b);

        // a = AND(p, q), b a leaf
        if let Some(d) = da.as_ref().filter(|d| !d.neg) {
            if d.left == not(b) || d.right == not(b) {
                return Literal::ZERO;
            }
            if d.left == b || d.right == b {
                return a;
            }
        }
        // a = NOT(AND(p, q)), b a leaf
        if let Some(d) = da.as_ref().filter(|d| d.neg) {
            if d.left == not(b) || d.right == not(b) {
                return b;
            }
            if d.right == b {
                return self.AND(not(d.left), b);
            }
            if d.left == b {
                return self.AND(not(d.right), b);
            }
        }
        // b = AND(r, s), a a leaf
        if let Some(d) = db.as_ref().filter(|d| !d.neg) {
            if d.left == not(a) || d.right == not(a) {
                return Literal::ZERO;
            }
            if d.left == a || d.right == a {
                return b;
            }
        }
        // b = NOT(AND(r, s)), a a leaf
        if let Some(d) = db.as_ref().filter(|d| d.neg) {
            if d.left == not(a) || d.right == not(a) {
                return a;
            }
            if d.right == a {
                return self.AND(a, not(d.left));
            }
            if d.left == a {
                return self.AND(a, not(d.right));
            }
        }

        // both children ANDs
        if let (Some(da), Some(db)) = (&da, &db) {
            let cross = |x: &AndDec, y: &AndDec| {
                x.left == not(y.left) || x.left == not(y.right) || x.right == not(y.left) || x.right == not(y.right)
            };
            if !da.neg && !db.neg {
                if cross(da, db) {
                    return Literal::ZERO;
                }
                if da.left == db.left || da.right == db.left {
                    return self.AND(a, db.right);
                }
                if da.left == db.right || da.right == db.right {
                    return self.AND(a, db.left);
                }
            }
            if da.neg && !db.neg {
                if cross(da, db) {
                    return b;
                }
                if da.right == db.left || da.right == db.right {
                    return self.AND(not(da.left), b);
                }
                if da.left == db.left || da.left == db.right {
                    return self.AND(not(da.right), b);
                }
            }
            if !da.neg && db.neg {
                if db.left == not(da.left) || db.left == not(da.right) || db.right == not(da.left) || db.right == not(da.right) {
                    return a;
                }
                if db.right == da.left || db.right == da.right {
                    return self.AND(a, not(db.left));
                }
                if db.left == da.left || db.left == da.right {
                    return self.AND(a, not(db.right));
                }
            }
            if da.neg && db.neg {
                if da.left == db.right && da.right == not(db.left) {
                    return not(da.left);
                }
                if da.left == db.left && da.right == not(db.right) {
                    return not(da.left);
                }
                if da.right == db.right && da.left == not(db.left) {
                    return not(da.right);
                }
                if da.right == db.left && da.left == not(db.right) {
                    return not(da.right);
                }
            }
        }

        // ---- the hash, or a new gate ----
        let key = if a < b { (a, b) } else { (b, a) };
        if let Some(&r) = self.and_cache.get(&key) {
            return r;
        }
        let gate = |op, x: Net, y: Net| Kind::Bin(op, vec![x], vec![y]);
        let result = match (a.positive, b.positive) {
            (true, true) => Literal::pos(self.g.add(gate(BinOp::And, a.net, b.net))[0]),
            (true, false) => Literal::pos(self.g.add(gate(BinOp::Andnot, a.net, b.net))[0]),
            (false, true) => Literal::pos(self.g.add(gate(BinOp::Andnot, b.net, a.net))[0]),
            (false, false) => Literal::neg(self.g.add(gate(BinOp::Or, a.net, b.net))[0]),
        };
        self.and_cache.insert(key, result);
        result
    }

    #[allow(non_snake_case)]
    fn OR(&mut self, a: Literal, b: Literal) -> Literal {
        let r = self.AND(not(a), not(b));
        not(r)
    }

    #[allow(non_snake_case)]
    fn XOR(&mut self, a: Literal, b: Literal) -> Literal {
        let x = self.AND(a, not(b));
        let y = self.AND(not(a), b);
        self.OR(x, y)
    }

    #[allow(non_snake_case)]
    fn MUX(&mut self, sel: Literal, a: Literal, b: Literal) -> Literal {
        let x = self.AND(sel, a);
        let y = self.AND(not(sel), b);
        self.OR(x, y)
    }

    /// Ripple carry: the n sums, then the carry out.
    fn ripple_adder(&mut self, a: &[Literal], b: &[Literal], cin: Literal) -> Vec<Literal> {
        let mut result = Vec::with_capacity(a.len() + 1);
        let mut carry = cin;
        for i in 0..a.len() {
            let ab = self.XOR(a[i], b[i]);
            result.push(self.XOR(ab, carry));
            let x = self.AND(a[i], b[i]);
            let y = self.AND(carry, ab);
            carry = self.OR(x, y);
        }
        result.push(carry);
        result
    }

    /// Han-Carlson parallel prefix (ripple carry up to 4 bits): the n sums, then the carry out.
    fn adder(&mut self, a: &[Literal], b: &[Literal], cin: Literal) -> Vec<Literal> {
        let n = a.len();
        if n <= 4 {
            return self.ripple_adder(a, b, cin);
        }
        let mut g = vec![Literal::ZERO; n];
        let mut p = vec![Literal::ZERO; n];
        for i in 0..n {
            p[i] = self.XOR(a[i], b[i]);
            g[i] = self.AND(a[i], b[i]);
        }
        // the carry in, into position 0
        let pc = self.AND(p[0], cin);
        g[0] = self.OR(g[0], pc);

        let mut levels = 0;
        let mut v = n;
        while v > 1 {
            levels += 1;
            v = v.div_ceil(2);
        }
        // the odd positions from their even neighbour
        for j in (1..n).step_by(2) {
            self.combine(&mut g, &mut p, j, j - 1);
        }
        // the odd positions, Kogge-Stone, highest first
        for i in 1..levels {
            let stride = 1usize << i;
            for j in (stride..n).rev() {
                if j % 2 == 1 {
                    self.combine(&mut g, &mut p, j, j - stride);
                }
            }
        }
        // the even positions from their odd neighbour
        for j in (2..n).step_by(2) {
            self.combine(&mut g, &mut p, j, j - 1);
        }
        let mut result = Vec::with_capacity(n + 1);
        for i in 0..n {
            let carry_in = if i == 0 { cin } else { g[i - 1] };
            let x = self.XOR(a[i], b[i]);
            result.push(self.XOR(x, carry_in));
        }
        result.push(g[n - 1]);
        result
    }

    /// (g[j], p[j]) = (g[j], p[j]) o (g[k], p[k]): generate g[j] | p[j] & g[k], propagate p[j] & p[k].
    fn combine(&mut self, g: &mut [Literal], p: &mut [Literal], j: usize, k: usize) {
        let t = self.AND(p[j], g[k]);
        let new_g = self.OR(g[j], t);
        let new_p = self.AND(p[j], p[k]);
        g[j] = new_g;
        p[j] = new_p;
    }

    /// The literal a net is, through buffers and inverters.
    fn import(&self, net: Net) -> Literal {
        let mut lit = Literal::pos(net);
        loop {
            let (id, off) = self.g.resolve(lit.net);
            match &self.g.inst(id).kind {
                Kind::Buffer(a) => lit = Literal::with_polarity(a[off as usize], lit.positive),
                Kind::Not(a) => lit = Literal::with_polarity(a[off as usize], !lit.positive),
                _ => return lit,
            }
        }
    }

    fn produce(&mut self, i: usize, lit: Literal) {
        self.replacement[i] = self.g.emit_control(lit);
    }

    /// A barrel shifter: per bit k of the amount, shift by 2^k strides when it is set. `fill` is
    /// what enters past the end; `overflow` what every bit becomes once a stage shifts past it.
    fn shift(&mut self, op: ShiftOp, a: &[Net], b: &[Net], stride: u32) {
        let n = a.len();
        let mut cur: Vec<Literal> = (0..n).map(|i| self.import(a[i])).collect();
        let sign = if op == ShiftOp::SShr { Some(self.import(a[a.len() - 1])) } else { None };
        for (k, &bn) in b.iter().enumerate() {
            let bk = self.import(bn);
            // a 32-bit amount, its shift count taken mod 32 as the machine does
            let shift = 1u32.wrapping_shl(k as u32).wrapping_mul(stride) as usize;
            if shift >= n {
                for c in cur.iter_mut() {
                    *c = match sign {
                        Some(s) => self.MUX(bk, s, *c),
                        None => self.AND(*c, not(bk)),
                    };
                }
                break;
            }
            let mut next = vec![Literal::ZERO; n];
            for i in 0..n {
                let shifted = match op {
                    ShiftOp::Shl => {
                        if i >= shift {
                            cur[i - shift]
                        } else {
                            Literal::ZERO
                        }
                    }
                    _ => {
                        if i + shift < n {
                            cur[i + shift]
                        } else {
                            sign.unwrap_or(Literal::ZERO)
                        }
                    }
                };
                next[i] = self.MUX(bk, shifted, cur[i]);
            }
            cur = next;
        }
        for (i, &c) in cur.iter().enumerate() {
            self.produce(i, c);
        }
    }

    /// Partial products in columns (sign rows and columns complemented, constants corrected),
    /// reduced 3 to 2 with full adders, then added.
    fn mul(&mut self, a: &[Net], b: &[Net], n: usize) {
        let (mut a_len, mut b_len) = (a.len(), b.len());
        while a_len >= 2 && a[a_len - 1] == a[a_len - 2] {
            a_len -= 1;
        }
        while b_len >= 2 && b[b_len - 1] == b[b_len - 2] {
            b_len -= 1;
        }
        let a_bits: Vec<Literal> = a[..a_len].iter().map(|&x| self.import(x)).collect();
        let b_bits: Vec<Literal> = b[..b_len].iter().map(|&x| self.import(x)).collect();

        let mut columns: Vec<Vec<Literal>> = vec![Vec::new(); n];
        {
            let mut corrections = vec![0i32; n];
            for k in 0..b_len.min(n) {
                for j in 0..a_len {
                    if j + k >= n {
                        break;
                    }
                    let mut product = self.AND(a_bits[j], b_bits[k]);
                    if (k == b_len - 1 || j == a_len - 1) && (k != b_len - 1 || j != a_len - 1) {
                        product = not(product);
                        corrections[j + k] -= 1;
                    }
                    if product.is_always(false) {
                    } else if product.is_always(true) {
                        corrections[j + k] += 1;
                    } else {
                        columns[j + k].push(product);
                    }
                }
            }
            let mut pending = 0i32;
            for i in 0..n {
                pending += corrections[i];
                if pending & 1 != 0 {
                    columns[i].push(Literal::ONE);
                }
                if pending >= 0 {
                    pending /= 2;
                } else {
                    pending = (pending / 2) - (pending & 1);
                }
            }
        }

        loop {
            let max_height = columns.iter().map(Vec::len).max().unwrap_or(0);
            if max_height <= 2 {
                break;
            }
            let mut next: Vec<Vec<Literal>> = vec![Vec::new(); n];
            for i in 0..n {
                let mut col = std::mem::take(&mut columns[i]);
                while col.len() >= 3 {
                    let x = col.pop().unwrap();
                    let y = col.pop().unwrap();
                    let z = col.pop().unwrap();
                    let xy = self.XOR(x, y);
                    let s = self.XOR(xy, z);
                    next[i].push(s);
                    if i + 1 < n {
                        let c1 = self.AND(x, y);
                        let c2 = self.AND(xy, z);
                        let c = self.OR(c1, c2);
                        next[i + 1].push(c);
                    }
                }
                next[i].extend(col);
            }
            columns = next;
        }

        let row_a: Vec<Literal> = columns.iter().map(|c| c.first().copied().unwrap_or(Literal::ZERO)).collect();
        let row_b: Vec<Literal> = columns.iter().map(|c| c.get(1).copied().unwrap_or(Literal::ZERO)).collect();
        let result = self.adder(&row_a, &row_b, Literal::ZERO);
        for (i, &r) in result.iter().take(n).enumerate() {
            self.produce(i, r);
        }
    }

    /// Two literals per bit, combined by `f`.
    fn bitwise(&mut self, a: &[Net], b: &[Net], f: fn(&mut Self, Literal, Literal) -> Literal) {
        for i in 0..a.len() {
            let x = self.import(a[i]);
            let y = self.import(b[i]);
            let r = f(self, x, y);
            self.produce(i, r);
        }
    }

    fn build(&mut self, kind: &Kind) {
        match kind {
            Kind::Adc(a, b, cin) => {
                let mut a_bits = Vec::new();
                let mut b_bits = Vec::new();
                for i in 0..a.len() {
                    a_bits.push(self.import(a[i]));
                    b_bits.push(self.import(b[i]));
                }
                let c = self.import(*cin);
                let sum = self.adder(&a_bits, &b_bits, c);
                for (i, &s) in sum.iter().enumerate() {
                    self.produce(i, s);
                }
            }
            Kind::Mux(sel, a, b) => {
                let sel = self.import(*sel);
                for i in 0..a.len() {
                    let x = self.import(a[i]);
                    let y = self.import(b[i]);
                    let r = self.MUX(sel, x, y);
                    self.produce(i, r);
                }
            }
            Kind::Bin(BinOp::Eq, a, b) => {
                let mut entries = Vec::with_capacity(a.len());
                for i in 0..a.len() {
                    let x = self.import(a[i]);
                    let y = self.import(b[i]);
                    entries.push(self.XOR(x, y));
                }
                while entries.len() > 1 {
                    let mut next = Vec::new();
                    for i in (0..entries.len()).step_by(2) {
                        if entries.len() > i + 1 {
                            next.push(self.OR(entries[i], entries[i + 1]));
                        } else {
                            next.push(entries[i]);
                        }
                    }
                    entries = next;
                }
                self.produce(0, not(entries[0]));
            }
            // a < b: no carry out of a + ~b + 1; signed: that carry XOR (the signs equal)
            Kind::Bin(op @ (BinOp::ULt | BinOp::SLt), a, b) => {
                let n = a.len();
                let a_bits: Vec<Literal> = a.iter().map(|&x| self.import(x)).collect();
                let nb_bits: Vec<Literal> = b.iter().map(|&x| not(self.import(x))).collect();
                let sum = self.adder(&a_bits, &nb_bits, Literal::ONE);
                if *op == BinOp::ULt {
                    self.produce(0, not(sum[n]));
                } else {
                    let a_msb = self.import(a[n - 1]);
                    let b_msb = self.import(b[n - 1]);
                    let same = self.XOR(a_msb, b_msb);
                    let r = self.XOR(sum[n], not(same));
                    self.produce(0, r);
                }
            }
            Kind::Bin(BinOp::Xor, a, b) => self.bitwise(a, b, Self::XOR),
            Kind::Shift(op, a, b, stride) => self.shift(*op, a, b, *stride),
            Kind::Bin(BinOp::Mul, a, b) => self.mul(a, b, self.replacement.len()),
            Kind::Bin(BinOp::And, a, b) => self.bitwise(a, b, Self::AND),
            Kind::Bin(BinOp::Or, a, b) => self.bitwise(a, b, Self::OR),
            Kind::Bin(BinOp::Andnot, a, b) => self.bitwise(a, b, |s, x, y| s.AND(x, not(y))),
            _ => unreachable!("not a bitblasted cell"),
        }
    }
}

/// Whether the pass rewrites this cell: everything but the multiplier, which only with
/// `blast_arith`.
fn is_bitblasted(kind: &Kind, blast_arith: bool) -> bool {
    match kind {
        Kind::Adc(..) | Kind::Mux(..) | Kind::Shift(..) => true,
        Kind::Bin(op, ..) => match op {
            BinOp::Eq | BinOp::ULt | BinOp::SLt | BinOp::Xor | BinOp::And | BinOp::Or | BinOp::Andnot => true,
            BinOp::Mul => blast_arith,
            _ => false,
        },
        _ => false,
    }
}

/// Normalizes, then replaces every bitblasted cell, in slot order, by gates; the AND hash is
/// shared by all of them. Cells the pass adds are not visited.
pub fn bitblast(g: &mut Graph, blast_arith: bool) {
    g.normalize();
    let mut cache = BTreeMap::new();
    let mut it = g.instances();
    while let Some(id) = it.next(g) {
        if !is_bitblasted(&g.inst(id).kind, blast_arith) {
            continue;
        }
        let kind = g.inst(id).kind.clone();
        let width = g.inst(id).output_width() as usize;
        let mut op = Bitblasted { g, and_cache: &mut cache, replacement: vec![Net::UNDEF; width] };
        op.build(&kind);
        let replacement = op.replacement;
        let output = g.output(id);
        g.replace(&output, &replacement, Equivalence::TwoValued, &[]);
    }
}
