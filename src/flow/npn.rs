// SPDX-License-Identifier: Apache-2.0
//! NPN classes of functions of up to six inputs: two functions are equivalent when one is the
//! other with inputs complemented (N), permuted (P) and the output complemented (N).
//!
//! A truth table is 64 bits, row `r` (the inputs' values as a binary number, input 0 the least
//! significant) at bit `r`.

pub type Truth6 = u64;

/// Rows where input `i` is 1.
pub const COFACTOR_MASKS: [Truth6; 6] = [
    0xaaaa_aaaa_aaaa_aaaa,
    0xcccc_cccc_cccc_cccc,
    0xf0f0_f0f0_f0f0_f0f0,
    0xff00_ff00_ff00_ff00,
    0xffff_0000_ffff_0000,
    0xffff_ffff_0000_0000,
];

/// Every row of a `size`-input table.
pub fn mask6(size: usize) -> Truth6 {
    if size == 6 {
        return u64::MAX;
    }
    (1u64 << (1 << size)) - 1
}

/// A transform: input `i` complemented when `input_complement[i]` and moved to
/// `permutation[i]`, the output complemented when `output_complement`. Unused inputs are -1.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Npn {
    pub output_complement: bool,
    pub input_complement: [bool; 6],
    pub permutation: [i32; 6],
}

impl Default for Npn {
    fn default() -> Self {
        Npn { output_complement: false, input_complement: [false; 6], permutation: [-1; 6] }
    }
}

impl Npn {
    pub fn ninputs(&self) -> usize {
        self.permutation.iter().take_while(|&&p| p != -1).count()
    }

    /// `self` after `other`: input `i` goes where `other` sends it, then where `self` sends that.
    pub fn compose(&self, other: &Npn) -> Npn {
        let mut ret = Npn { output_complement: self.output_complement ^ other.output_complement, ..Npn::default() };
        for i in 0..6 {
            if self.permutation[i] == -1 {
                break;
            }
            let o = other.permutation[i] as usize;
            ret.permutation[i] = self.permutation[o];
            ret.input_complement[i] = self.input_complement[o] ^ other.input_complement[i];
        }
        ret
    }

    pub fn inv(&self) -> Npn {
        let mut ret = Npn { output_complement: self.output_complement, ..Npn::default() };
        for i in 0..6 {
            if self.permutation[i] == -1 {
                break;
            }
            let p = self.permutation[i] as usize;
            ret.permutation[p] = i as i32;
            ret.input_complement[p] = self.input_complement[i];
        }
        ret
    }

    /// The complements as bits: the output's bit 0, input `i`'s bit `i + 1`.
    pub fn c_fingerprint(&self) -> u32 {
        let mut f = self.output_complement as u32;
        for (i, &c) in self.input_complement.iter().enumerate() {
            f |= (c as u32) << (i + 1);
        }
        f
    }
}

fn popcount(m: Truth6) -> i32 {
    m.count_ones() as i32
}

/// Order the inputs by the 1s in their negative cofactor, each complemented when that cofactor has
/// more 1s than the positive one; an input with as many as an earlier one goes after it.
/// Returns (complemented, cofactor counts in order, order).
fn sort_inputs(m: Truth6, ninputs: usize, mut on_tie: impl FnMut(usize)) -> ([bool; 6], [i32; 6], [usize; 6]) {
    let mut compls = [false; 6];
    let mut counts = [0i32; 6];
    let mut order = [0usize; 6];
    for i in 0..ninputs {
        let mut nfactor = popcount(m & !COFACTOR_MASKS[i]);
        let mut pfactor = popcount(m & COFACTOR_MASKS[i]);
        if nfactor > pfactor {
            std::mem::swap(&mut pfactor, &mut nfactor);
            compls[i] = true;
        } else if nfactor == pfactor {
            on_tie(i);
        }
        let mut j = 0;
        while j < i && nfactor >= counts[j] {
            j += 1;
        }
        for k in (j..i).rev() {
            counts[k + 1] = counts[k];
            order[k + 1] = order[k];
        }
        counts[j] = nfactor;
        order[j] = i;
    }
    (compls, counts, order)
}

/// `m` with each input complemented as `compl` says and moved to its place in `order`.
fn apply(m: Truth6, ninputs: usize, order: &[usize; 6], compl: impl Fn(usize) -> bool) -> Truth6 {
    let mut sc = 0;
    for idx1 in 0..1usize << ninputs {
        if m & 1 << idx1 == 0 {
            continue;
        }
        let mut idx2 = 0;
        for (j, &pj) in order.iter().enumerate().take(ninputs) {
            if ((idx1 >> pj) & 1 != 0) ^ compl(pj) {
                idx2 |= 1 << j;
            }
        }
        sc |= 1u64 << idx2;
    }
    sc
}

/// A representative of `m`'s class and the transform onto it: the output complemented when more
/// than half the rows are 1, each input complemented when its negative cofactor has more 1s, the
/// inputs ordered by their negative cofactor's 1s. Ties (half the rows, equal cofactors, equal
/// counts) are left as found, so equivalent functions can land on different representatives.
pub fn npn_semiclass(mut m: Truth6, ninputs: usize, npn: &mut Npn) -> Truth6 {
    *npn = Npn::default();
    if ninputs == 0 {
        return 0;
    }
    let nbits = 1 << ninputs;
    let mask = mask6(ninputs);
    m &= mask;
    if popcount(m) > nbits / 2 {
        npn.output_complement = true;
        m ^= mask;
    }
    let (compls, _, order) = sort_inputs(m, ninputs, |_| {});
    let sc = apply(m, ninputs, &order, |p| compls[p]);
    for (i, &o) in order.iter().enumerate().take(ninputs) {
        npn.input_complement[i] = compls[i];
        npn.permutation[o] = i as i32;
    }
    sc
}

/// The next permutation in lexicographic order; false (and the slice sorted) after the last.
fn next_permutation(v: &mut [usize]) -> bool {
    if v.len() < 2 {
        return false;
    }
    let mut i = v.len() - 1;
    while i > 0 && v[i - 1] >= v[i] {
        i -= 1;
    }
    if i == 0 {
        v.reverse();
        return false;
    }
    let mut j = v.len() - 1;
    while v[j] <= v[i - 1] {
        j -= 1;
    }
    v.swap(i - 1, j);
    v[i..].reverse();
    true
}

/// Every representative [`npn_semiclass`] could give a function equivalent to `m`, with the
/// transform onto it: for a function with half its rows 1, both output polarities (this one first);
/// for each, every polarity of the inputs whose cofactors tie (counting up over those inputs'
/// bits), and for each, every order within each run of equal counts (lexicographic, the last run
/// fastest).
pub fn npn_semiclass_all_repr(mut m: Truth6, ninputs: usize, mut cb: impl FnMut(Truth6, &Npn)) {
    let mut npn = Npn::default();
    if ninputs == 0 {
        cb(0, &npn);
        return;
    }
    let nbits = 1i32 << ninputs;
    let mask = mask6(ninputs);
    m &= mask;
    let mut bipolar = false;
    if popcount(m) > nbits / 2 {
        npn.output_complement = true;
        m ^= mask;
    } else if popcount(m) == nbits / 2 {
        bipolar = true;
    }
    loop {
        let mut ambimask = nbits - 1;
        let (compls, counts, mut order) = sort_inputs(m, ninputs, |i| ambimask &= !(1 << i));
        let mut tied = [0usize; 6];
        let mut i = 0;
        while i + 1 < ninputs {
            let mark = i;
            while i + 1 < ninputs && counts[i] == counts[i + 1] {
                tied[mark] += 1;
                i += 1;
            }
            i += 1;
        }
        let mut ambi = 0i32;
        while ambi < nbits {
            loop {
                let flip = |p: usize| compls[p] ^ (ambi & 1 << p != 0);
                let sc = apply(m, ninputs, &order, flip);
                for (k, &o) in order.iter().enumerate().take(ninputs) {
                    npn.input_complement[k] = flip(k);
                    npn.permutation[o] = k as i32;
                }
                cb(sc, &npn);
                let mut advanced = false;
                for j in (0..ninputs.saturating_sub(1)).rev() {
                    if tied[j] != 0 && next_permutation(&mut order[j..j + tied[j] + 1]) {
                        advanced = true;
                        break;
                    }
                }
                if !advanced {
                    break;
                }
            }
            ambi = ((ambi | ambimask) + 1) & !ambimask;
        }
        if !bipolar {
            break;
        }
        bipolar = false;
        m ^= mask;
        npn.output_complement ^= true;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Rule: the representative of a 2-input AND (0b1000) is itself, untransformed; an OR (0b1110,
    // three rows 1) is complemented to a NOR (0b0001), then both inputs complemented so the 1 row
    // moves to 11: an AND again.
    #[test]
    fn and_and_or_share_a_class() {
        let mut npn = Npn::default();
        assert_eq!(npn_semiclass(0b1000, 2, &mut npn), 0b1000);
        assert!(!npn.output_complement && npn.c_fingerprint() == 0);
        assert_eq!(npn_semiclass(0b1110, 2, &mut npn), 0b1000);
        assert_eq!(npn.c_fingerprint(), 0b111);
    }

    // Rule: an XOR is bipolar (half its rows 1) with both inputs tied in polarity and count: both
    // output polarities x both polarities of each input x both orders = 16 representatives.
    #[test]
    fn a_bipolar_tied_function_lists_every_representative() {
        let mut n = 0;
        npn_semiclass_all_repr(0b0110, 2, |_, _| n += 1);
        assert_eq!(n, 16);
    }

    // Rule: composing a transform with its inverse is the identity.
    #[test]
    fn a_transform_composed_with_its_inverse_is_the_identity() {
        let mut npn = Npn::default();
        npn_semiclass(0b0010_1100, 3, &mut npn);
        let id = npn.compose(&npn.inv());
        assert_eq!(id.c_fingerprint(), 0);
        assert_eq!(&id.permutation[..3], &[0, 1, 2]);
    }
}
