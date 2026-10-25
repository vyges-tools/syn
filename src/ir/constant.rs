// SPDX-License-Identifier: Apache-2.0
//! Three-valued constants and their arithmetic, least significant bit first.
//!
//! An undefined bit poisons: arithmetic and comparisons with any undefined input are undefined
//! (bitwise operations follow the dominance rules: 0 dominates AND, 1 dominates OR).

use super::net::Trit;

pub fn not(a: Trit) -> Trit {
    match a {
        Trit::Zero => Trit::One,
        Trit::One => Trit::Zero,
        Trit::Undef => Trit::Undef,
    }
}

pub fn and(a: Trit, b: Trit) -> Trit {
    if a == Trit::Zero || b == Trit::Zero {
        Trit::Zero
    } else if a == Trit::Undef || b == Trit::Undef {
        Trit::Undef
    } else {
        Trit::One
    }
}

pub fn or(a: Trit, b: Trit) -> Trit {
    if a == Trit::One || b == Trit::One {
        Trit::One
    } else if a == Trit::Undef || b == Trit::Undef {
        Trit::Undef
    } else {
        Trit::Zero
    }
}

pub fn xor(a: Trit, b: Trit) -> Trit {
    if a == Trit::Undef || b == Trit::Undef {
        Trit::Undef
    } else if a != b {
        Trit::One
    } else {
        Trit::Zero
    }
}

/// `sel ? a : b`; an undefined select keeps the bits the two agree on.
pub fn mux(sel: Trit, a: Trit, b: Trit) -> Trit {
    match sel {
        Trit::One => a,
        Trit::Zero => b,
        Trit::Undef => {
            if a == b {
                a
            } else {
                Trit::Undef
            }
        }
    }
}

pub fn has_undef(c: &[Trit]) -> bool {
    c.contains(&Trit::Undef)
}

pub fn is_zero(c: &[Trit]) -> bool {
    c.iter().all(|&t| t == Trit::Zero)
}

pub fn c_not(c: &[Trit]) -> Vec<Trit> {
    c.iter().map(|&t| not(t)).collect()
}

fn zip(a: &[Trit], b: &[Trit], f: fn(Trit, Trit) -> Trit) -> Vec<Trit> {
    assert_eq!(a.len(), b.len());
    a.iter().zip(b).map(|(&x, &y)| f(x, y)).collect()
}

pub fn c_and(a: &[Trit], b: &[Trit]) -> Vec<Trit> {
    zip(a, b, and)
}

pub fn c_or(a: &[Trit], b: &[Trit]) -> Vec<Trit> {
    zip(a, b, or)
}

pub fn c_xor(a: &[Trit], b: &[Trit]) -> Vec<Trit> {
    zip(a, b, xor)
}

/// Add with carry in: `width + 1` bits, the carry out last. An undefined bit makes that sum bit
/// and every carry after it undefined.
pub fn adc(a: &[Trit], b: &[Trit], ci: Trit) -> Vec<Trit> {
    assert_eq!(a.len(), b.len());
    let mut out = Vec::with_capacity(a.len() + 1);
    let mut carry = ci;
    for (&x, &y) in a.iter().zip(b) {
        let (s, co) = if x == Trit::Undef || y == Trit::Undef || carry == Trit::Undef {
            (Trit::Undef, Trit::Undef)
        } else if x == Trit::Zero && y == Trit::Zero {
            (carry, Trit::Zero)
        } else if x == Trit::One && y == Trit::One {
            (carry, Trit::One)
        } else {
            (not(carry), carry)
        };
        carry = co;
        out.push(s);
    }
    out.push(carry);
    out
}

/// Equal: zero at the first defined difference, else undefined if any bit is undefined.
pub fn eq(a: &[Trit], b: &[Trit]) -> Trit {
    assert_eq!(a.len(), b.len());
    let mut undef = false;
    for (&x, &y) in a.iter().zip(b) {
        if x == Trit::Undef || y == Trit::Undef {
            undef = true;
        } else if x != y {
            return Trit::Zero;
        }
    }
    if undef {
        Trit::Undef
    } else {
        Trit::One
    }
}

fn below_from_msb(a: &[Trit], b: &[Trit]) -> Trit {
    for i in (0..a.len()).rev() {
        if a[i] != b[i] {
            return if a[i] < b[i] { Trit::One } else { Trit::Zero };
        }
    }
    Trit::Zero
}

pub fn ult(a: &[Trit], b: &[Trit]) -> Trit {
    assert_eq!(a.len(), b.len());
    if has_undef(a) || has_undef(b) {
        return Trit::Undef;
    }
    below_from_msb(a, b)
}

/// Signed less-than: a set sign bit is the smaller; equal signs compare as unsigned.
pub fn slt(a: &[Trit], b: &[Trit]) -> Trit {
    assert_eq!(a.len(), b.len());
    if has_undef(a) || has_undef(b) {
        return Trit::Undef;
    }
    let (ma, mb) = (*a.last().unwrap(), *b.last().unwrap());
    if ma != mb {
        return if ma > mb { Trit::One } else { Trit::Zero };
    }
    below_from_msb(a, b)
}

/// A shift amount as an integer; none when a set bit sits at position 32 or above.
fn shift_amount(c: &[Trit]) -> Option<u64> {
    let mut v: u64 = 0;
    for i in (0..c.len()).rev() {
        v <<= 1;
        if c[i] == Trit::One {
            if i >= 32 {
                return None;
            }
            v |= 1;
        }
    }
    Some(v)
}

/// The shift distance (amount × stride), or what an out-of-range amount yields: the value itself
/// for stride 0, else a full shift.
enum Distance {
    Keep,
    All,
    By(usize),
}

fn distance(width: usize, amt: &[Trit], stride: u32) -> Distance {
    match shift_amount(amt) {
        None if stride == 0 => Distance::Keep,
        None => Distance::All,
        Some(s) => {
            let d = s * stride as u64;
            if d >= width as u64 {
                Distance::All
            } else {
                Distance::By(d as usize)
            }
        }
    }
}

pub fn shl(a: &[Trit], amt: &[Trit], stride: u32) -> Vec<Trit> {
    if has_undef(amt) {
        return vec![Trit::Undef; a.len()];
    }
    match distance(a.len(), amt, stride) {
        Distance::Keep => a.to_vec(),
        Distance::All => vec![Trit::Zero; a.len()],
        Distance::By(d) => {
            let mut v = vec![Trit::Zero; d];
            v.extend_from_slice(&a[..a.len() - d]);
            v
        }
    }
}

fn shr(a: &[Trit], amt: &[Trit], stride: u32, fill: Trit) -> Vec<Trit> {
    if has_undef(amt) {
        return vec![Trit::Undef; a.len()];
    }
    match distance(a.len(), amt, stride) {
        Distance::Keep => a.to_vec(),
        Distance::All => vec![fill; a.len()],
        Distance::By(d) => {
            let mut v = a[d..].to_vec();
            v.extend(std::iter::repeat_n(fill, d));
            v
        }
    }
}

pub fn ushr(a: &[Trit], amt: &[Trit], stride: u32) -> Vec<Trit> {
    shr(a, amt, stride, Trit::Zero)
}

/// Fills with the sign bit (read before the amount is checked).
pub fn sshr(a: &[Trit], amt: &[Trit], stride: u32) -> Vec<Trit> {
    if has_undef(amt) {
        return vec![Trit::Undef; a.len()];
    }
    shr(a, amt, stride, *a.last().expect("sshr of an empty constant"))
}

pub fn xshr(a: &[Trit], amt: &[Trit], stride: u32) -> Vec<Trit> {
    shr(a, amt, stride, Trit::Undef)
}

/// Schoolbook multiply truncated to the operands' width.
pub fn mul(a: &[Trit], b: &[Trit]) -> Vec<Trit> {
    assert_eq!(a.len(), b.len());
    let w = a.len();
    if has_undef(a) || has_undef(b) {
        return vec![Trit::Undef; w];
    }
    let mut r = vec![Trit::Zero; w];
    for (i, &bit) in b.iter().enumerate() {
        if bit == Trit::One {
            let mut shifted = vec![Trit::Zero; i];
            shifted.extend_from_slice(a);
            r = adc(&r, &shifted[..w], Trit::Zero)[..w].to_vec();
        }
    }
    r
}

/// Restoring division, most significant bit first: quotient and remainder.
fn divide(a: &[Trit], b: &[Trit]) -> (Vec<Trit>, Vec<Trit>) {
    let n = a.len();
    let nb = c_not(b);
    let mut rem = vec![Trit::Zero; n];
    let mut quot = vec![Trit::Zero; n];
    for k in (0..n).rev() {
        for i in (1..n).rev() {
            rem[i] = rem[i - 1];
        }
        rem[0] = a[k];
        let trial = adc(&rem, &nb, Trit::One);
        if trial[n] == Trit::One {
            rem = trial[..n].to_vec();
            quot[k] = Trit::One;
        }
    }
    (quot, rem)
}

pub fn udiv(a: &[Trit], b: &[Trit]) -> Vec<Trit> {
    assert_eq!(a.len(), b.len());
    if has_undef(a) || has_undef(b) || is_zero(b) {
        return vec![Trit::Undef; a.len()];
    }
    divide(a, b).0
}

pub fn umod(a: &[Trit], b: &[Trit]) -> Vec<Trit> {
    assert_eq!(a.len(), b.len());
    if has_undef(a) || has_undef(b) || is_zero(b) {
        return vec![Trit::Undef; a.len()];
    }
    divide(a, b).1
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A constant written most significant bit first, as the dump prints it.
    fn c(s: &str) -> Vec<Trit> {
        s.chars()
            .rev()
            .map(|ch| match ch {
                '0' => Trit::Zero,
                '1' => Trit::One,
                _ => Trit::Undef,
            })
            .collect()
    }

    #[test]
    fn dominance_beats_undefined() {
        // 0 dominates AND and 1 dominates OR even against an undefined bit; XOR has no dominance.
        assert_eq!(and(Trit::Zero, Trit::Undef), Trit::Zero);
        assert_eq!(and(Trit::One, Trit::Undef), Trit::Undef);
        assert_eq!(or(Trit::One, Trit::Undef), Trit::One);
        assert_eq!(or(Trit::Zero, Trit::Undef), Trit::Undef);
        assert_eq!(xor(Trit::One, Trit::Undef), Trit::Undef);
        assert_eq!(xor(Trit::One, Trit::One), Trit::Zero);
    }

    #[test]
    fn mux_undefined_select_keeps_agreement() {
        // An undefined select yields the input value only where both inputs agree.
        assert_eq!(mux(Trit::Undef, Trit::One, Trit::One), Trit::One);
        assert_eq!(mux(Trit::Undef, Trit::One, Trit::Zero), Trit::Undef);
        assert_eq!(mux(Trit::One, Trit::One, Trit::Zero), Trit::One);
        assert_eq!(mux(Trit::Zero, Trit::One, Trit::Zero), Trit::Zero);
    }

    #[test]
    fn adc_carry_out_last_and_undefined_propagates_upward() {
        assert_eq!(adc(&c("11"), &c("01"), Trit::Zero), c("100"));
        assert_eq!(adc(&c("01"), &c("01"), Trit::One), c("011"));
        // An undefined bit makes its sum bit and every later carry undefined; lower bits stay.
        assert_eq!(adc(&c("0X1"), &c("001"), Trit::Zero), c("XXX0"));
    }

    #[test]
    fn eq_defined_difference_wins_over_undefined() {
        assert_eq!(eq(&c("X1"), &c("00")), Trit::Zero);
        assert_eq!(eq(&c("X1"), &c("01")), Trit::Undef);
        assert_eq!(eq(&c("10"), &c("10")), Trit::One);
    }

    #[test]
    fn comparisons() {
        assert_eq!(ult(&c("01"), &c("10")), Trit::One);
        assert_eq!(ult(&c("10"), &c("10")), Trit::Zero);
        assert_eq!(ult(&c("X0"), &c("10")), Trit::Undef);
        // Signed: 10 (-2) < 01 (1); 11 (-1) is not < 10 (-2).
        assert_eq!(slt(&c("10"), &c("01")), Trit::One);
        assert_eq!(slt(&c("11"), &c("10")), Trit::Zero);
        assert_eq!(slt(&c("10"), &c("11")), Trit::One);
    }

    #[test]
    fn shifts_by_amount_times_stride() {
        assert_eq!(shl(&c("0011"), &c("1"), 1), c("0110"));
        assert_eq!(shl(&c("0011"), &c("1"), 2), c("1100"));
        assert_eq!(ushr(&c("1100"), &c("01"), 1), c("0110"));
        assert_eq!(sshr(&c("1100"), &c("10"), 1), c("1111"));
        assert_eq!(xshr(&c("1100"), &c("1"), 1), c("X110"));
        // A distance at or past the width shifts everything out.
        assert_eq!(shl(&c("0011"), &c("100"), 1), c("0000"));
        assert_eq!(sshr(&c("1000"), &c("111"), 1), c("1111"));
        // An undefined amount makes the whole result undefined.
        assert_eq!(ushr(&c("1100"), &c("X"), 1), c("XXXX"));
    }

    #[test]
    fn shift_amount_with_a_bit_at_32_or_above() {
        // The amount does not fit 32 bits: a full shift, or the value unchanged at stride 0.
        let mut big = vec![Trit::Zero; 33];
        big[32] = Trit::One;
        assert_eq!(shl(&c("0011"), &big, 1), c("0000"));
        assert_eq!(ushr(&c("0011"), &big, 0), c("0011"));
        assert_eq!(xshr(&c("0011"), &big, 1), c("XXXX"));
        // A zero stride with an in-range amount keeps the value too.
        assert_eq!(shl(&c("0011"), &c("11"), 0), c("0011"));
    }

    #[test]
    fn mul_truncates_to_operand_width() {
        assert_eq!(mul(&c("0011"), &c("0101")), c("1111"));
        assert_eq!(mul(&c("0110"), &c("0110")), c("0100"));
        assert_eq!(mul(&c("0X10"), &c("0001")), c("XXXX"));
    }

    #[test]
    fn division_and_remainder() {
        assert_eq!(udiv(&c("1101"), &c("0011")), c("0100"));
        assert_eq!(umod(&c("1101"), &c("0011")), c("0001"));
        assert_eq!(udiv(&c("1111"), &c("0001")), c("1111"));
        // Division by zero, or any undefined operand, is all undefined.
        assert_eq!(udiv(&c("1101"), &c("0000")), c("XXXX"));
        assert_eq!(umod(&c("1101"), &c("000X")), c("XXXX"));
    }
}
