// SPDX-License-Identifier: Apache-2.0
use super::*;

/// The trace prints a criticality as the logger's `{:a}`: a normal double as `0x1.<hex>p±e` with
/// its trailing zero hex digits dropped (none left: no point); zero, unlike C's `%a`, with the
/// subnormal exponent (witnessed: every non-critical output of the gcd trace reads `0x0p-1022`).
#[test]
fn criticality_prints_as_a_hexfloat() {
    assert_eq!(hexfloat(1.0), "0x1p+0");
    assert_eq!(hexfloat(0.0), "0x0p-1022");
    assert_eq!(hexfloat(0.5), "0x1p-1");
    assert_eq!(hexfloat(0.75), "0x1.8p-1");
    assert_eq!(hexfloat(-3.0), "-0x1.8p+1");
    assert_eq!(hexfloat(f64::from_bits(0x3fcd77d46923d58f)), "0x1.d77d46923d58fp-3");
}

/// A delay prints in the library's time unit: the FLOAT quotient, then fixed at the digits asked.
#[test]
fn delays_print_in_the_time_unit() {
    assert_eq!(delay_as_string(-2.3e-11, 3, 1e-9), "-0.023");
    assert_eq!(delay_as_string(2.5809e-11, 6, 1e-9), "0.025809");
    assert_eq!(delay_as_string(-1e-15, 3, 1e-9), "-0.000");
}

/// `std::min` / `std::max`: the first operand is kept on a tie and when the comparison is
/// unordered.
#[test]
fn min_and_max_keep_the_first_operand() {
    assert!(min_f(f32::NAN, 1.0).is_nan());
    assert_eq!(min_f(1.0, f32::NAN), 1.0);
    assert!(max_f(f32::NAN, 1.0).is_nan());
    assert_eq!(max_f(f32::NEG_INFINITY, 2.0), 2.0);
}

fn pin(id: u64, inst: Option<usize>, name: &str) -> Pin {
    Pin { id, inst, term: name.into(), name: name.into(), net: Some(0), io: "INPUT".into(), signal: true, supply: false, vertex: None }
}

/// A cut output's external load subtracts the cone's input pin caps in the order the timer's
/// connected-pin iterator gives them: a pin SET, so by pin id (an instance pin's id doubled, a
/// port's doubled plus one) — not the net's own iterm order. Float subtraction is not
/// associative: witnessed as a one-ulp load on 8 of gcd's cuts when walked in net order.
#[test]
fn connected_pins_walk_in_pin_id_order() {
    // Pin indices are held in id order; the net lists its iterms out of that order.
    let nl = Netlist {
        pins: vec![pin(2, Some(0), "a"), pin(3, None, "p"), pin(4, Some(1), "b"), pin(6, Some(2), "c")],
        insts: Vec::new(),
        nets: vec![Net { name: "n".into(), iterms: vec![3, 0, 2], bterms: vec![1], dont_touch: false, drivers: Vec::new() }],
        vertex_pin: Vec::new(),
    };
    assert_eq!(nl.connected_pins(0), vec![0, 1, 2, 3]);
}
