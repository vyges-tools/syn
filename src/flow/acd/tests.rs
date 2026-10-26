// SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::flow::target_index::build_index;
use crate::library::Libraries;
use vyges_loom::liberty::Lib;

/// A small library: every cell 1 ns from each input, 0.01 ns transition, 1 fF inputs.
/// (name, area, inputs, function); the output is `Y`.
const CELLS: &[(&str, f32, &[&str], &str)] = &[
    ("INV", 1.0, &["A"], "!A"),
    ("BUF", 2.0, &["A"], "A"),
    ("AND2", 3.0, &["A", "B"], "A&B"),
    ("OR2", 3.0, &["A", "B"], "A|B"),
    ("NAND2", 2.0, &["A", "B"], "!(A&B)"),
    ("NOR2", 2.0, &["A", "B"], "!(A|B)"),
    ("ANDNOT2", 3.0, &["A", "B"], "A&!B"),
    ("ORNOT2", 3.0, &["A", "B"], "A|!B"),
    ("XOR2", 5.0, &["A", "B"], "A^B"),
    ("XNOR2", 5.0, &["A", "B"], "!(A^B)"),
    ("MUX2", 7.0, &["A", "B", "S"], "(A&!S)|(B&S)"),
    ("AOI21", 4.0, &["A", "B", "C"], "!(A&(B|C))"),
    ("OAI21", 4.0, &["A", "B", "C"], "!(A|(B&C))"),
    ("AO21", 5.0, &["A", "B", "C"], "A&(B|C)"),
    ("OA21", 5.0, &["A", "B", "C"], "A|(B&C)"),
];

fn liberty_text() -> String {
    let mut s = String::from(
        "library(acd_cells) {\n delay_model : table_lookup;\n time_unit : \"1ns\";\n voltage_unit : \"1V\";\n \
         current_unit : \"1mA\";\n capacitive_load_unit(1, pf);\n",
    );
    let scalar = |name: &str, v: &str| format!("    {name} (scalar) {{ values (\"{v}\"); }}\n");
    for (name, area, inputs, function) in CELLS {
        s += &format!(" cell({name}) {{\n  area : {area};\n");
        for i in *inputs {
            s += &format!("  pin({i}) {{ direction : input; capacitance : 0.001; }}\n");
        }
        s += &format!("  pin(Y) {{\n   direction : output;\n   function : \"{function}\";\n");
        for i in *inputs {
            s += &format!("   timing () {{\n    related_pin : \"{i}\";\n");
            s += &scalar("cell_rise", "1.0");
            s += &scalar("cell_fall", "1.0");
            s += &scalar("rise_transition", "0.01");
            s += &scalar("fall_transition", "0.01");
            s += "   }\n";
        }
        s += "  }\n }\n";
    }
    s + "}\n"
}

struct Fixture {
    corner: Corner,
    index: TargetIndex,
}

impl Fixture {
    fn new() -> Self {
        let text = liberty_text();
        let mut libs = Libraries::default();
        libs.add(&Lib::parse(&text).expect("library parses"));
        let index = build_index(&libs);
        let mut corner = Corner::default();
        corner.add(TimingLibrary::read(&vyges_sta::liberty_parse::parse(&text).unwrap()).unwrap());
        Fixture { corner, index }
    }

    fn dparams<'c>(&'c self, mc: &MatchCache) -> DelayEstimationParameters<'c> {
        // Scalar tables ignore the input slew.
        let fixed = [0.0, 0.0];
        DelayEstimationParameters {
            nand_delay: find_delay_lower_bound(&self.corner, &mc.nand2().name, fixed),
            fixed_slews: fixed,
            corner: &self.corner,
        }
    }
}

/// a & (b | (c & (d | e)))-style chain over five inputs, minterm `m` at bit `m`.
const AND_OR_CHAIN5: u32 = 0xEEEA_EAEA;

fn and_or_chain_problem() -> SynthesisProblem {
    let mut f = TruthTable::new((0..5).collect(), 1, false, false);
    for m in 0..32 {
        f.set_value(0, m, (AND_OR_CHAIN5 >> m) & 1 != 0);
    }
    let mut p = SynthesisProblem::new(f);
    p.output_mut(0).critical = true;
    p.output_mut(0).criticality = 1.0;
    p
}

/// Input `var` arrives `arrival` seconds relative to the output's required time, every
/// transition pair alike.
fn set_arrival(p: &mut SynthesisProblem, var: usize, arrival: f32) {
    for in_rf in RISE_FALL {
        for out_rf in RISE_FALL {
            *p.input_mut(var).arrivals.at_transition_mut(in_rf).at_exit_mut(0, out_rf) = arrival;
        }
    }
}

fn bits_of(tt: &TruthTable, out: usize) -> u64 {
    (0..tt.num_minterms()).filter(|&m| tt.value(out, m)).fold(0u64, |acc, m| acc | 1 << m)
}

// Rule: with the timing term on hard (effort 1e11), the structure follows the late input — a
// late last input is placed near the output, a late first input likewise — and each network has
// strictly better slack (by half a NAND delay) in the context it was built for than the other.
// Both still compute the function.
#[test]
fn structure_reassociates_with_timing() {
    let fx = Fixture::new();
    let mut mc = MatchCache::new(&fx.index, MAX_BOUND_VARS).unwrap();
    let dp = fx.dparams(&mc);
    let early = -1e-7f32;
    let late = 0.0f32;

    let mut c_late = and_or_chain_problem();
    let mut a_late = and_or_chain_problem();
    for v in 0..5 {
        set_arrival(&mut c_late, v, early);
        set_arrival(&mut a_late, v, early);
    }
    set_arrival(&mut c_late, 4, late);
    set_arrival(&mut a_late, 0, late);

    let mut synth = |p: &SynthesisProblem| -> GateNetwork {
        let mut dbg = DebugLog::default();
        let mut calls = 0;
        synthesize(p, &mut mc, &dp, &mut dbg, f64::INFINITY, true, Some(&mut calls), 1e11)
            .unwrap()
            .expect("a network is found")
    };
    let net_c = synth(&c_late);
    let net_a = synth(&a_late);

    for net in [&net_c, &net_a] {
        assert_eq!(bits_of(&evaluate_function(net), 0), AND_OR_CHAIN5 as u64);
    }
    let slack = |p: &SynthesisProblem, n: &GateNetwork| network_slack(p, n, &fx.corner, [0.0, 0.0]);
    let margin = 0.5 * dp.nand_delay;
    assert!(slack(&c_late, &net_c) > slack(&c_late, &net_a) + margin);
    assert!(slack(&a_late, &net_a) > slack(&a_late, &net_c) + margin);
}

// Rule: whatever the search builds computes the function it was given — every 3-input function
// and a sweep of 4-input ones, area only (no critical output), single and two outputs.
#[test]
fn synthesized_networks_compute_their_function() {
    let fx = Fixture::new();
    let mut mc = MatchCache::new(&fx.index, MAX_BOUND_VARS).unwrap();
    let dp = fx.dparams(&mc);
    let mut found = 0;
    let mut check = |nv: usize, outs: &[u64]| {
        let mut f = TruthTable::new((0..nv).collect(), outs.len(), false, false);
        for (o, &bits) in outs.iter().enumerate() {
            for m in 0..1 << nv {
                f.set_value(o, m, (bits >> m) & 1 != 0);
            }
        }
        let p = SynthesisProblem::new(f.clone());
        let mut dbg = DebugLog::default();
        if let Some(net) = synthesize(&p, &mut mc, &dp, &mut dbg, f64::INFINITY, true, None, 1.0).unwrap() {
            assert_eq!(evaluate_function(&net), f, "{nv} inputs, {outs:x?}");
            found += 1;
        }
    };
    for bits in 0..256u64 {
        check(3, &[bits]);
    }
    let mut x: u64 = 0x9E37_79B9;
    for _ in 0..200 {
        x = x.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        check(4, &[(x >> 16) & 0xffff]);
        check(3, &[(x >> 8) & 0xff, (x >> 40) & 0xff]);
    }
    assert!(found > 500, "most functions find a network ({found})");
}

// Rule: a variable is dropped when no pair of care minterms differing in it alone differs in
// value; the merged minterm takes the low cofactor when care, else the high one.
#[test]
fn shrink_to_support_merges_cofactors_care_first() {
    // f(x0, x1) = x0, with x1 = 1 rows don't-care except one agreeing row.
    let mut f = TruthTable::new(vec![7, 9], 1, false, false);
    for m in 0..4 {
        f.set_value(0, m, m & 1 != 0);
    }
    f.set_dont_care(0, 2, true);
    assert_eq!(f.find_unsupported_var(), Some(1));
    f.shrink_to_support();
    assert_eq!(f.variables(), &[7]);
    assert!(!f.has_dontcares());
    assert!(!f.value(0, 0) && f.value(0, 1));

    // g = x0 with row 0 don't-care: x1 drops; merged row 0 has its low cofactor (row 0)
    // don't-care, so takes the high one (row 2, care 0).
    let mut g = TruthTable::new(vec![0, 1], 1, false, false);
    g.set_dont_care(0, 0, true);
    g.set_value(0, 0, true);
    g.set_value(0, 1, true);
    g.set_value(0, 3, true);
    g.shrink_to_support();
    assert_eq!(g.variables(), &[0]);
    assert!(!g.value(0, 0) && !g.dont_care(0, 0));
    assert!(g.value(0, 1));
}

// Rule: the FIRST unsupported position is dropped first (it is swapped to the top, so the
// surviving variables' order depends on which one goes first).
#[test]
fn the_first_unsupported_variable_goes_first() {
    // f(x0, x1, x2) = x1: x0 and x2 unsupported.
    let mut f = TruthTable::new(vec![4, 5, 6], 1, false, false);
    for m in 0..8 {
        f.set_value(0, m, m & 2 != 0);
    }
    assert_eq!(f.find_unsupported_var(), Some(0));
    f.shrink_to_support();
    assert_eq!(f.variables(), &[5]);
}

// Rule: swapping positions moves the variable ids and permutes every output's minterms alike.
#[test]
fn swap_vars_permutes_every_output() {
    let mut f = TruthTable::new(vec![3, 5, 8], 2, false, false);
    for m in 0..8 {
        f.set_value(0, m, m == 0b001);
        f.set_value(1, m, m == 0b011);
    }
    f.swap_vars(0, 2);
    assert_eq!(f.variables(), &[8, 5, 3]);
    assert_eq!(bits_of(&f, 0), 1 << 0b100);
    assert_eq!(bits_of(&f, 1), 1 << 0b110);
}

// Rule: the passthrough is the FIRST variable the output equals on its care rows.
#[test]
fn output_passthrough_is_the_first_matching_variable() {
    let mut f = TruthTable::new(vec![0, 1], 1, false, false);
    for m in 0..4 {
        f.set_value(0, m, m & 1 != 0);
    }
    f.set_dont_care(0, 1, true);
    f.set_dont_care(0, 2, true);
    // Care rows 0 (=0) and 3 (=1): both x0 and x1 match.
    assert_eq!(f.output_passthrough(0), Some(0));
}

// Rule: the hex dump is four bits a nibble, lowest index first, every output in sequence.
#[test]
fn hexdump_is_nibbles_low_first() {
    let mut f = TruthTable::new(vec![0, 1], 2, false, false);
    f.set_value(0, 0, true);
    f.set_value(1, 3, true);
    f.set_dont_care(1, 1, true);
    assert_eq!(hexdump(&f, false), "18");
    assert_eq!(hexdump(&f, true), "02");
}

// Rule: the NAND2 is the cheapest pure-permutation NAND; a library without one is SYN-0039.
#[test]
fn nand2_specimen_and_its_absence() {
    let fx = Fixture::new();
    let mc = MatchCache::new(&fx.index, MAX_BOUND_VARS).unwrap();
    assert_eq!(mc.nand2().name, "NAND2");
    assert_eq!(mc.min_area_for_width(2), 2.0);
    assert_eq!(mc.min_area_for_width(3), 4.0);
    assert_eq!(mc.min_area_for_width(7), INF_COST);

    let empty = TargetIndex::default();
    let e = MatchCache::new(&empty, MAX_BOUND_VARS).err().expect("refused");
    assert_eq!(e.code, 39);
}

// Rule: a match wires cell port j to input perm[j]; with don't-cares the cheapest fill wins (the
// first of least area, fills counted up from none).
#[test]
fn matches_wire_ports_and_fill_dont_cares() {
    let fx = Fixture::new();
    let mut mc = MatchCache::new(&fx.index, MAX_BOUND_VARS).unwrap();
    // x0 & !x1: ANDNOT2 with A = x0, B = x1.
    let m = mc.match_tt(0b0010, 2).unwrap();
    assert_eq!(m.driver.cell.name, "ANDNOT2");
    assert_eq!(&m.perm[..2], &[0, 1]);
    // x1 & !x0: the same cell, ports swapped.
    let m = mc.match_tt(0b0100, 2).unwrap();
    assert_eq!(m.driver.cell.name, "ANDNOT2");
    assert_eq!(&m.perm[..2], &[1, 0]);
    // Row 3 is 0, rows 1 and 2 are 1, row 0 free: NAND2 (row 0 → 1) at 2 beats XOR2 at 5.
    let m = mc.match_dc(0b0110, 0b1110, 2).unwrap();
    assert_eq!(m.driver.cell.name, "NAND2");
    assert!(mc.match_tt(0, 0).is_none(), "constants never match");
}

// Rule: the area lower bound spends the widest cells first, each removing w − 1 variables.
#[test]
fn lut_min_cost_uses_the_widest_cells_first() {
    let fx = Fixture::new();
    let mc = MatchCache::new(&fx.index, MAX_BOUND_VARS).unwrap();
    // 5 variables: two 3-input cells (4 each) take it to 1.
    assert_eq!(lut_min_cost(&mc, MAX_BOUND_VARS, 5), 8.0);
    // 4 variables: one 3-input (to 2), one 2-input.
    assert_eq!(lut_min_cost(&mc, MAX_BOUND_VARS, 4), 6.0);
    assert_eq!(lut_min_cost(&mc, MAX_BOUND_VARS, 0), 0.0);
}

// Rule: positions are symmetric when swapping them leaves the function (and its don't-cares)
// unchanged; classes are union-find roots.
#[test]
fn symmetry_classes_group_interchangeable_inputs() {
    // x0 & x1 | x2
    let mut f = TruthTable::new((0..3).collect(), 1, false, false);
    for m in 0..8 {
        f.set_value(0, m, (m & 3) == 3 || m & 4 != 0);
    }
    let c = symmetry_classes(&f);
    assert_eq!(c[0], c[1]);
    assert_ne!(c[0], c[2]);
}

// Rule: the timing arcs go per input transition to output transition, positive unate for AND:
// rise→rise and fall→fall, each the input's set plus the table delay.
#[test]
fn output_arrival_adds_the_gate_delay_per_arc() {
    let fx = Fixture::new();
    let mut mc = MatchCache::new(&fx.index, MAX_BOUND_VARS).unwrap();
    let and2 = mc.match_tt(0b1000, 2).unwrap().driver;
    let mut a = NodeArrivals::default();
    *a.at_transition_mut(RISE).at_exit_mut(0, RISE) = -5e-9;
    let b = NodeArrivals::default();
    let out = output_arrival(&and2, &[a, b], 0.002e-12, &fx.corner, [0.0, 0.0]);
    let got = out.at_transition(RISE).at_exit(0, RISE);
    assert!((got - (-4e-9)).abs() < 1e-15, "{got}");
    assert_eq!(out.at_transition(FALL).at_exit(0, RISE), f32::NEG_INFINITY);
    assert_eq!(out.exit_slack(0), 4e-9f32.min(f32::INFINITY));
}

// Rule: the logger prints a double in fixed form between 1e-4 and 1e16, else as d.ddde±XX.
#[test]
fn doubles_print_as_the_logger_does() {
    assert_eq!(fmt_double(3.0), "3");
    assert_eq!(fmt_double(2.5), "2.5");
    assert_eq!(fmt_double(1e-7), "1e-07");
    assert_eq!(fmt_double(-1.5e17), "-1.5e+17");
}
