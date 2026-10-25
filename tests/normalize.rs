// SPDX-License-Identifier: Apache-2.0
//! `normalize` against the reference's output on the same text (`data/normalize/<case>.ir` →
//! `.ref`), one case per rule:
//!
//! - live = reachable backwards from outputs, inputs, opaque cells, macros and non-tentative names;
//!   the rest is dropped and survivors are renumbered densely after the three ties;
//! - observable cells and inputs are placed first, in slot order; then a depth-first walk from
//!   their inputs places each cell after its inputs;
//! - buffers are forwarded (their net maps to their input's), never placed;
//! - an input already on the walk's stack is cut by a loop breaker;
//! - a flip-flop is placed when reached and its inputs walked after every observable root, so
//!   feedback through it needs no breaker;
//! - a bitwise cell is placed only over the run of live bits around the one reached whose inputs
//!   are already placed; a partial run becomes a cell of its own;
//! - a tentative name keeps nothing live by itself: it is moved through buffers and inverters to a
//!   live net (keeping the last inverter when the polarity is negative) and re-added, last, over
//!   its live runs only.
use vyges_syn::ir::parse::parse;

fn check(case: &str, input: &str, expected: &str) {
    let mut g = parse(input, None).unwrap_or_else(|e| panic!("{case}: {e}"));
    g.normalize();
    assert_eq!(g.dump(), expected, "{case}");
}

macro_rules! case {
    ($name:ident, $file:literal) => {
        #[test]
        fn $name() {
            check(
                $file,
                include_str!(concat!("data/normalize/", $file, ".ir")),
                include_str!(concat!("data/normalize/", $file, ".ref")),
            );
        }
    };
}

case!(dead_logic_is_dropped, "hand_dead");
case!(cells_follow_their_inputs, "hand_reorder");
case!(a_combinational_loop_gets_a_breaker, "hand_loop");
case!(a_loop_through_a_buffer_gets_a_breaker, "hand_loop_buf");
case!(a_wide_cell_is_kept_over_its_live_bits, "hand_slice");
case!(two_live_runs_become_two_cells, "hand_slice2");
case!(buffers_are_forwarded, "hand_buffers");
case!(a_tentative_name_keeps_an_inverter_of_a_live_net, "hand_tentative_inv");
case!(a_tentative_name_moves_through_buffers, "hand_tentative_buf");
case!(a_tentative_name_moves_from_a_buffer_to_the_inverter, "hand_tentative_buf_inv");
case!(a_tentative_name_splits_into_live_runs, "hand_tentative_split");
case!(flip_flop_feedback_needs_no_breaker, "hand_dff_loop");
case!(a_flip_flop_input_cone_is_walked_after_the_roots, "hand_dff_chain");
case!(an_opaque_cell_is_a_root, "hand_other");
case!(a_name_is_a_root, "hand_names");
case!(a_mux_keeps_its_select_per_slice, "hand_mux");
case!(an_adder_in_a_loop, "hand_adc_loop");
case!(random_0, "fuzz_0000");
case!(random_1, "fuzz_0001");
case!(random_2, "fuzz_0002");
case!(random_3, "fuzz_0003");
case!(random_4, "fuzz_0004");
case!(random_5, "fuzz_0005");
case!(random_6, "fuzz_0006");
case!(random_7, "fuzz_0007");
case!(random_8, "fuzz_0008");
case!(random_9, "fuzz_0009");
