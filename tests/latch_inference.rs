//! Latches, on a real elaboration (divergence D2). The reference flow's rule, Yosys: an
//! `always_latch` is a `$dlatch` (the slang frontend's `handle_comb_like_process`; `proc_dlatch`
//! for a process: enable = NOT of the paths that select the variable itself, data = the tree with
//! those paths cut), mapped to `$_DLATCH_N_`/`$_DLATCH_P_` cells, so a clock gate's latch stays a
//! latch. Our mux-lowering frontend emits the feedback mux; `infer_latches` must turn it back into
//! a library latch, and leave no combinational loop.

use std::collections::BTreeMap;

use vyges_syn::ir::instance::{BinOp, ShiftOp};
use vyges_syn::ir::net::Net;
use vyges_syn::ir::{Graph, Kind};
use vyges_syn::library::Libraries;

const LIB: &str = r#"library (latches) {
  cell (LATH) {
    area : 1.0;
    pin (D) { direction : input; }
    pin (E) { direction : input; }
    pin (Q) { direction : output; function : "IQ"; }
    latch (IQ, IQN) { enable : "E"; data_in : "D"; }
  }
  cell (LATL) {
    area : 1.0;
    pin (D) { direction : input; }
    pin (E) { direction : input; }
    pin (Q) { direction : output; function : "IQ"; }
    latch (IQ, IQN) { enable : "!E"; data_in : "D"; }
  }
}
"#;

/// CoralNPU's `ClockGate` (its generic branch), two more latch forms, and a form that is no latch.
const SRC: &str = "\
module cg(input clk_i, input enable, input te, output clk_o);
  logic en_latch;
  always_latch begin
    if (!clk_i) begin
      en_latch = enable | te;
    end
  end
  assign clk_o = en_latch & clk_i;
endmodule
module hi(input g, input d, output q);
  logic l;
  always_latch if (g) l = d;
  assign q = l;
endmodule
module nest(input a, input b, input c, output q);
  logic l;
  always_latch begin
    if (a) begin
      if (b) l = c;
    end
  end
  assign q = l;
endmodule
module blockvar(input [1:0] sel, input [3:0] lt, output logic [3:0] elt);
  always_comb begin
    case (sel)
      2'd0: for (int b = 0; b < 4; b++) begin
        int m;
        m = b | 1;
        if (m >= 4) m = 3;
        elt[b] = lt[m];
      end
      default: elt = '0;
    endcase
  end
endmodule
";

fn elaborate(top: &str, with_lib: bool) -> Graph {
    // One file per call: the tests run in parallel.
    static CALL: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let k = CALL.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("latch_inference");
    std::fs::create_dir_all(&dir).unwrap();
    let src = dir.join(format!("design-{k}.sv"));
    std::fs::write(&src, SRC).unwrap();
    let mut libs = Libraries::default();
    if with_lib {
        let lib = dir.join(format!("latches-{k}.lib"));
        std::fs::write(&lib, LIB).unwrap();
        libs.read(&lib.to_string_lossy()).unwrap();
    }
    let args = [src.to_string_lossy().into_owned(), "--top".into(), top.into()];
    vyges_syn::synthesis::sv_elaborate(&args, &libs, &Default::default()).unwrap()
}

/// A combinational net's value, the inputs by port name.
fn eval(g: &Graph, net: Net, ins: &BTreeMap<&str, bool>) -> bool {
    match net {
        Net::ZERO => return false,
        Net::ONE => return true,
        _ => {}
    }
    let (id, off) = g.resolve(net);
    let off = off as usize;
    let v = |n: Net| eval(g, n, ins);
    match &g.inst(id).kind {
        Kind::Input(name, _) => ins[name.as_str()],
        Kind::Buffer(a) => v(a[off]),
        Kind::Not(a) => !v(a[off]),
        Kind::Bin(BinOp::And, a, b) => v(a[off]) && v(b[off]),
        Kind::Bin(BinOp::Or, a, b) => v(a[off]) || v(b[off]),
        Kind::Bin(BinOp::Andnot, a, b) => v(a[off]) && !v(b[off]),
        Kind::Bin(BinOp::Xor, a, b) => v(a[off]) != v(b[off]),
        Kind::Bin(BinOp::Eq, a, b) => a.iter().zip(b).all(|(&x, &y)| v(x) == v(y)),
        Kind::Mux(s, a, b) => if v(*s) { v(a[off]) } else { v(b[off]) },
        Kind::Shift(ShiftOp::UShr | ShiftOp::XShr, a, s, stride) => {
            let k = s.iter().enumerate().fold(0usize, |acc, (i, &b)| acc | (usize::from(v(b)) << i));
            a.get(off + k * *stride as usize).is_some_and(|&n| v(n))
        }
        k => panic!("eval: {} not modelled", k.keyword()),
    }
}

/// The latch cells: (cell name, enable net, data net).
fn latches(g: &Graph) -> Vec<(String, Net, Net)> {
    g.instance_list()
        .into_iter()
        .filter_map(|id| match &g.inst(id).kind {
            Kind::Target(c, inputs) => Some((c.name.clone(), inputs[1], inputs[0])),
            _ => None,
        })
        .collect()
}

fn loop_breakers(g: &Graph) -> usize {
    g.instance_list().into_iter().filter(|&id| matches!(g.inst(id).kind, Kind::LoopBreaker(_))).count()
}

/// Every input combination: the latch must be transparent exactly when `open` says, passing
/// `want` then.
fn check(g: &Graph, names: &[&'static str], open: impl Fn(&BTreeMap<&str, bool>) -> bool, want: impl Fn(&BTreeMap<&str, bool>) -> bool) {
    let l = latches(g);
    assert_eq!(l.len(), 1, "one latch cell: {l:?}\n{}", g.dump());
    assert_eq!(loop_breakers(g), 0, "no combinational loop left:\n{}", g.dump());
    let (cell, en, d) = &l[0];
    for v in 0..1u32 << names.len() {
        let ins: BTreeMap<&str, bool> = names.iter().enumerate().map(|(i, &n)| (n, v >> i & 1 == 1)).collect();
        let transparent = eval(g, *en, &ins) == (cell == "LATH");
        assert_eq!(transparent, open(&ins), "{cell} enable at {ins:?}\n{}", g.dump());
        if transparent {
            assert_eq!(eval(g, *d, &ins), want(&ins), "{cell} data at {ins:?}\n{}", g.dump());
        }
    }
}

/// `always_latch if (!clk_i) en_latch = enable | te;`: Yosys makes it `$_DLATCH_N_` on `clk_i`
/// (`DLLx1` on ASAP7); ours the active-low latch, open while `clk_i` is 0, passing `enable | te`.
#[test]
fn clock_gate_latch_is_an_active_low_latch_on_the_clock() {
    let g = elaborate("cg", true);
    check(&g, &["clk_i", "enable", "te"], |i| !i["clk_i"], |i| i["enable"] || i["te"]);
    assert_eq!(latches(&g)[0].0, "LATL");
}

/// `if (g) l = d;`: Yosys `$_DLATCH_P_` on `g`; ours the active-high latch on `g`.
#[test]
fn positive_latch_is_an_active_high_latch() {
    let g = elaborate("hi", true);
    check(&g, &["g", "d"], |i| i["g"], |i| i["d"]);
    assert_eq!(latches(&g)[0].0, "LATH");
}

/// Yosys `find_mux_feedback`: both paths to the feedback hold (`!a`, `a & !b`); open on `a & b`.
#[test]
fn nested_ifs_hold_on_every_path_to_the_feedback() {
    let g = elaborate("nest", true);
    check(&g, &["a", "b", "c"], |i| i["a"] && i["b"], |i| i["c"]);
}

/// Without a latch cell the reference's own form stays: the feedback loop, unmapped.
#[test]
fn no_latch_cell_leaves_the_reference_form() {
    let g = elaborate("cg", false);
    assert!(latches(&g).is_empty());
    assert_eq!(loop_breakers(&g), 1, "{}", g.dump());
}

/// A block variable read only where it is assigned is no latch (CoralNPU's `msb_idx`): the
/// frontend's graph reads it back on the paths that do not assign it, but nothing observes those
/// reads, and the reference flow (Yosys, ORFS `1_2`) has no latch there. Latches are inferred on
/// the loops that survive optimization, where the reference runs `check_combinational_loops`.
#[test]
fn block_variable_read_only_where_assigned_is_no_latch() {
    let g = elaborate("blockvar", true);
    assert!(latches(&g).is_empty(), "{:?}\n{}", latches(&g), g.dump());
    assert_eq!(loop_breakers(&g), 0, "{}", g.dump());
}

/// The latch's output carries the variable's name, as Yosys's `$dlatch` Q is the variable (ORFS
/// names the cell `cg.en_latch`): a name left on the replaced mux tree is dropped with it, and
/// equivalence checking then pairs nothing with the reference's latch.
#[test]
fn latch_output_carries_the_variable_name() {
    let g = elaborate("cg", true);
    let q: Vec<Net> = g
        .instance_list()
        .into_iter()
        .filter(|&id| matches!(g.inst(id).kind, Kind::Target(..)))
        .map(|id| g.output(id)[0])
        .collect();
    assert_eq!(q.len(), 1, "one latch cell\n{}", g.dump());
    let named: Vec<Net> = g
        .instance_list()
        .into_iter()
        .filter_map(|id| match &g.inst(id).kind {
            Kind::Name(n) if n.name.ends_with("en_latch") => Some(n.value[0]),
            _ => None,
        })
        .collect();
    assert_eq!(named, q, "the name en_latch is on the latch output\n{}", g.dump());
}
