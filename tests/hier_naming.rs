//! Flat names joined at module-instance boundaries as the reference flow's `flatten` joins them, on
//! a real elaboration. Expected names are Yosys 0.68's (`flatten -separator / -noscopeinfo`, and a
//! module kept, then flattened by a second `flatten -separator /`) on the same source: a module
//! instance boundary takes the separator; a generate block (array element, named or `genblkN`)
//! keeps `.`; an instance-array element is `name[i]`; a kept module's boundary takes `/`.

use vyges_syn::elab::frontend::Failed;
use vyges_syn::elab::hierarchy::HierNaming;
use vyges_syn::ir::Kind;
use vyges_syn::library::Libraries;

const SRC: &str = "\
module leaf(input logic a, input logic b, output logic y);
  logic t;
  assign t = a ^ b;
  assign y = ~t;
endmodule
module mid #(parameter N = 2) (input logic [N-1:0] a, output logic [N-1:0] y);
  logic [N-1:0] m;
  genvar i;
  for (i = 0; i < N; i++) begin : g
    leaf u_l (.a(a[i]), .b(m[i]), .y(y[i]));
  end
  if (N > 1) begin
    leaf u_un (.a(a[0]), .b(a[1]), .y(m[0]));
  end
  assign m[N-1:1] = a[N-2:0];
endmodule
module top(input logic [3:0] a, output logic [3:0] y, output logic [1:0] z, output logic [1:0] w);
  mid #(.N(2)) u_m0 (.a(a[1:0]), .y(y[1:0]));
  mid #(.N(2)) u_m1 (.a(a[3:2]), .y(y[3:2]));
  leaf u_arr [2:1] (.a(a[1:0]), .b(a[3:2]), .y(z));
  for (genvar j = 3; j >= 2; j--) begin : q
    leaf u_q (.a(a[j]), .b(a[j-2]), .y(w[j-2]));
  end
endmodule
";

fn names(naming: &HierNaming) -> Result<Vec<String>, Failed> {
    let dir = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("hier_naming");
    std::fs::create_dir_all(&dir).unwrap();
    let src = dir.join("design.sv");
    std::fs::write(&src, SRC).unwrap();
    let args = [src.to_string_lossy().into_owned(), "--top".into(), "top".into()];
    let g = vyges_syn::synthesis::elaborate(&args, &Libraries::default(), naming)?;
    Ok(g.instance_list().into_iter().filter_map(|id| match &g.inst(id).kind {
        Kind::Name(n) => Some(n.name.clone()),
        _ => None,
    }).collect())
}

fn has(all: &[String], want: &[&str]) {
    for w in want {
        assert!(all.iter().any(|n| n == w), "{w} missing from {all:?}");
    }
}

// Rule (Yosys flatten, F1/F2): `u_m0/g[0].u_l/t`, `u_m0/genblk2.u_un/t`, `u_arr[1]/t`, `q[3].u_q/t`.
#[test]
fn every_module_instance_boundary_takes_the_separator() {
    let n = names(&HierNaming { separator: Some("/".into()), keep_modules: vec![] }).unwrap();
    has(&n, &["a", "u_m0/m", "u_m0/g[0].u_l/t", "u_m0/g[1].u_l/t", "u_m0/genblk2.u_un/t", "u_m1/g[1].u_l/y", "u_arr[1]/t", "u_arr[2]/t", "q[3].u_q/t", "q[2].u_q/a"]);
    assert!(!n.iter().any(|x| x.contains("g[0]/") || x.contains("genblk2/") || x.contains("q[3]/")), "{n:?}");
}

// Rule (ORFS default SYNTH_HIER_SEPARATOR `.` = the reference `syn`'s own names): nothing changes.
#[test]
fn the_default_is_the_frontends_names() {
    let d = names(&HierNaming::default()).unwrap();
    has(&d, &["u_m0.g[0].u_l.t", "u_arr[1].t", "q[3].u_q.t"]);
    assert_eq!(d, names(&HierNaming { separator: Some(".".into()), keep_modules: vec![] }).unwrap());
}

// Rule (ORFS SYNTH_KEEP_MODULES, then the reader's `/`): kept `leaf` boundaries take `/`, the
// rest keep SYNTH_HIER_SEPARATOR: `u_m0.g[0].u_l/t`; keeping `mid` gives `u_m0/g[0].u_l.t`.
#[test]
fn a_kept_module_boundary_takes_the_readers_divider() {
    let n = names(&HierNaming { separator: None, keep_modules: vec!["leaf".into()] }).unwrap();
    has(&n, &["u_m0.g[0].u_l/t", "u_m0.genblk2.u_un/t", "u_m0.m", "u_arr[1]/t"]);
    let n = names(&HierNaming { separator: None, keep_modules: vec!["mid".into()] }).unwrap();
    has(&n, &["u_m0/g[0].u_l.t", "u_m1/m", "u_arr[1].t"]);
}

// Rule (ORFS: "SYNTH_KEEP_MODULES: no module X in the design" stops the run).
#[test]
fn a_kept_module_the_design_lacks_stops_the_run() {
    match names(&HierNaming { separator: None, keep_modules: vec!["nope".into()] }) {
        Err(Failed::Error(73, m)) => assert!(m.contains("nope"), "{m}"),
        other => panic!("expected SYN-0073, got {other:?}"),
    }
}
