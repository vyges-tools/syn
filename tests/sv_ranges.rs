//! `sv-ranges` on a real elaboration: the names and ranges slang's design gives, through a
//! second instance of one module (slang prints that body once and refers to it after) and a
//! generate-array element, as the netlist names them.

#[test]
fn declared_ranges_of_an_elaborated_design() {
    let dir = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("sv_ranges");
    std::fs::create_dir_all(&dir).unwrap();
    let src = dir.join("design.sv");
    std::fs::write(
        &src,
        "module sub(input clk, input x, output [5:4] o);\n  logic [5:4] t;\n  always_ff @(posedge clk) t <= {x, x};\n  assign o = t;\nendmodule\n\
         module top(input clk, input x, input [0:3] c, output [11:8] q, output [5:4] o1, output [5:4] o2);\n\
           logic [11:8] r;\n  always_ff @(posedge clk) r <= {c[0], c[1], c[2], x};\n  assign q = r;\n\
           sub u_sub(.clk(clk), .x(x), .o(o1));\n\
           for (genvar i = 0; i < 1; i++) begin : g\n    sub u_in(.clk(clk), .x(c[3]), .o(o2));\n  end\nendmodule\n",
    )
    .unwrap();
    let r = vyges_syn::elab::ranges::sv_ranges(&[src.to_string_lossy().into_owned(), "--top".into(), "top".into()]).unwrap();
    for (n, v) in [("q", (11, 8)), ("c", (0, 3)), ("r", (11, 8)), ("u_sub.t", (5, 4)), ("u_sub.o", (5, 4)), ("g[0].u_in.t", (5, 4))] {
        assert_eq!(r.ranges.get(n), Some(&v), "{n}: {:?}", r.ranges);
    }
    assert!(!r.ranges.contains_key("x") && !r.ranges.contains_key("clk"));
}
