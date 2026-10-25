// SPDX-License-Identifier: Apache-2.0
//! The text form reads back to the same text, and declared ids are kept.
use vyges_syn::ir::instance::{OtherPort, PortDirection};
use vyges_syn::ir::parse::{other, parse};
use vyges_syn::ir::{BinOp, ControlNet, Graph, Kind, Net, ShiftOp, Trit};

#[test]
fn every_cell_kind_dumps_parses_and_dumps_the_same() {
    let mut g = Graph::new();
    let a = g.add(Kind::Input("a".into(), 4));
    let b = g.add(Kind::Input("b".into(), 4));
    let clk = g.add(Kind::Input("clk".into(), 1));
    let sel = g.add(Kind::Input("sel".into(), 1));
    g.add(Kind::Dangling(3));
    g.add(Kind::Buffer(a.clone()));
    g.add(Kind::Not(b.clone()));
    let c = g.add(Kind::Bin(BinOp::And, a.clone(), b.clone()));
    for op in [BinOp::Or, BinOp::Andnot, BinOp::Xor] {
        g.add(Kind::Bin(op, a.clone(), b.clone()));
    }
    g.add(Kind::Mux(sel[0], a.clone(), b.clone()));
    g.add(Kind::Adc(a.clone(), b.clone(), Net::ZERO));
    for op in [BinOp::Eq, BinOp::ULt, BinOp::SLt] {
        g.add(Kind::Bin(op, a.clone(), b.clone()));
    }
    for op in [ShiftOp::Shl, ShiftOp::UShr, ShiftOp::SShr, ShiftOp::XShr] {
        g.add(Kind::Shift(op, a.clone(), b.clone(), 1));
    }
    for op in [BinOp::Mul, BinOp::UDiv, BinOp::UMod, BinOp::SDivTrunc, BinOp::SDivFloor, BinOp::SModTrunc, BinOp::SModFloor] {
        g.add(Kind::Bin(op, a.clone(), b.clone()));
    }
    let undef = vec![Trit::Undef; 4];
    g.add(Kind::Dff(Box::new(vyges_syn::ir::instance::Dff {
        data: a.clone(),
        clock: ControlNet::pos(clk[0]),
        clear: ControlNet::ZERO,
        reset: ControlNet::ZERO,
        enable: ControlNet::ONE,
        init_value: undef.clone(),
        reset_value: undef.clone(),
        clear_value: undef,
    })));
    let name = |n: &str, v: Vec<Net>, tentative: bool, is_vector: bool| {
        let to = v.len() as u32;
        Kind::Name(Box::new(vyges_syn::ir::instance::NameInst { name: n.into(), value: v, from: 0, to, tentative, is_vector }))
    };
    g.add(name("wire_a", a.clone(), false, true));
    g.add(name("dbg_b", b.clone(), true, true));
    let ports = vec![
        OtherPort { name: "A".into(), direction: PortDirection::Input, width: 4, value: a.clone() },
        OtherPort { name: "Y".into(), direction: PortDirection::Output, width: 2, value: vec![] },
    ];
    g.add(Kind::Other(Box::new(other("CUSTOM_CELL".into(), ports))));
    g.add(Kind::Output("out".into(), c));
    let d1 = g.dump();
    let d2 = parse(&d1, None).unwrap().dump();
    assert_eq!(d1, d2);
}

#[test]
fn declared_ids_are_kept_across_gaps() {
    // %3..%5 unused: `a` is %6..%9, `b` %10..%13, the output %14, the and %15..%18.
    let src = "%6:4 = input \"a\"\n%10:4 = input \"b\"\n%14:0 = output \"y\" %15:4\n%15:4 = and %6:4 %10:4\n";
    let g = parse(src, None).unwrap();
    assert_eq!(g.dump(), src);
    let and = g.resolve(Net(15)).0;
    let Kind::Bin(BinOp::And, a, b) = &g.inst(and).kind else { panic!() };
    assert_eq!(a, &(6..10).map(Net).collect::<Vec<_>>());
    assert_eq!(b, &(10..14).map(Net).collect::<Vec<_>>());
}
