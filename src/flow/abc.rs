// SPDX-License-Identifier: Apache-2.0
//! The ABC round trip: the combinational AIG (And, Andnot, Or, Not, Buffer cells) out to an ABC
//! GIA manager, ABC commands run on it, and the result read back as And / Andnot / Or cells.
//!
//! Every other cell's outputs are the AIG's inputs (CIs); every net an AIG cell drives and a
//! non-AIG cell reads is an output (CO), once, in the order the non-AIG cells read them.

use std::collections::BTreeSet;

use vyges_abc_lib::{Abc, Gia, GiaObj};

use crate::ir::net::{ControlNet as Literal, Net};
use crate::ir::{Graph, Kind};

fn is_aig(kind: &Kind) -> bool {
    use crate::ir::instance::BinOp;
    matches!(kind, Kind::Bin(BinOp::And | BinOp::Andnot | BinOp::Or, ..) | Kind::Not(_) | Kind::Buffer(_))
}

fn is_tie(kind: &Kind) -> bool {
    matches!(kind, Kind::TieLow | Kind::TieHigh | Kind::TieX)
}

/// An AND of two literals as one cell, constants folded and nothing else: And, Andnot (the
/// positive input first) or Or for both negative.
fn and(g: &mut Graph, a: Literal, b: Literal) -> Literal {
    use crate::ir::instance::BinOp;
    if a.is_always(false) || b.is_always(false) {
        return Literal::ZERO;
    }
    if a.is_always(true) {
        return b;
    }
    if b.is_always(true) {
        return a;
    }
    let gate = |op, x: Net, y: Net| Kind::Bin(op, vec![x], vec![y]);
    match (a.positive, b.positive) {
        (true, true) => Literal::pos(g.add(gate(BinOp::And, a.net, b.net))[0]),
        (true, false) => Literal::pos(g.add(gate(BinOp::Andnot, a.net, b.net))[0]),
        (false, true) => Literal::pos(g.add(gate(BinOp::Andnot, b.net, a.net))[0]),
        (false, false) => Literal::neg(g.add(gate(BinOp::Or, a.net, b.net))[0]),
    }
}

fn not(l: Literal) -> Literal {
    Literal::with_polarity(l.net, !l.positive)
}

/// Normalizes, exports the AIG, runs `commands` in ABC, and replaces each output net by what ABC
/// computed for it. `naming_threshold` >= 0: a tentative name keeps the nets it reads as outputs
/// when they have at least that many readers (names not counted); < 0: tentative names are ignored.
/// What it logs is printed as the reference's logger prints it.
pub fn abc_roundtrip(g: &mut Graph, abc: &mut Abc, commands: &str, naming_threshold: i32) -> Result<(), String> {
    g.normalize();

    // ---- export ----
    let size = g.table_size() as usize;
    let mut fanout = Vec::new();
    if naming_threshold >= 0 {
        fanout = vec![0i32; size];
        let mut it = g.instances();
        while let Some(id) = it.next(g) {
            let kind = &g.inst(id).kind;
            if !matches!(kind, Kind::Name(n) if n.tentative) {
                for n in kind.inputs() {
                    fanout[n.0 as usize] += 1;
                }
            }
        }
    }

    let mut net2lit = vec![-1i32; size];
    let mut ci2net: Vec<Net> = Vec::new();
    let mut co2net: Vec<Net> = Vec::new();
    net2lit[Net::ZERO.0 as usize] = 0;
    net2lit[Net::ONE.0 as usize] = 1;
    // X is taken as 0
    net2lit[Net::UNDEF.0 as usize] = 0;

    let nets = g.nets();
    let (mut n_ci, mut n_and) = (0, 0);
    for &(_, id, _) in &nets {
        let inst = g.inst(id);
        if is_tie(&inst.kind) || inst.output_width() == 0 {
            continue;
        }
        if is_aig(&inst.kind) {
            n_and += 1;
        } else {
            n_ci += 1;
        }
    }

    let mut gia = Gia::start(abc, 1 + n_ci + n_and + n_ci, "syn").map_err(|e| e.to_string())?;
    for &(net, id, off) in &nets {
        let kind = &g.inst(id).kind;
        if is_tie(kind) || g.inst(id).output_width() == 0 {
            continue;
        }
        let off = off as usize;
        let lit = |n: Net| net2lit[n.0 as usize];
        use crate::ir::instance::BinOp;
        net2lit[net.0 as usize] = match kind {
            Kind::Bin(BinOp::And, a, b) => gia.hash_and(lit(a[off]), lit(b[off])),
            Kind::Bin(BinOp::Andnot, a, b) => gia.hash_and(lit(a[off]), lit(b[off]) ^ 1),
            // Or(a, b) = ~(~a & ~b)
            Kind::Bin(BinOp::Or, a, b) => gia.hash_and(lit(a[off]) ^ 1, lit(b[off]) ^ 1) ^ 1,
            Kind::Not(a) => lit(a[off]) ^ 1,
            Kind::Buffer(a) => lit(a[off]),
            _ => {
                ci2net.push(net);
                gia.append_ci()
            }
        };
    }

    // the outputs: nets an AIG cell drives that a non-AIG cell reads, once each
    let mut po_set = BTreeSet::new();
    let mut it = g.instances();
    while let Some(id) = it.next(g) {
        let kind = &g.inst(id).kind;
        if is_aig(kind) || is_tie(kind) {
            continue;
        }
        let tentative_name = matches!(kind, Kind::Name(n) if n.tentative);
        if tentative_name && naming_threshold < 0 {
            continue;
        }
        for fanin in kind.inputs() {
            if fanin.0 <= 2 {
                continue;
            }
            let fid = fanin.0 as usize;
            if net2lit[fid] < 0 {
                continue;
            }
            if tentative_name && fanout[fid] < naming_threshold {
                continue;
            }
            if !is_aig(&g.inst(g.resolve(fanin).0).kind) {
                continue;
            }
            if po_set.insert(fid) {
                gia.append_co(net2lit[fid]);
                co2net.push(fanin);
            }
        }
    }

    gia.cleanup().map_err(|e| e.to_string())?;
    println!(
        "[INFO SYN-0020] abc_roundtrip: exported {} ANDs, {} CIs, {} COs",
        gia.and_count(),
        gia.ci_count(),
        gia.co_count()
    );

    // ---- ABC ----
    abc.set_gia(gia);
    if abc.execute(commands).is_err() {
        println!("[WARNING SYN-0021] abc_roundtrip: ABC command returned error");
    }
    let Some(gia) = abc.take_gia() else {
        return Err("[ERROR SYN-0022] abc_roundtrip: no GIA after ABC commands".to_string());
    };
    println!(
        "[INFO SYN-0023] abc_roundtrip: after ABC: {} ANDs, {} CIs, {} COs",
        gia.and_count(),
        gia.ci_count(),
        gia.co_count()
    );

    // ---- import ----
    let mut obj2lit = vec![Literal::ZERO; gia.object_count() as usize];
    for (i, &net) in ci2net.iter().enumerate() {
        if let Some(id) = gia.ci_id(i as i32) {
            obj2lit[id as usize] = Literal::pos(net);
        }
    }
    for id in 0..gia.object_count() {
        if let Some(GiaObj::And(f0, c0, f1, c1)) = gia.object(id) {
            let a = if c0 { not(obj2lit[f0 as usize]) } else { obj2lit[f0 as usize] };
            let b = if c1 { not(obj2lit[f1 as usize]) } else { obj2lit[f1 as usize] };
            obj2lit[id as usize] = and(g, a, b);
        }
    }
    for (i, &net) in co2net.iter().enumerate() {
        let Some(GiaObj::Co(f, c)) = gia.co_id(i as i32).and_then(|id| gia.object(id)) else { continue };
        let driver = if c { not(obj2lit[f as usize]) } else { obj2lit[f as usize] };
        let result = g.emit_control(driver);
        g.force_replace(&[net], &[result]);
    }
    Ok(())
}
