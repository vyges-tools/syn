// SPDX-License-Identifier: Apache-2.0
//! The combinational loop check (the reference's `check_combinational_loops`), run in
//! `synthesize` after the constants are folded and before the rewriting round trip, as there.
//!
//! The reference rejects every loop: optimization does not keep the state a loop holds, so a loop
//! mapped as logic would silently change the design. It finds the loops itself instead of trusting
//! normalize's loop breakers, because normalize treats every library cell as depending on all its
//! inputs (and a sequential one as a boundary): here a library cell's output depends only on the
//! inputs its Liberty model ties it to ([`LibCell::comb_deps`]), so a RAM read port or a latch
//! cuts a loop and a cell whose one output does not use an input does not close one through it.
//!
//! Each loop (strongly connected component of the combinational dependencies) is named in a
//! warning, SYN-0079, by the nets of one cycle through it (at most ten loops, eight nets each);
//! then the run stops with SYN-0080. Our latch inference runs earlier (in `sv_elaborate`), so a
//! latch it made is a library latch here and passes; a loop it left (no latch cell, or not a
//! latch form) is rejected as the reference rejects it.
//!
//! [`LibCell::comb_deps`]: crate::ir::instance::LibCell::comb_deps

use std::collections::HashMap;

use crate::ir::instance::Pin;
use crate::ir::net::Net;
use crate::ir::{Graph, Kind};

const MAX_REPORTED_LOOPS: usize = 10;
const MAX_REPORTED_NAMES: usize = 8;

/// The reference's `collectNetNames`: each net's user-visible name, a name that is not tentative
/// preferred; among equals the first in instance order. A vector name's bit is `name[index]`,
/// counting from `from` toward `to`.
fn collect_net_names(g: &Graph) -> HashMap<u32, String> {
    let mut names: HashMap<u32, String> = HashMap::new();
    let mut tentative: HashMap<u32, bool> = HashMap::new();
    for id in g.instance_list() {
        let Kind::Name(name) = &g.inst(id).kind else { continue };
        for (i, &net) in name.value.iter().enumerate() {
            if net.is_const() {
                continue;
            }
            if let Some(&have_tentative) = tentative.get(&net.0) {
                if name.tentative || !have_tentative {
                    continue;
                }
            }
            let mut s = name.name.clone();
            if name.is_vector {
                let i = i as u32;
                let index = if name.from <= name.to { name.from + i } else { name.from - i };
                s.push_str(&format!("[{index}]"));
            }
            names.insert(net.0, s);
            tentative.insert(net.0, name.tentative);
        }
    }
    names
}

/// The reference's `CombFanins::visit`: the nets `net` depends on combinationally. A register,
/// a black box and an input cut the dependency; a library cell's output depends on the inputs its
/// model names (all of them when the layout and the model disagree); a bitwise cell's bit on its
/// own operands' bit; anything else on all its inputs. Constants are not visited.
fn comb_fanins(g: &Graph, net: Net) -> Vec<Net> {
    let mut out = Vec::new();
    if net.is_const() {
        return out;
    }
    let (id, offset) = g.resolve(net);
    let kind = &g.inst(id).kind;
    let mut visit = |n: Net| {
        if !n.is_const() {
            out.push(n);
        }
    };
    if let Kind::Target(cell, inputs) = kind {
        match cell.comb_deps.get(offset as usize) {
            Some(deps) => {
                for &i in deps {
                    if let Some(&n) = inputs.get(i as usize) {
                        visit(n);
                    }
                }
            }
            None => {
                for &n in inputs {
                    visit(n);
                }
            }
        }
        return out;
    }
    if kind.has_state() || matches!(kind, Kind::Input(..)) {
        return out;
    }
    let pins: Vec<Pin> = if kind.is_sliceable() { kind.slice_pins(offset) } else { kind.pins() };
    for p in pins {
        visit(kind.get(p));
    }
    out
}

/// The reference's `Sccs`: each net's component, and one net of each component that holds a cycle.
struct Sccs {
    id: Vec<u32>,
    cyclic: Vec<Net>,
}

/// The reference's `computeSccs`: iterative Tarjan over every net, roots in net order; a
/// component holds a cycle when it has more than one net or its one net feeds itself.
fn compute_sccs(g: &Graph) -> Sccs {
    const UNVISITED: u32 = u32::MAX;
    let n = g.table_size() as usize;
    let mut sccs = Sccs { id: vec![UNVISITED; n], cyclic: Vec::new() };
    let mut index = vec![UNVISITED; n];
    let mut lowlink = vec![0u32; n];
    let mut on_stack = vec![false; n];
    let mut stack: Vec<u32> = Vec::new();
    let (mut next_index, mut next_scc) = (0u32, 0u32);

    struct Frame {
        id: u32,
        fanins: Vec<u32>,
        self_loop: bool,
        next: usize,
    }
    let mut make_frame = |id: u32, index: &mut Vec<u32>, lowlink: &mut Vec<u32>, stack: &mut Vec<u32>, on_stack: &mut Vec<bool>| {
        let fanins: Vec<u32> = comb_fanins(g, Net(id)).into_iter().map(|f| f.0).collect();
        let self_loop = fanins.contains(&id);
        index[id as usize] = next_index;
        lowlink[id as usize] = next_index;
        next_index += 1;
        stack.push(id);
        on_stack[id as usize] = true;
        Frame { id, fanins, self_loop, next: 0 }
    };

    for (root, ..) in g.nets() {
        if root.is_const() || index[root.0 as usize] != UNVISITED {
            continue;
        }
        let mut call_stack = vec![make_frame(root.0, &mut index, &mut lowlink, &mut stack, &mut on_stack)];
        while let Some(top) = call_stack.len().checked_sub(1) {
            if call_stack[top].next < call_stack[top].fanins.len() {
                let fanin = call_stack[top].fanins[call_stack[top].next];
                call_stack[top].next += 1;
                if index[fanin as usize] == UNVISITED {
                    let f = make_frame(fanin, &mut index, &mut lowlink, &mut stack, &mut on_stack);
                    call_stack.push(f);
                } else if on_stack[fanin as usize] {
                    let id = call_stack[top].id as usize;
                    lowlink[id] = lowlink[id].min(index[fanin as usize]);
                }
                continue;
            }
            let frame = call_stack.pop().expect("the loop runs while a frame is on the stack");
            let id = frame.id as usize;
            if lowlink[id] == index[id] {
                let mut size = 0usize;
                loop {
                    let member = stack.pop().expect("a component's root is still on the stack") as usize;
                    on_stack[member] = false;
                    sccs.id[member] = next_scc;
                    size += 1;
                    if member == id {
                        break;
                    }
                }
                if size > 1 || frame.self_loop {
                    sccs.cyclic.push(Net(frame.id));
                }
                next_scc += 1;
            }
            if let Some(parent) = call_stack.last() {
                let p = parent.id as usize;
                lowlink[p] = lowlink[p].min(lowlink[id]);
            }
        }
    }
    sccs
}

/// The reference's `findCycle`: a cycle through `net` inside its component, depth first from
/// `net` (the last fanin found is expanded first; each net is reached once, from the first net
/// that finds it), as the nets from `net` back to `net`. Empty when there is none.
fn find_cycle(g: &Graph, sccs: &Sccs, net: Net) -> Vec<Net> {
    let scc = sccs.id[net.0 as usize];
    let mut parent: HashMap<u32, Net> = HashMap::new();
    let mut stack: Vec<Net> = Vec::new();
    let expand = |from: Net, parent: &mut HashMap<u32, Net>, stack: &mut Vec<Net>| {
        for fanin in comb_fanins(g, from) {
            if sccs.id[fanin.0 as usize] == scc && !parent.contains_key(&fanin.0) {
                parent.insert(fanin.0, from);
                stack.push(fanin);
            }
        }
    };
    expand(net, &mut parent, &mut stack);
    while let Some(cur) = stack.pop() {
        if cur == net {
            let mut cycle = vec![net];
            let mut n = parent[&net.0];
            while n != net {
                cycle.push(n);
                n = parent[&n.0];
            }
            cycle.push(net);
            return cycle;
        }
        expand(cur, &mut parent, &mut stack);
    }
    Vec::new()
}

/// The reference's `checkCombinationalLoops`: normalize (only live logic is checked), find the
/// loops, name each in a SYN-0079 warning (printed here) and fail with the SYN-0080 line.
pub fn check_combinational_loops(g: &mut Graph) -> Result<(), String> {
    g.normalize();
    let sccs = compute_sccs(g);
    if sccs.cyclic.is_empty() {
        return Ok(());
    }
    let names = collect_net_names(g);
    for &start in sccs.cyclic.iter().take(MAX_REPORTED_LOOPS) {
        let mut cycle = find_cycle(g, &sccs, start);
        // the start net closes the cycle a second time
        cycle.pop();
        let mut nets = String::new();
        let mut reported = 0;
        for net in cycle {
            let name = names.get(&net.0);
            // an unnamed loop breaker repeats its input, which is on the cycle too
            if name.is_none() && matches!(g.inst(g.resolve(net).0).kind, Kind::LoopBreaker(_)) {
                continue;
            }
            if reported == MAX_REPORTED_NAMES {
                nets.push_str(", ...");
                break;
            }
            if reported > 0 {
                nets.push_str(", ");
            }
            match name {
                Some(n) => nets.push_str(n),
                None => nets.push_str(&format!("%{}", net.0)),
            }
            reported += 1;
        }
        println!("[WARNING SYN-0079] Combinational loop through: {nets}");
    }
    Err(format!(
        "[ERROR SYN-0080] Design contains {} combinational loop(s). Combinational loops, including latches inferred from incomplete assignments in always blocks, are not supported.",
        sccs.cyclic.len()
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The reference rule: a net that feeds itself through logic is one loop, named by a cycle
    /// through it; `y = p ^ c` hangs off the loop and is not on it.
    #[test]
    fn a_two_gate_loop_is_one_loop() {
        let mut g = Graph::new();
        let a = g.add(Kind::Input("a".into(), 1))[0];
        let b = g.add(Kind::Input("b".into(), 1))[0];
        let p = g.add(Kind::Buffer(vec![Net::UNDEF]));
        let q = g.add(Kind::Bin(crate::ir::BinOp::Or, vec![p[0]], vec![b]))[0];
        let and = g.add(Kind::Bin(crate::ir::BinOp::And, vec![a], vec![q]))[0];
        let (id, _) = g.resolve(p[0]);
        g.inst_mut(id).kind = Kind::Buffer(vec![and]);
        g.add(Kind::Output("y".into(), vec![q]));
        let e = check_combinational_loops(&mut g).expect_err("a loop is rejected");
        assert!(e.starts_with("[ERROR SYN-0080] Design contains 1 combinational loop(s)."), "{e}");
    }

    /// The same with an xor in place of the register: the reference rejects it.
    #[test]
    fn the_same_feedback_without_the_register_is_a_loop() {
        let src = "%3:1 = input \"d\"\n%5:0 = output \"q\" %6\n%6:1 = buf %7\n%7:1 = xor %3 %6\n";
        let mut g = crate::ir::parse::parse(src, None).expect("the IR text is well formed");
        assert!(check_combinational_loops(&mut g).is_err());
    }

    /// No loop: the check passes.
    #[test]
    fn no_loop_passes() {
        let mut g = Graph::new();
        let a = g.add(Kind::Input("a".into(), 1))[0];
        let n = g.add(Kind::Not(vec![a]))[0];
        g.add(Kind::Output("y".into(), vec![n]));
        assert_eq!(check_combinational_loops(&mut g), Ok(()));
    }

    /// A register's output cuts the dependency: `q <= q ^ a` is no combinational loop.
    #[test]
    fn a_register_feedback_is_no_loop() {
        let src = "%3:1 = input \"clk\"\n%4:1 = input \"d\"\n%5:0 = output \"q\" %6\n%6:1 = dff %7 clk=%3\n%7:1 = xor %4 %6\n";
        let mut g = crate::ir::parse::parse(src, None).expect("the IR text is well formed");
        assert_eq!(check_combinational_loops(&mut g), Ok(()));
    }
}
