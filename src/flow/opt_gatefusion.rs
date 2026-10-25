// SPDX-License-Identifier: Apache-2.0
//! Gate fusion: a library cell whose output only feeds one input of another cell, the pair
//! replaced by one smaller library cell computing the same function.
//!
//! Functions are sums of products whose cubes share no inputs ("disjoint"); two cells' sums
//! compose when the driver's sum is one of the reader's cubes, or a cube of single literals that
//! negates into one; the fused sum is matched to a cell by its fingerprint, the sorted (positive,
//! negative) literal counts of its cubes and the output polarity.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::sync::Arc;

use vyges_loom::liberty_func::Func;

use crate::ir::graph::InstId;
use crate::ir::instance::{LibCell, LibDirection};
use crate::ir::net::Net;
use crate::ir::{Graph, Kind};
use crate::library::Libraries;

/// A product: bit `i` of `pos` / `neg` is input `i` read positive / negative.
#[derive(Clone, Copy, PartialEq, Eq, Default, Debug)]
struct Cube {
    pos: u32,
    neg: u32,
}

impl Cube {
    fn support(&self) -> u32 {
        self.pos | self.neg
    }
    fn size(&self) -> u32 {
        self.support().count_ones()
    }
    fn npos(&self) -> u32 {
        self.pos.count_ones()
    }
    fn nneg(&self) -> u32 {
        self.neg.count_ones()
    }
    fn contradictory(&self) -> bool {
        self.pos & self.neg != 0
    }
    fn merge(&self, o: &Cube) -> Cube {
        Cube { pos: self.pos | o.pos, neg: self.neg | o.neg }
    }
}

/// By (positive count, negative count), then (pos, neg): two sums with one fingerprint list their
/// cubes in matching order.
impl Ord for Cube {
    fn cmp(&self, o: &Self) -> std::cmp::Ordering {
        (self.npos(), self.nneg(), self.pos, self.neg).cmp(&(o.npos(), o.nneg(), o.pos, o.neg))
    }
}

impl PartialOrd for Cube {
    fn partial_cmp(&self, o: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(o))
    }
}

#[derive(Clone, Default, Debug)]
struct Sop {
    cubes: BTreeSet<Cube>,
    /// The output complemented.
    oc: bool,
}

impl Sop {
    fn is_disjoint(&self) -> bool {
        let mut seen = 0;
        for c in &self.cubes {
            if seen & c.support() != 0 {
                return false;
            }
            seen |= c.support();
        }
        true
    }

    /// Cubes another cube's literals are a subset of dropped.
    fn absorb(&mut self) {
        let absorbed: Vec<Cube> = self
            .cubes
            .iter()
            .filter(|c1| self.cubes.iter().any(|c2| c2 != *c1 && c1.pos & c2.pos == c2.pos && c1.neg & c2.neg == c2.neg))
            .copied()
            .collect();
        for c in absorbed {
            self.cubes.remove(&c);
        }
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
struct Fingerprint {
    cube_types: Vec<(u32, u32)>,
    oc: bool,
}

fn fingerprint(sop: &Sop) -> Fingerprint {
    let mut cube_types: Vec<(u32, u32)> = sop.cubes.iter().map(|c| (c.npos(), c.nneg())).collect();
    cube_types.sort();
    Fingerprint { cube_types, oc: sop.oc }
}

const MAX_CUBES: usize = 1024;

fn sop_cross(a: Option<Sop>, b: Option<Sop>) -> Option<Sop> {
    let (a, b) = (a?, b?);
    let mut result = Sop::default();
    for ca in &a.cubes {
        for cb in &b.cubes {
            let merged = ca.merge(cb);
            if !merged.contradictory() {
                result.cubes.insert(merged);
            }
            if result.cubes.len() > MAX_CUBES {
                return None;
            }
        }
    }
    result.absorb();
    Some(result)
}

fn sop_union(a: Option<Sop>, b: Option<Sop>) -> Option<Sop> {
    let (a, b) = (a?, b?);
    let mut result = Sop { cubes: a.cubes, oc: false };
    result.cubes.extend(b.cubes);
    Some(result)
}

/// The expression (negated when `negated`) as a sum of products over `ins`; None with an XOR.
fn fexpr_to_sop(f: &Func, negated: bool, ins: &[&str]) -> Option<Sop> {
    let one = |c: Cube| Some(Sop { cubes: BTreeSet::from([c]), oc: false });
    match f {
        Func::Port(p) => {
            // ⚠️ A port that is not an input: the reference's index is -1, and the shift by it
            // is the machine's (the count taken mod 32).
            let idx = ins.iter().position(|i| i == p).map_or(-1i32, |i| i as i32);
            let bit = 1u32.wrapping_shl(idx as u32);
            one(if negated { Cube { pos: 0, neg: bit } } else { Cube { pos: bit, neg: 0 } })
        }
        Func::Not(a) => fexpr_to_sop(a, !negated, ins),
        Func::And(a, b) if negated => sop_union(fexpr_to_sop(a, true, ins), fexpr_to_sop(b, true, ins)),
        Func::And(a, b) => sop_cross(fexpr_to_sop(a, false, ins), fexpr_to_sop(b, false, ins)),
        Func::Or(a, b) if negated => sop_cross(fexpr_to_sop(a, true, ins), fexpr_to_sop(b, true, ins)),
        Func::Or(a, b) => sop_union(fexpr_to_sop(a, false, ins), fexpr_to_sop(b, false, ins)),
        Func::Xor(..) => None,
        Func::One if negated => Some(Sop::default()),
        Func::One => one(Cube::default()),
        Func::Zero if negated => one(Cube::default()),
        Func::Zero => Some(Sop::default()),
    }
}

/// The disjoint sum of the function or of its complement (marked `oc`); both disjoint: the one
/// with more cubes, the function's on a tie.
fn extract_sop(f: &Func, ins: &[&str]) -> Option<Sop> {
    let direct = fexpr_to_sop(f, false, ins).filter(Sop::is_disjoint);
    let negated = fexpr_to_sop(f, true, ins).map(|mut s| {
        s.oc = true;
        s
    });
    let negated = negated.filter(Sop::is_disjoint);
    match (direct, negated) {
        (None, n) => n,
        (d, None) => d,
        (Some(d), Some(n)) => Some(if n.cubes.len() > d.cubes.len() { n } else { d }),
    }
}

#[derive(Clone)]
struct CellInfo {
    cell: Arc<LibCell>,
    sop: Sop,
}

struct CellIndex {
    by_fingerprint: BTreeMap<Fingerprint, CellInfo>,
    by_cell: HashMap<*const LibCell, CellInfo>,
}

/// Every cell not `dont_use` and not sequential with only inputs and outputs, one output with a
/// function, and 1 to 16 inputs, by cell; and by fingerprint, the smallest area (the first one met,
/// libraries in read order and cells by name, on a tie).
fn build_index(libs: &Libraries) -> CellIndex {
    let mut result = CellIndex { by_fingerprint: BTreeMap::new(), by_cell: HashMap::new() };
    for cell in libs.cells() {
        if cell.dont_use || cell.is_sequential {
            continue;
        }
        let mut inputs = Vec::new();
        let mut outputs = Vec::new();
        let mut skip = false;
        for p in cell.ports.iter().filter(|p| !p.pwr_gnd) {
            match p.direction {
                LibDirection::Input => inputs.push(p.name.as_str()),
                LibDirection::Output => outputs.push(p),
                _ => {
                    skip = true;
                    break;
                }
            }
        }
        if skip || outputs.len() != 1 || inputs.is_empty() || inputs.len() > 16 {
            continue;
        }
        let is_port = |n: &str| cell.ports.iter().any(|p| p.name == n);
        let Some(func) = outputs[0].function.as_deref().and_then(|t| Func::parse_in(t, is_port)) else { continue };
        let Some(sop) = extract_sop(&func, &inputs) else { continue };
        let fp = fingerprint(&sop);
        let info = CellInfo { cell: cell.clone(), sop };
        result.by_cell.insert(Arc::as_ptr(cell), info.clone());
        let better = match result.by_fingerprint.get(&fp) {
            None => true,
            Some(have) => cell.area < have.cell.area,
        };
        if better {
            result.by_fingerprint.insert(fp, info);
        }
    }
    result
}

/// B's sum with its input `index_b` replaced by A's sum (A's inputs moved up to bits 16 on):
/// A's sum is a cube of B read in A's polarity, or A's cubes are single literals and B has a cube
/// reading the link the other way (A negated into one cube).
fn compose_sops(sop_a: &Sop, sop_b: &Sop, index_b: u32) -> Option<Sop> {
    let link_b = 1u32 << index_b;
    if (!sop_a.oc && sop_b.cubes.contains(&Cube { pos: link_b, neg: 0 }))
        || (sop_a.oc && sop_b.cubes.contains(&Cube { pos: 0, neg: link_b }))
    {
        let mut result = Sop { cubes: sop_b.cubes.clone(), oc: sop_b.oc };
        result.cubes.remove(&Cube { pos: link_b, neg: 0 });
        result.cubes.remove(&Cube { pos: 0, neg: link_b });
        for cube in &sop_a.cubes {
            result.cubes.insert(Cube { pos: cube.pos << 16, neg: cube.neg << 16 });
        }
        return Some(result);
    }

    let mut primed = Cube::default();
    for cube in &sop_a.cubes {
        if cube.size() != 1 {
            return None;
        }
        primed.pos |= cube.neg;
        primed.neg |= cube.pos;
    }
    for c in &sop_b.cubes {
        if (sop_a.oc && link_b & c.pos != 0) || (!sop_a.oc && link_b & c.neg != 0) {
            let mut result = Sop { cubes: sop_b.cubes.clone(), oc: sop_b.oc };
            result.cubes.remove(c);
            result.cubes.insert(Cube { pos: (c.pos & !link_b) | primed.pos << 16, neg: (c.neg & !link_b) | primed.neg << 16 });
            return Some(result);
        }
    }
    None
}

/// The set bits, lowest first.
fn set_bits(mut bits: u32) -> impl Iterator<Item = u32> {
    std::iter::from_fn(move || {
        if bits == 0 {
            return None;
        }
        let b = bits.trailing_zeros();
        bits &= bits - 1;
        Some(b)
    })
}

/// Rounds until one fuses nothing: each round normalizes, counts the readers each net has among
/// mapped cells, then walks the instances in slot order; a cell B (indexed) takes its first input
/// whose driver A is an indexed cell read once, not yet fused this round, whose sum composes with
/// B's into a fingerprint some cell has, of smaller area than the two. An input driven by a cell
/// that is not indexed ends B's turn. Prints `[INFO SYN-0040]` and the cells removed (SYN-0044) and
/// added (SYN-0045).
pub fn gate_fusion_opt(g: &mut Graph, libs: &Libraries) {
    g.normalize();
    let index = build_index(libs);
    if index.by_fingerprint.is_empty() {
        return;
    }

    let mut total_fusions = 0;
    let mut total_area_delta = 0.0f32;
    // ⚠️ The reference orders these by cell address; here, by name.
    let mut removed_cells: BTreeMap<String, i32> = BTreeMap::new();
    let mut added_cells: BTreeMap<String, i32> = BTreeMap::new();

    loop {
        g.normalize();
        let mut use_counts = vec![0i32; g.table_size() as usize];
        for id in g.instance_list() {
            let kind = &g.inst(id).kind;
            if kind.is_mapped() {
                for n in kind.inputs() {
                    use_counts[n.0 as usize] += 1;
                }
            }
        }

        let mut visited: HashSet<InstId> = HashSet::new();
        let mut fusions = 0;
        let mut it = g.instances();
        while let Some(inst_b) = it.next(g) {
            let Kind::Target(cell_b, inputs_b) = &g.inst(inst_b).kind else { continue };
            if visited.contains(&inst_b) {
                continue;
            }
            let Some(info_b) = index.by_cell.get(&Arc::as_ptr(cell_b)) else { continue };
            let (cell_b, inputs_b) = (cell_b.clone(), inputs_b.clone());
            for (i, &input) in inputs_b.iter().enumerate() {
                let (inst_a, off) = g.resolve(input);
                let Kind::Target(cell_a, inputs_a) = &g.inst(inst_a).kind else { continue };
                if visited.contains(&inst_a) {
                    continue;
                }
                let Some(info_a) = index.by_cell.get(&Arc::as_ptr(cell_a)) else { break };
                let output_a = g.output(inst_a)[off as usize];
                if use_counts[output_a.0 as usize] != 1 {
                    continue;
                }
                let Some(composed) = compose_sops(&info_a.sop, &info_b.sop, i as u32) else { continue };
                let Some(fused) = index.by_fingerprint.get(&fingerprint(&composed)) else { continue };

                let area_before = cell_b.area + cell_a.area;
                let area_after = fused.cell.area;
                if area_after >= area_before {
                    continue;
                }
                total_area_delta += area_after - area_before;

                // the two sums' cubes in lockstep, literals matched lowest first
                let mut fused_inputs = vec![Net::SENTINEL; inputs_b.len() + inputs_a.len() - 1];
                for (c, t) in composed.cubes.iter().zip(&fused.sop.cubes) {
                    for (s, t) in set_bits(c.pos).zip(set_bits(t.pos)).chain(set_bits(c.neg).zip(set_bits(t.neg))) {
                        fused_inputs[t as usize] = if s >= 16 { inputs_a[s as usize - 16] } else { inputs_b[s as usize] };
                    }
                }
                let cell_a = cell_a.clone();
                let fused_out = g.add(Kind::Target(fused.cell.clone(), fused_inputs));
                let out_b = g.output(inst_b)[0];
                g.force_replace(&[out_b], &[fused_out[0]]);

                *removed_cells.entry(cell_a.name.clone()).or_default() += 1;
                *removed_cells.entry(cell_b.name.clone()).or_default() += 1;
                *added_cells.entry(fused.cell.name.clone()).or_default() += 1;
                visited.insert(inst_a);
                visited.insert(inst_b);
                fusions += 1;
                break;
            }
        }
        total_fusions += fusions;
        if fusions == 0 {
            break;
        }
    }
    if total_fusions > 0 {
        g.normalize();
    }
    println!("[INFO SYN-0040] gatefusion: {total_fusions} fusions applied, area delta {total_area_delta:.4}");
    for (cell, count) in &removed_cells {
        println!("[INFO SYN-0044]   -{cell} {count}");
    }
    for (cell, count) in &added_cells {
        println!("[INFO SYN-0045]   +{cell} {count}");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Rule: NAND2 = !(A1 & A2) is disjoint both ways; its complement (one cube A1A2, oc) has fewer
    // cubes than the direct sum (!A1 + !A2), so the direct sum is kept.
    #[test]
    fn a_nand_is_the_sum_of_its_negated_inputs() {
        let f = Func::parse_in("!(A1 & A2)", |_| true).unwrap();
        let sop = extract_sop(&f, &["A1", "A2"]).unwrap();
        assert!(!sop.oc);
        assert_eq!(fingerprint(&sop).cube_types, vec![(0, 1), (0, 1)]);
    }

    // Rule: a sum is kept in the polarity with more cubes, so an AND2 is {!A1, !A2} complemented
    // and a NOR2 {B1, B2} complemented. The AND's single-literal cubes negate into one cube A1A2,
    // which takes the place of the NOR cube reading the link: !(A1A2 + B2), an AOI21. Into an OR2
    // ({B1, B2}, direct) the same gives A1A2 + B2, an AO21.
    #[test]
    fn single_literal_drivers_negate_into_one_cube() {
        let and = extract_sop(&Func::parse_in("A1 & A2", |_| true).unwrap(), &["A1", "A2"]).unwrap();
        assert!(and.oc && and.cubes.len() == 2);
        let nor = extract_sop(&Func::parse_in("!(B1 | B2)", |_| true).unwrap(), &["B1", "B2"]).unwrap();
        let aoi = compose_sops(&and, &nor, 0).unwrap();
        assert_eq!(fingerprint(&aoi), Fingerprint { cube_types: vec![(1, 0), (2, 0)], oc: true });
        let or = extract_sop(&Func::parse_in("B1 | B2", |_| true).unwrap(), &["B1", "B2"]).unwrap();
        let ao = compose_sops(&and, &or, 0).unwrap();
        assert_eq!(fingerprint(&ao), Fingerprint { cube_types: vec![(1, 0), (2, 0)], oc: false });
    }

    // Rule: cubes order by literal counts before their bits.
    #[test]
    fn cubes_order_by_counts_first() {
        assert!(Cube { pos: 0b100, neg: 0 } < Cube { pos: 0b11, neg: 0 });
        assert!(Cube { pos: 0b1, neg: 0 } < Cube { pos: 0b10, neg: 0 });
    }

    // Rule: a product of sums absorbs every cube whose literals include another cube's:
    // (A + B)(A + C) = A + AB + AC + BC = A + BC, which is disjoint.
    #[test]
    fn a_product_absorbs_its_supersets() {
        let f = Func::parse_in("(A | B) & (A | C)", |_| true).unwrap();
        let sop = fexpr_to_sop(&f, false, &["A", "B", "C"]).unwrap();
        assert_eq!(sop.cubes.iter().copied().collect::<Vec<_>>(), [Cube { pos: 0b001, neg: 0 }, Cube { pos: 0b110, neg: 0 }]);
        assert!(sop.is_disjoint());
    }

    // Rule: a product past 1024 cubes is given up: ten two-literal sums multiply out to exactly
    // 1024 cubes, eleven to 2048.
    #[test]
    fn a_product_past_1024_cubes_is_given_up() {
        let names: Vec<String> = (0..22).map(|i| format!("P{i}")).collect();
        let ins: Vec<&str> = names.iter().map(String::as_str).collect();
        let product = |n: usize| (0..n).map(|k| format!("({} | {})", names[2 * k], names[2 * k + 1])).collect::<Vec<_>>().join(" & ");
        let ten = Func::parse_in(&product(10), |_| true).unwrap();
        assert_eq!(fexpr_to_sop(&ten, false, &ins).unwrap().cubes.len(), 1024);
        let eleven = Func::parse_in(&product(11), |_| true).unwrap();
        assert!(fexpr_to_sop(&eleven, false, &ins).is_none());
    }
}
