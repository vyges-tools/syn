// SPDX-License-Identifier: Apache-2.0
//! The commands, each nothing but the sequence of stages it runs, in the reference's order.

use vyges_abc_lib::Abc;

use crate::elab::backend::ElabError;
use crate::elab::frontend::{self, Failed};
use crate::elab::hierarchy::{self, HierNaming};
use crate::flow::abc::abc_roundtrip;
use crate::flow::bitblast::bitblast;
use crate::flow::combinational_mapper::map_combinationals;
use crate::flow::constant_fold::constant_fold;
use crate::flow::import::import_targets;
use crate::flow::liveness::liveness_opt;
use crate::flow::opt_gatefusion::gate_fusion_opt;
use crate::flow::sequential_mapper::map_sequentials;
use crate::ir::Graph;
use crate::library::Libraries;

/// `sv_elaborate`: elaborate, then clean the graph up — names tentative, normalize, library cells
/// imported, normalize, constants folded, normalize. The libraries' cells are blackbox modules
/// the design may instantiate.
pub fn sv_elaborate(args: &[String], libs: &Libraries, naming: &HierNaming) -> Result<Graph, Failed> {
    let mut g = elaborate(args, libs, naming)?;
    g.make_names_tentative();
    g.normalize();
    import_targets(&mut g, libs).map_err(|e| Failed::Error(e.code, e.message))?;
    g.normalize();
    constant_fold(&mut g);
    g.normalize();
    Ok(g)
}

/// The frontend's graph, as built, with its names joined at module-instance boundaries as `naming`
/// asks (flatten's separator, kept modules); the default leaves them as the frontend made them.
pub fn elaborate(args: &[String], libs: &Libraries, naming: &HierNaming) -> Result<Graph, Failed> {
    let mut g = frontend::elaborate(args, &libs.blackboxes())?;
    if !naming.is_default() {
        // NOT in the reference `syn` (flat, `.` only): names as the Yosys reference flow's flatten.
        let b = hierarchy::instance_boundaries(args).map_err(|e| Failed::Error(74, format!("module boundaries: {e}")))?;
        let unknown = hierarchy::unknown_keep_modules(&b, naming);
        if !unknown.is_empty() {
            return Err(Failed::Error(73, format!("--keep-module: no module {} in the design", unknown.join(", "))));
        }
        hierarchy::flatten_names(&mut g, &b, naming);
    }
    Ok(g)
}

/// The first ABC round trip of `synthesize`: structural hashing and fraiging.
pub const ABC_FRAIG: &str = "&ps; &st; &fraig -v -w;";

/// The second: rewriting, a 6-input mapping and rewriting again.
pub const ABC_DC2: &str = "&ps; &st; &dc2 -v; &dc2 -v; &if -g -K 6; &dc2 -v; &dc2 -v; &dc2 -v; &ps";

fn reported(e: ElabError) -> String {
    format!("[ERROR SYN-{:04}] {}", e.code, e.message)
}

/// `synthesize` up to the export: bitblast all but arithmetic, liveness, the fraiging round trip,
/// bitblast arithmetic too, fold constants, the rewriting round trip, map the registers, map the
/// logic, fuse gates, print the counts. Names may be lost at any fanout. An error comes back as
/// the line the run reports.
pub fn synthesize(g: &mut Graph, libs: &Libraries, abc: &mut Abc) -> Result<(), String> {
    bitblast(g, false);
    let (regs, combs) = liveness_opt(g, false);
    println!("[INFO SYN-0056] liveness: replaced {regs} register bits, {combs} combinational bits");
    abc_roundtrip(g, abc, ABC_FRAIG, -1)?;
    bitblast(g, true);
    constant_fold(g);
    // DIVERGENCE D1: the reference leaves division and modulo unmapped (dropped at export).
    let divmods = crate::flow::bitblast::bitblast_divmod(g);
    if divmods > 0 {
        println!("[INFO SYN-0072] bitblasted {divmods} division/modulo cell(s) (not in the reference flow)");
    }
    abc_roundtrip(g, abc, ABC_DC2, -1)?;
    map_sequentials(g, libs).map_err(reported)?;
    map_combinationals(g, libs).map_err(reported)?;
    gate_fusion_opt(g, libs);
    print!("{}", g.stats());
    Ok(())
}
