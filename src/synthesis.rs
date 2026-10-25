// SPDX-License-Identifier: Apache-2.0
//! The commands, each nothing but the sequence of stages it runs, in the reference's order.

use crate::elab::frontend::{self, Failed};
use crate::flow::constant_fold::constant_fold;
use crate::flow::import::import_targets;
use crate::ir::Graph;
use crate::library::Libraries;

/// `sv_elaborate`: elaborate, then clean the graph up — names tentative, normalize, library cells
/// imported, normalize, constants folded, normalize. The libraries' cells are blackbox modules
/// the design may instantiate.
pub fn sv_elaborate(args: &[String], libs: &Libraries) -> Result<Graph, Failed> {
    let mut g = frontend::elaborate(args, &libs.blackboxes())?;
    g.make_names_tentative();
    g.normalize();
    import_targets(&mut g, libs).map_err(|e| Failed::Error(e.code, e.message))?;
    g.normalize();
    constant_fold(&mut g);
    g.normalize();
    Ok(g)
}

/// The first ABC round trip of `synthesize`: structural hashing and fraiging.
pub const ABC_FRAIG: &str = "&ps; &st; &fraig -v -w;";

/// The second: rewriting, a 6-input mapping and rewriting again.
pub const ABC_DC2: &str = "&ps; &st; &dc2 -v; &dc2 -v; &if -g -K 6; &dc2 -v; &dc2 -v; &dc2 -v; &ps";
