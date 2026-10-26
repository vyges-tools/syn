// SPDX-License-Identifier: Apache-2.0
//! The timer `acd_resynth` asks, built over the database as the other engines build it: the
//! netlist from the database, the libraries, the constraints, the logic constants, one graph,
//! its delays, arrivals and requireds — and the buffer target slews the resizer's preamble finds.
//!
//! One scene and no wire parasitics (the command runs on a netlist before placement); anything
//! else is refused rather than timed some other way.

use std::collections::{BTreeSet, HashMap};

use vyges_opendb::Db;
use vyges_rsz::preamble::Libs;
use vyges_sta::graph::Graph;
use vyges_sta::liberty::Library;
use vyges_sta::liberty_parse::Group;
use vyges_sta::search::Search;

/// The design's libraries (Liberty text, in read order) and its constraints.
pub struct Timer {
    pub liberties: Vec<String>,
    pub sdc: String,
}

/// Whether every `k_` scale factor of a library multiplies by exactly 1: the timer scales a
/// delay by `1 + k · (x − nom_x)` per process, voltage and temperature at the default operating
/// conditions (none: no scaling at all), so when those equal the nominals each factor is
/// `1 + k · 0` whatever `k` is.
pub fn scale_factors_are_one(group: &Group) -> bool {
    let Some(name) = group.attr_text("default_operating_conditions") else { return true };
    let Some(oc) = group.groups_of("operating_conditions").find(|g| g.name().as_deref() == Some(name.as_str())) else {
        return true;
    };
    [("process", "nom_process"), ("voltage", "nom_voltage"), ("temperature", "nom_temperature")]
        .iter()
        .all(|(at, nom)| oc.attr_float(at) == group.attr_float(nom))
}

impl Timer {
    /// The libraries as the one scene reads them; a library whose scale factors would scale is
    /// refused (they are not modelled).
    pub fn libs(&self) -> Result<Libs, String> {
        let mut libs = Libs { scenes: vec!["default".into()], ..Libs::default() };
        for text in &self.liberties {
            let group = vyges_sta::liberty_parse::parse(text)?;
            let scales = group.simple.iter().any(|(n, _)| n.starts_with("k_")) || group.groups_of("scaling_factors").next().is_some();
            if scales && !scale_factors_are_one(&group) {
                return Err("liberty k_ scale factors away from the nominal operating conditions are not modelled".into());
            }
            libs.libs.push(Library::read(&group)?);
        }
        Ok(libs)
    }

    fn clocks(&self) -> Result<vyges_est::liberty::LibertyClocks, String> {
        let mut liberty = vyges_est::liberty::LibertyClocks::default();
        for text in &self.liberties {
            liberty.read(text)?;
        }
        Ok(liberty)
    }

    /// `Resizer::resizePreamble`'s target slews (rise, fall): the buffers found as the resizer
    /// finds them, no cell held back.
    pub fn target_slews(&self, db: &Db, libs: &Libs) -> Result<[f32; 2], String> {
        let masters = vyges_rsz::env::masters(db)?;
        let dont_use = BTreeSet::new();
        let buffers = vyges_rsz::preamble::find_buffers(libs, &masters, &dont_use, true).map_err(|e| e.message().to_string())?;
        let (tgt_slews, _, _) = vyges_rsz::preamble::find_target_loads(libs, &buffers.cells, &dont_use);
        Ok(tgt_slews)
    }

    /// Time the design and hand the graph and its searched arrivals and requireds to `f`.
    pub fn with_search<R>(&self, db: &Db, libs: &Libs, f: impl FnOnce(&Graph, &Search) -> Result<R, String>) -> Result<R, String> {
        let liberty = self.clocks()?;
        let time_scale = libs.default_library().ok_or("acd_resynth needs a liberty library")?.time_scale;
        let mut s = vyges_loom::sdc::Sdc::parse(&self.sdc).map_err(|e| format!("constraints: {e:?}"))?;
        let netlist = vyges_grt::timer::netlist(db);
        let mpins = vyges_rsz::env::master_pins(db)?;
        for (name, cell) in netlist.insts.iter().map(|i| &**i) {
            if !libs.libs.iter().any(|l| l.cells.contains_key(cell.as_str())) {
                return Err(format!("{name}: master {cell} has no Liberty cell"));
            }
        }
        // A constraint names a pin by its path name, the database by its escaped name.
        let mut by_path: HashMap<String, String> = netlist.ports.iter().map(|(p, _)| (vyges_sta::power::path_name(p), p.clone())).collect();
        for (name, cell) in netlist.insts.iter().map(|i| &**i) {
            for p in mpins.get(cell).cloned().unwrap_or_default() {
                let pin = format!("{name}/{p}");
                by_path.insert(vyges_sta::power::path_name(&pin), pin);
            }
        }
        for c in &mut s.clocks {
            for src in &mut c.sources {
                if let Some(name) = by_path.get(src.as_str()) {
                    *src = name.clone();
                }
            }
        }
        let clock_sources: Vec<String> = s.clocks.iter().filter(|c| !c.is_virtual()).flat_map(|c| c.sources.iter().cloned()).collect();
        let mut env = vyges_rsz::env::sdc_env(&s, libs, &netlist)?;
        // `ensureConstantsPropagated` seeds `set_logic_*` and `set_case_analysis` too.
        let mut constraints = vyges_est::sim::Constraints::default();
        for (cmds, map) in [(&s.logic_values, &mut constraints.logic), (&s.case_values, &mut constraints.case)] {
            for c in cmds {
                for o in &c.objects {
                    let pin = match c.accessor.as_str() {
                        "get_ports" => vyges_est::sim::Pin::Port(by_path.get(o).cloned().unwrap_or_else(|| o.clone())),
                        "get_pins" => {
                            let name = by_path.get(o).cloned().unwrap_or_else(|| o.clone());
                            let (i, t) = name.rsplit_once('/').ok_or_else(|| format!("{}: `{o}` is not an instance pin", c.cmd))?;
                            vyges_est::sim::Pin::ITerm(i.to_string(), t.to_string())
                        }
                        a => return Err(format!("{} on `{a}` objects is not modelled", c.cmd)),
                    };
                    map.insert(pin, c.constant());
                }
            }
        }
        let values = vyges_est::sim::constant_pins_constrained(db, &liberty, &constraints).map_err(|e| format!("constant propagation: {e}"))?;
        env.constants = vyges_rsz::env::constants_by_name(values);
        let propagated = !s.propagated.is_empty();
        let mut g = Graph::build_with_pins(libs.scene_slice(0), &netlist, Some(&mpins))?;
        g.sdc = env;
        if !propagated {
            g.ideal_clock = vyges_rsz::timing::clock_pins(&g, &clock_sources).into_iter().collect();
        }
        g.find_delays(&HashMap::new(), None)?;
        let ssdc = vyges_rsz::env::search_sdc_on(&s, &netlist, time_scale, propagated, false)?;
        let mut search = Search::in_graph_order(&g, &ssdc);
        search.constraints_modelled()?;
        search.find_arrivals()?;
        search.find_requireds()?;
        f(&g, &search)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lib(op: &str) -> Group {
        let text = format!(
            "library (l) {{ k_process_cell_rise : 1.2 ; nom_process : 1.00 ; nom_temperature : 25.00 ; nom_voltage : 1.10 ;
               operating_conditions (typical) {{ {op} }} default_operating_conditions : typical ; }}"
        );
        vyges_sta::liberty_parse::parse(&text).expect("parses")
    }

    /// A delay is scaled by `1 + k · (x − nom_x)` per process, voltage and temperature at the
    /// default operating conditions, so k factors scale nothing when those ARE the nominals
    /// (Nangate45's typical corner: 36 `k_` lines, every factor exactly 1); one step away and
    /// they would, which is refused rather than timed unscaled.
    #[test]
    fn scale_factors_are_one_only_at_the_nominals() {
        assert!(scale_factors_are_one(&lib("process : 1.00 ; voltage : 1.10 ; temperature : 25.00 ;")));
        assert!(!scale_factors_are_one(&lib("process : 1.00 ; voltage : 0.95 ; temperature : 25.00 ;")));
        assert!(!scale_factors_are_one(&lib("process : 1.00 ; voltage : 1.10 ; temperature : 125.00 ;")));
    }
}
