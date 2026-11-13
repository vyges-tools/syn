// SPDX-License-Identifier: Apache-2.0
//! Module-instance boundaries in the flat design's names, joined as the reference flow's `flatten`
//! joins them.
//!
//! Elaboration flattens: a signal of an instance is named by its path below the top, every scope
//! joined by `.` (`u_m0.g[1].u_l.t`). The Yosys flow that is the QoR reference instead flattens a
//! hierarchical design, and joins only a MODULE INSTANCE boundary with its separator (`flatten
//! -separator`, ORFS `SYNTH_HIER_SEPARATOR`, default `.`); a generate block stays part of the
//! object's own name. A module kept by synthesis (ORFS `SYNTH_KEEP_MODULES`) and flattened later
//! by the reference's netlist reader is joined with that reader's divider, `/`.
//!
//! The frontend hands over the joined string only, so the boundaries are read from slang's
//! elaborated design (its JSON form, as `sv-ranges` reads it): each module instance's path, in
//! the netlist's form, and its definition.

use std::collections::{BTreeSet, HashMap};

use serde_json::Value;

use crate::ir::{Graph, Kind};

/// The divider the reference's netlist reader joins a kept module's contents with (`pathName`).
pub const KEPT_SEPARATOR: &str = "/";

/// How names join a module-instance boundary: the default (`.`, nothing kept) is elaboration's own.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct HierNaming {
    /// The separator at a boundary flattened by synthesis; `None` is `.`.
    pub separator: Option<String>,
    /// Definitions whose instances synthesis keeps: their boundary is joined with [`KEPT_SEPARATOR`].
    pub keep_modules: Vec<String>,
}

impl HierNaming {
    /// Whether every name stays as elaboration made it.
    #[must_use]
    pub fn is_default(&self) -> bool {
        self.separator.as_deref().is_none_or(|s| s == ".") && self.keep_modules.is_empty()
    }
}

/// Each module instance below the top: its path as the netlist names it, and its definition.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct Boundaries {
    pub instances: HashMap<String, String>,
}

/// The module-instance boundaries of the design the slang arguments name. A module the sources do
/// not define (a library cell) is not elaborated, so it is not an error here. Err: slang rejected
/// the arguments or reported an error (its report).
pub fn instance_boundaries(args: &[String]) -> Result<Boundaries, String> {
    let mut words = super::frontend::split_args(args);
    if !words.iter().any(|w| w == "--ignore-unknown-modules") {
        words.push("--ignore-unknown-modules".to_string());
    }
    let mut c = vyges_slang_lib::compile(&words).map_err(|e| e.to_string())?;
    if c.status() != vyges_slang_lib::Status::Ok || c.error_count() > 0 {
        return Err(c.report().trim().to_string());
    }
    let json = c.ast_json(false).ok_or_else(|| "slang produced no elaborated design".to_string())?;
    let ast: Value = serde_json::from_str(&json).map_err(|e| format!("slang's design JSON: {e}"))?;
    Ok(boundaries(&ast))
}

/// The boundaries in an elaborated design (`{"design": …, "definitions": …}`). Only a module's
/// instance is a boundary: the frontend dissolves an interface into its user.
pub fn boundaries(ast: &Value) -> Boundaries {
    let mut bodies: HashMap<u64, &Value> = HashMap::new();
    super::ranges::collect_bodies(&ast["design"], &mut bodies);
    let mut modules: BTreeSet<&str> = BTreeSet::new();
    for d in ast["definitions"].as_array().into_iter().flatten() {
        if d["definitionKind"] == "Module" {
            if let Some(n) = d["name"].as_str() {
                modules.insert(n);
            }
        }
    }
    let mut w = Walk { bodies, modules, out: Boundaries::default() };
    for m in ast["design"]["members"].as_array().into_iter().flatten() {
        if m["kind"] == "Instance" {
            w.body(&m["body"], "");
        }
    }
    w.out
}

struct Walk<'a> {
    /// A body slang printed once, by address: a later instance of it refers to it as `"<addr> <name>"`.
    bodies: HashMap<u64, &'a Value>,
    /// Definitions that are modules.
    modules: BTreeSet<&'a str>,
    out: Boundaries,
}

impl<'a> Walk<'a> {
    /// The body an instance refers to, printed in place or by reference.
    fn resolve(&self, b: &'a Value) -> Option<&'a Value> {
        match b {
            Value::String(r) => r.split_whitespace().next().and_then(|a| a.parse::<u64>().ok()).and_then(|a| self.bodies.get(&a).copied()),
            Value::Object(_) => Some(b),
            _ => None,
        }
    }

    fn body(&mut self, b: &'a Value, prefix: &str) {
        if let Some(b) = self.resolve(b) {
            self.members(b, prefix);
        }
    }

    /// One instance at `path`: a boundary when its definition is a module; its body walked below it.
    fn instance(&mut self, m: &'a Value, path: String) {
        let Some(b) = self.resolve(&m["body"]) else { return };
        // the body's name is its definition's
        let def = b["name"].as_str().unwrap_or("");
        if self.modules.contains(def) {
            self.out.instances.insert(path.clone(), def.to_string());
        }
        self.members(b, &format!("{path}."));
    }

    /// An instance array's elements `name[i]`, `i` counting up from the range's lower bound; an
    /// element of a multi-dimensional array is itself an array, indexed again.
    fn array(&mut self, a: &'a Value, path: &str) {
        let lower = a["range"].as_str().and_then(range_lower).unwrap_or(0);
        let elems = a["members"].as_array().into_iter().flatten().filter(|e| e["kind"] == "Instance" || e["kind"] == "InstanceArray");
        for (k, e) in elems.enumerate() {
            let p = format!("{path}[{}]", lower + k as i64);
            if e["kind"] == "InstanceArray" {
                self.array(e, &p);
            } else {
                self.instance(e, p);
            }
        }
    }

    fn members(&mut self, scope: &'a Value, prefix: &str) {
        for m in scope["members"].as_array().into_iter().flatten() {
            let name = m["name"].as_str().unwrap_or("");
            match m["kind"].as_str().unwrap_or("") {
                "Instance" => self.instance(m, format!("{prefix}{name}")),
                "InstanceArray" => self.array(m, &format!("{prefix}{name}")),
                "GenerateBlock" if m["isUninstantiated"] == true => {}
                "GenerateBlock" => self.members(m, &format!("{prefix}{name}.")),
                "GenerateBlockArray" => {
                    // each element is named by its genvar's value: `g[0]`. slang gives each element
                    // the loop's value as an implicit parameter, its FIRST member; the array has a
                    // `Genvar` member only when the loop declares it (`for (genvar i = …)`).
                    let elems = m["members"].as_array().into_iter().flatten().filter(|x| x["kind"] == "GenerateBlock" && x["isUninstantiated"] != true);
                    for e in elems {
                        let first = e["members"].as_array().and_then(|v| v.first());
                        let idx = first.filter(|x| x["kind"] == "Parameter").and_then(|x| x["value"].as_str());
                        if let Some(i) = idx {
                            self.members(e, &format!("{prefix}{name}[{i}]."));
                        }
                    }
                }
                _ => {}
            }
        }
    }
}

/// `[l:r]`'s lower bound.
fn range_lower(r: &str) -> Option<i64> {
    let (l, rt) = r.strip_prefix('[')?.strip_suffix(']')?.split_once(':')?;
    Some(l.trim().parse::<i64>().ok()?.min(rt.trim().parse().ok()?))
}

/// `name` with each module-instance boundary joined as `flatten` joins it: the `.` right after an
/// instance's path becomes the separator, [`KEPT_SEPARATOR`] when its definition is kept. Any
/// other `.` (a generate block, a named block, an escaped name's own) stays.
pub fn join_boundaries(name: &str, b: &Boundaries, sep: &str, kept: &BTreeSet<&str>) -> String {
    let mut out = String::with_capacity(name.len());
    let mut from = 0;
    for (pos, _) in name.match_indices('.') {
        let Some(def) = b.instances.get(&name[..pos]) else { continue };
        out.push_str(&name[from..pos]);
        out.push_str(if kept.contains(def.as_str()) { KEPT_SEPARATOR } else { sep });
        from = pos + 1;
    }
    out.push_str(&name[from..]);
    out
}

/// Every design name in the graph joined as [`join_boundaries`] does.
pub fn flatten_names(g: &mut Graph, b: &Boundaries, naming: &HierNaming) {
    let sep = naming.separator.as_deref().unwrap_or(".");
    let kept: BTreeSet<&str> = naming.keep_modules.iter().map(String::as_str).collect();
    for id in g.instance_list() {
        if let Kind::Name(nm) = &mut g.inst_mut(id).kind {
            nm.name = join_boundaries(&nm.name, b, sep, &kept);
        }
    }
}

/// The kept definitions no instance of the design has (ORFS stops: "no module … in the design").
#[must_use]
pub fn unknown_keep_modules<'n>(b: &Boundaries, naming: &'n HierNaming) -> Vec<&'n str> {
    let defs: BTreeSet<&str> = b.instances.values().map(String::as_str).collect();
    naming.keep_modules.iter().map(String::as_str).filter(|m| !defs.contains(m)).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bounds(v: &[(&str, &str)]) -> Boundaries {
        Boundaries { instances: v.iter().map(|(p, d)| (p.to_string(), d.to_string())).collect() }
    }

    /// Yosys `flatten` (concat_name, modules leaves first): an instance's public object `x` becomes
    /// `<cell><sep>x`, one boundary at a time, so every module-instance boundary takes the
    /// separator; a generate block is part of the object's own name within one module and keeps
    /// its `.` (Yosys 0.68: `u_m0/g[0].u_l/t`).
    #[test]
    fn only_module_instance_boundaries_take_the_separator() {
        let b = bounds(&[("u_m0", "mid"), ("u_m0.g[0].u_l", "leaf"), ("u_m0.genblk2.u_un", "leaf"), ("u_arr[1]", "leaf")]);
        let none = BTreeSet::new();
        assert_eq!(join_boundaries("u_m0.g[0].u_l.t", &b, "/", &none), "u_m0/g[0].u_l/t");
        assert_eq!(join_boundaries("u_m0.genblk2.u_un.t", &b, "/", &none), "u_m0/genblk2.u_un/t");
        assert_eq!(join_boundaries("u_arr[1].y", &b, "/", &none), "u_arr[1]/y");
        assert_eq!(join_boundaries("u_m0.m", &b, "/", &none), "u_m0/m");
        // a top-level name, and a generate block at the top, have no boundary
        assert_eq!(join_boundaries("a", &b, "/", &none), "a");
        assert_eq!(join_boundaries("g[0].x", &b, "/", &none), "g[0].x");
        // the default separator is elaboration's own: nothing changes
        assert_eq!(join_boundaries("u_m0.g[0].u_l.t", &b, ".", &none), "u_m0.g[0].u_l.t");
    }

    /// The reference chain keeps a module (ORFS SYNTH_KEEP_MODULES -> keep_hierarchy) and its
    /// netlist reader then names the kept module's contents `<path>/<local>`; boundaries flattened
    /// inside synthesis keep SYNTH_HIER_SEPARATOR (default `.`): `a.b.backend/_000085_`.
    #[test]
    fn a_kept_module_boundary_takes_the_readers_divider() {
        let b = bounds(&[("u_m0", "mid"), ("u_m0.g[0].u_l", "leaf")]);
        let kept: BTreeSet<&str> = ["leaf"].into_iter().collect();
        assert_eq!(join_boundaries("u_m0.g[0].u_l.t", &b, ".", &kept), "u_m0.g[0].u_l/t");
        let kept: BTreeSet<&str> = ["mid"].into_iter().collect();
        assert_eq!(join_boundaries("u_m0.g[0].u_l.t", &b, ".", &kept), "u_m0/g[0].u_l.t");
    }

    /// A `.` inside an escaped instance name is not a boundary: only the full path is.
    #[test]
    fn an_escaped_name_is_matched_whole() {
        let b = bounds(&[("a.b", "leaf")]);
        assert_eq!(join_boundaries("a.b.t", &b, "/", &BTreeSet::new()), "a.b/t");
    }

    /// Instance paths as the frontend names them (sv-elab build_hiername): instance, `[i]` per
    /// instance-array dimension counting from the lower bound, generate array `g[<genvar>]`, a
    /// generate block by its name (the element value is the block's first member, the loop's
    /// implicit parameter, with or without a `Genvar` member); a body printed once is referred to
    /// by address; an interface instance is not a module boundary.
    #[test]
    fn boundaries_are_named_as_the_netlist_names_them() {
        // `h`: the genvar declared outside the loop, so no `Genvar` member
        let ast: Value = serde_json::from_str(r#"{ "design": { "kind": "Root", "members": [
            { "kind": "Instance", "name": "top", "body": { "kind": "InstanceBody", "name": "top", "addr": 1, "members": [
                { "kind": "Instance", "name": "u_m0", "body": { "kind": "InstanceBody", "name": "mid", "addr": 2, "members": [
                    { "kind": "GenerateBlockArray", "name": "g", "members": [
                        { "kind": "Genvar", "name": "i" },
                        { "kind": "GenerateBlock", "name": "", "isUninstantiated": false, "members": [
                            { "kind": "Parameter", "name": "i", "value": "3" },
                            { "kind": "Instance", "name": "u_l", "body": { "kind": "InstanceBody", "name": "leaf", "addr": 7, "members": [] } } ] },
                        { "kind": "GenerateBlock", "name": "", "isUninstantiated": true, "members": [] } ] },
                    { "kind": "GenerateBlock", "name": "genblk2", "isUninstantiated": false, "members": [
                        { "kind": "Instance", "name": "u_un", "body": "7 leaf" } ] },
                    { "kind": "GenerateBlockArray", "name": "h", "members": [
                        { "kind": "GenerateBlock", "name": "", "isUninstantiated": false, "members": [
                            { "kind": "Parameter", "name": "k", "value": "-1" },
                            { "kind": "Instance", "name": "u_h", "body": "7 leaf" } ] } ] } ] } },
                { "kind": "Instance", "name": "u_m1", "body": "2 mid" },
                { "kind": "InstanceArray", "name": "u_arr", "range": "[2:1]", "members": [
                    { "kind": "Instance", "name": "", "body": "7 leaf" },
                    { "kind": "Instance", "name": "", "body": "7 leaf" } ] },
                { "kind": "Instance", "name": "bus", "body": { "kind": "InstanceBody", "name": "ifc", "addr": 9, "members": [] } }
            ] } }
        ] }, "definitions": [
            { "kind": "Definition", "name": "leaf", "definitionKind": "Module" },
            { "kind": "Definition", "name": "mid", "definitionKind": "Module" },
            { "kind": "Definition", "name": "top", "definitionKind": "Module" },
            { "kind": "Definition", "name": "ifc", "definitionKind": "Interface" }
        ] }"#).expect("fixture is JSON");
        let got = boundaries(&ast);
        let want = bounds(&[
            ("u_m0", "mid"),
            ("u_m0.g[3].u_l", "leaf"),
            ("u_m0.genblk2.u_un", "leaf"),
            ("u_m0.h[-1].u_h", "leaf"),
            ("u_m1", "mid"),
            ("u_m1.g[3].u_l", "leaf"),
            ("u_m1.genblk2.u_un", "leaf"),
            ("u_m1.h[-1].u_h", "leaf"),
            ("u_arr[1]", "leaf"),
            ("u_arr[2]", "leaf"),
        ]);
        assert_eq!(got, want);
    }

    /// ORFS stops when a SYNTH_KEEP_MODULES name matches no module of the design.
    #[test]
    fn a_kept_module_the_design_lacks_is_reported() {
        let b = bounds(&[("u", "leaf")]);
        let n = HierNaming { separator: None, keep_modules: vec!["leaf".into(), "nope".into()] };
        assert_eq!(unknown_keep_modules(&b, &n), ["nope"]);
        assert!(!n.is_default());
        assert!(HierNaming { separator: Some(".".into()), keep_modules: vec![] }.is_default());
    }
}
