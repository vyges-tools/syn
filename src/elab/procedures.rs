// SPDX-License-Identifier: Apache-2.0
//! Which variables a latch may be inferred for: those assigned in an `always_latch` block, or in
//! an `always` block whose event control has no edge (`always @*`, `always @(a or b)`).
//!
//! The frontend (built with mux lowering) emits every incompletely assigned variable of a
//! combinational-like process as the same feedback mux, whatever the process was, so the kind of
//! process is read here from slang's elaborated design (its JSON form, as `hierarchy` reads it).
//! The rule is the Yosys reference flow's (its slang frontend's `handle_comb_like_process`,
//! non-mux-lowering build): a variable some path leaves unassigned becomes a latch in any such
//! process except `always_comb`. An `always_comb` that does so, and a continuous assignment that
//! reads its own result, stay combinational loops, which `check_combinational_loops` rejects as
//! the reference `syn` does.
//!
//! A variable is named as the netlist names it: its scope's path below the top, joined by `.`.
//! A variable declared inside a procedural block (a block-local) is not listed.

use std::collections::{BTreeSet, HashMap};

use serde_json::Value;

/// The variables, by name, a latch may be inferred for, in the design the slang arguments name.
/// Err: slang rejected the arguments or reported an error (its report).
pub fn latch_variables(args: &[String]) -> Result<BTreeSet<String>, String> {
    let mut words = super::frontend::split_args(args);
    if !words.iter().any(|w| w == "--ignore-unknown-modules") {
        words.push("--ignore-unknown-modules".to_string());
    }
    let mut c = vyges_slang_lib::compile(&words).map_err(|e| e.to_string())?;
    if c.status() != vyges_slang_lib::Status::Ok || c.error_count() > 0 {
        return Err(c.report().trim().to_string());
    }
    let json = c.ast_json(false).ok_or_else(|| "slang produced no elaborated design".to_string())?;
    drop(c);
    walk_json(json)
}

/// [`latch_variables_in`] of the design JSON text. A large design's JSON nests deeper than serde's
/// default limit (CoralNPU: past 128 levels, an expression chain is a left-deep tree): it is
/// parsed, walked and dropped without that limit, on a thread whose stack is sized for the depth.
fn walk_json(json: String) -> Result<BTreeSet<String>, String> {
    let walk = std::thread::Builder::new().stack_size(PARSE_STACK).spawn(move || -> Result<BTreeSet<String>, String> {
        let mut de = serde_json::Deserializer::from_str(&json);
        de.disable_recursion_limit();
        let ast: Value = match de.into_iter::<Value>().next() {
            Some(Ok(v)) => v,
            Some(Err(e)) => return Err(format!("slang's design JSON: {e}")),
            None => return Err("slang's design JSON is empty".to_string()),
        };
        Ok(latch_variables_in(&ast))
    });
    let walk = walk.map_err(|e| format!("cannot start the design JSON walk: {e}"))?;
    walk.join().unwrap_or_else(|_| Err("the design JSON walk panicked".to_string()))
}

/// The stack of the thread that parses and walks the design JSON (virtual memory: only the depth
/// actually reached is touched).
const PARSE_STACK: usize = 1 << 30;

/// [`latch_variables`] of an elaborated design (`{"design": …}`).
pub fn latch_variables_in(ast: &Value) -> BTreeSet<String> {
    let mut bodies: HashMap<u64, &Value> = HashMap::new();
    super::ranges::collect_bodies(&ast["design"], &mut bodies);
    let mut w = Walk { bodies, out: BTreeSet::new() };
    for m in ast["design"]["members"].as_array().into_iter().flatten() {
        if m["kind"] == "Instance" {
            w.body(&m["body"], "");
        }
    }
    w.out
}

/// A process whose incompletely assigned variables become latches: `always_latch`, or `always`
/// with no edge in its event control.
fn latch_like(p: &Value) -> bool {
    match p["procedureKind"].as_str() {
        Some("AlwaysLatch") => true,
        Some("Always") => p["body"]["kind"] == "Timed" && !has_edge(&p["body"]["timing"]),
        _ => false,
    }
}

fn has_edge(timing: &Value) -> bool {
    match timing {
        Value::Object(o) => {
            matches!(o.get("edge").and_then(Value::as_str), Some("PosEdge" | "NegEdge" | "BothEdges")) || o.values().any(has_edge)
        }
        Value::Array(a) => a.iter().any(has_edge),
        _ => false,
    }
}

/// The address in a `"<addr> <name>"` symbol reference.
fn symbol_addr(v: &Value) -> Option<u64> {
    v.as_str()?.split_whitespace().next()?.parse().ok()
}

/// The variables an assignment's left side writes: through selects and member accesses to the
/// variable, and into each part of a concatenation; an index is not written.
fn written(left: &Value, out: &mut Vec<u64>) {
    match left["kind"].as_str() {
        Some("NamedValue") => out.extend(symbol_addr(&left["symbol"])),
        Some("ElementSelect" | "RangeSelect" | "MemberAccess") => written(&left["value"], out),
        Some("Concatenation") => left["operands"].as_array().into_iter().flatten().for_each(|o| written(o, out)),
        Some("SimpleAssignmentPattern" | "StructuredAssignmentPattern") => {
            left["elements"].as_array().into_iter().flatten().for_each(|o| written(o, out))
        }
        _ => {}
    }
}

/// Every variable an assignment anywhere in `stmt` writes.
fn assigned(stmt: &Value, out: &mut Vec<u64>) {
    match stmt {
        Value::Object(o) => {
            if o.get("kind").and_then(Value::as_str) == Some("Assignment") {
                written(&stmt["left"], out);
            }
            o.values().for_each(|v| assigned(v, out));
        }
        Value::Array(a) => a.iter().for_each(|v| assigned(v, out)),
        _ => {}
    }
}

struct Walk<'a> {
    bodies: HashMap<u64, &'a Value>,
    out: BTreeSet<String>,
}

impl<'a> Walk<'a> {
    fn body(&mut self, b: &'a Value, prefix: &str) {
        let b = match b {
            Value::String(_) => symbol_addr(b).and_then(|a| self.bodies.get(&a).copied()),
            Value::Object(_) => Some(b),
            _ => None,
        };
        if let Some(b) = b {
            // an instance sees none of its parent's variables
            self.members(b, prefix, &mut Vec::new());
        }
    }

    fn array(&mut self, a: &'a Value, path: &str) {
        let lower = a["range"].as_str().and_then(super::hierarchy::range_lower).unwrap_or(0);
        let elems = a["members"].as_array().into_iter().flatten().filter(|e| e["kind"] == "Instance" || e["kind"] == "InstanceArray");
        for (k, e) in elems.enumerate() {
            let p = format!("{path}[{}]", lower + k as i64);
            if e["kind"] == "InstanceArray" {
                self.array(e, &p);
            } else {
                self.body(&e["body"], &format!("{p}."));
            }
        }
    }

    /// One scope at `prefix`: its variables join `scopes` (innermost last) while its processes
    /// and nested scopes are walked.
    fn members(&mut self, scope: &'a Value, prefix: &str, scopes: &mut Vec<HashMap<u64, String>>) {
        let members = scope["members"].as_array();
        let mut here = HashMap::new();
        for m in members.into_iter().flatten() {
            if matches!(m["kind"].as_str(), Some("Variable" | "Net")) {
                if let (Some(a), Some(n)) = (m["addr"].as_u64(), m["name"].as_str()) {
                    here.insert(a, format!("{prefix}{n}"));
                }
            }
        }
        scopes.push(here);
        for m in members.into_iter().flatten() {
            let name = m["name"].as_str().unwrap_or("");
            match m["kind"].as_str().unwrap_or("") {
                "ProceduralBlock" if latch_like(m) => {
                    let mut addrs = Vec::new();
                    assigned(&m["body"], &mut addrs);
                    for a in addrs {
                        if let Some(n) = scopes.iter().rev().find_map(|s| s.get(&a)) {
                            self.out.insert(n.clone());
                        }
                    }
                }
                "Instance" => self.body(&m["body"], &format!("{prefix}{name}.")),
                "InstanceArray" => self.array(m, &format!("{prefix}{name}")),
                "GenerateBlock" if m["isUninstantiated"] == true => {}
                "GenerateBlock" => self.members(m, &format!("{prefix}{name}."), scopes),
                "GenerateBlockArray" => {
                    // each element is named by its genvar's value, its first member (`hierarchy`)
                    let elems = m["members"].as_array().into_iter().flatten().filter(|x| x["kind"] == "GenerateBlock" && x["isUninstantiated"] != true);
                    for e in elems {
                        let first = e["members"].as_array().and_then(|v| v.first());
                        if let Some(i) = first.filter(|x| x["kind"] == "Parameter").and_then(|x| x["value"].as_str()) {
                            self.members(e, &format!("{prefix}{name}[{i}]."), scopes);
                        }
                    }
                }
                _ => {}
            }
        }
        scopes.pop();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn process(kind: &str, timing: Option<Value>, var: u64) -> Value {
        let assign = serde_json::json!({"kind": "ExpressionStatement", "expr": {"kind": "Assignment",
            "left": {"kind": "ElementSelect", "value": {"kind": "NamedValue", "symbol": format!("{var} q")},
                     "selector": {"kind": "NamedValue", "symbol": "9 i"}}}});
        let body = match timing {
            Some(t) => serde_json::json!({"kind": "Timed", "timing": t, "stmt": assign}),
            None => assign,
        };
        serde_json::json!({"kind": "ProceduralBlock", "name": "", "procedureKind": kind, "body": body})
    }

    fn design(procs: Vec<Value>) -> Value {
        let mut members = vec![
            serde_json::json!({"kind": "Variable", "name": "q", "addr": 1}),
            serde_json::json!({"kind": "Variable", "name": "i", "addr": 9}),
        ];
        members.extend(procs);
        serde_json::json!({"design": {"members": [{"kind": "Instance", "name": "top",
            "body": {"kind": "InstanceBody", "addr": 100, "name": "top", "members": members}}]}})
    }

    /// Yosys's slang frontend (`handle_comb_like_process`): a latch for `always_latch` and for an
    /// `always` with an implicit or edgeless event control; none for `always_comb` or an edge-
    /// triggered `always`. The variable written is named, not the index that selects into it.
    /// The design JSON of a large design nests past serde's default depth limit (128): CoralNPU
    /// failed there. A process body 20,000 blocks deep still names its variable.
    #[test]
    fn a_deeply_nested_design_is_walked() {
        let mut stmt = r#"{"kind": "ExpressionStatement", "expr": {"kind": "Assignment", "left": {"kind": "NamedValue", "symbol": "1 q"}}}"#.to_string();
        for _ in 0..20_000 {
            stmt = format!(r#"{{"kind": "Block", "body": {stmt}}}"#);
        }
        let json = format!(
            r#"{{"design": {{"members": [{{"kind": "Instance", "name": "top", "body": {{"kind": "InstanceBody", "addr": 100,
                "members": [{{"kind": "Variable", "name": "q", "addr": 1}},
                            {{"kind": "ProceduralBlock", "procedureKind": "AlwaysLatch", "body": {stmt}}}]}}}}]}}}}"#
        );
        let want: BTreeSet<String> = ["q".to_string()].into_iter().collect();
        assert_eq!(walk_json(json), Ok(want));
    }

    #[test]
    fn only_latch_like_processes_name_their_variables() {
        let implicit = serde_json::json!({"kind": "ImplicitEvent"});
        let edgeless = serde_json::json!({"kind": "SignalEvent", "edge": "None"});
        let posedge = serde_json::json!({"kind": "SignalEvent", "edge": "PosEdge"});
        let want: BTreeSet<String> = ["q".to_string()].into_iter().collect();
        assert_eq!(latch_variables_in(&design(vec![process("AlwaysLatch", None, 1)])), want);
        assert_eq!(latch_variables_in(&design(vec![process("Always", Some(implicit), 1)])), want);
        assert_eq!(latch_variables_in(&design(vec![process("Always", Some(edgeless), 1)])), want);
        assert!(latch_variables_in(&design(vec![process("AlwaysComb", None, 1)])).is_empty());
        assert!(latch_variables_in(&design(vec![process("Always", Some(posedge), 1)])).is_empty());
    }
}
