// SPDX-License-Identifier: Apache-2.0
//! Each vector's range as DECLARED, by the name the elaborated netlist gives it.
//!
//! Elaboration numbers every vector's bits from 0 (`logic [11:8] r` becomes `r[0]`..`r[3]`, ports
//! included, as the reference's `synthesize` does), so a name written against the RTL (`r[8]`, a
//! constraint file's) no longer names the same bit. This reads the declared ranges from the same
//! frontend's elaborated design (slang's AST, `--ast-json`'s form), so a consumer can translate.
//!
//! Names are the netlist's: the instance path below the top joined by `.`, then the vector's
//! name (`u_sub.t`, a generate-array element as `g[0].u_in.t`); a top-level port or variable by
//! its name alone. Only a vector with ONE packed dimension of constant bounds is listed; any
//! other type (several dimensions, unpacked, a struct, a typedef name) is left out, as is what
//! sits in an unnamed generate block or an instance array, and each is counted in `skipped`.

use std::collections::{BTreeMap, HashMap};

use serde_json::Value;

/// The declared ranges of a design, elaborated by slang from `args` (the words `sv-elaborate`
/// takes). A module the sources do not define (a library cell) is not elaborated, so it is not
/// an error here. Err: slang rejected the arguments or reported an error (its report).
pub fn sv_ranges(args: &[String]) -> Result<Ranges, String> {
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
    Ok(declared_ranges(&ast))
}

/// What [`declared_ranges`] found.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct Ranges {
    /// `name -> (left, right)` of `[left:right]`.
    pub ranges: BTreeMap<String, (i64, i64)>,
    /// What was not listed, and why (`<scope>: <reason>`).
    pub skipped: Vec<String>,
}

/// `[left:right]` of a type written as slang prints it (`logic[11:8]`, `logic signed[3:0]`,
/// `reg[0:3]`): one packed dimension with integer bounds, nothing after it.
pub fn one_dimension(ty: &str) -> Option<(i64, i64)> {
    let (_, dims) = ty.split_once('[')?;
    let inner = dims.strip_suffix(']')?;
    if inner.contains(['[', ']', '$']) {
        return None;
    }
    let (l, r) = inner.split_once(':')?;
    Some((l.trim().parse().ok()?, r.trim().parse().ok()?))
}

/// The ranges in an elaborated design (`{"design": …, "definitions": …}`).
pub fn declared_ranges(ast: &Value) -> Ranges {
    // a body slang already printed is printed again as `"<addr> <name>"`
    let mut bodies: HashMap<u64, &Value> = HashMap::new();
    collect_bodies(&ast["design"], &mut bodies);
    let mut out = Ranges::default();
    for m in ast["design"]["members"].as_array().into_iter().flatten() {
        if m["kind"] == "Instance" {
            body(&m["body"], "", &bodies, &mut out);
        }
    }
    out.skipped.sort();
    out.skipped.dedup();
    out
}

/// Every instance body slang printed in place, by its address.
pub(crate) fn collect_bodies<'a>(v: &'a Value, bodies: &mut HashMap<u64, &'a Value>) {
    match v {
        Value::Object(o) => {
            if o.get("kind").and_then(Value::as_str) == Some("InstanceBody") {
                if let Some(a) = o.get("addr").and_then(Value::as_u64) {
                    bodies.insert(a, v);
                }
            }
            o.values().for_each(|x| collect_bodies(x, bodies));
        }
        Value::Array(a) => a.iter().for_each(|x| collect_bodies(x, bodies)),
        _ => {}
    }
}

fn body(b: &Value, prefix: &str, bodies: &HashMap<u64, &Value>, out: &mut Ranges) {
    let b = match b {
        Value::String(r) => match r.split_whitespace().next().and_then(|a| a.parse::<u64>().ok()).and_then(|a| bodies.get(&a)) {
            Some(b) => *b,
            None => {
                out.skipped.push(format!("{prefix}: instance body not found"));
                return;
            }
        },
        b => b,
    };
    members(b, prefix, bodies, out);
}

fn members(scope: &Value, prefix: &str, bodies: &HashMap<u64, &Value>, out: &mut Ranges) {
    for m in scope["members"].as_array().into_iter().flatten() {
        let name = m["name"].as_str().unwrap_or("");
        match m["kind"].as_str().unwrap_or("") {
            "Port" | "Variable" | "Net" => {
                let ty = m["type"].as_str().unwrap_or("");
                if ty.contains('[') {
                    match one_dimension(ty) {
                        Some(r) => {
                            out.ranges.insert(format!("{prefix}{name}"), r);
                        }
                        None => out.skipped.push(format!("{prefix}{name}: type {ty}")),
                    }
                }
            }
            "Instance" => body(&m["body"], &format!("{prefix}{name}."), bodies, out),
            "InstanceArray" => out.skipped.push(format!("{prefix}{name}: instance array")),
            "GenerateBlock" if m["isUninstantiated"] == true => {}
            "GenerateBlock" if name.is_empty() => out.skipped.push(format!("{prefix}(unnamed generate block)")),
            "GenerateBlock" => members(m, &format!("{prefix}{name}."), bodies, out),
            "GenerateBlockArray" => {
                // each element is named by its genvar's value: `g[0]`
                let genvar = m["members"].as_array().into_iter().flatten().find(|x| x["kind"] == "Genvar").and_then(|x| x["name"].as_str());
                for e in m["members"].as_array().into_iter().flatten().filter(|x| x["kind"] == "GenerateBlock" && x["isUninstantiated"] != true) {
                    let idx = e["members"]
                        .as_array()
                        .into_iter()
                        .flatten()
                        .find(|x| x["kind"] == "Parameter" && x["name"].as_str() == genvar)
                        .and_then(|x| x["value"].as_str());
                    match idx {
                        Some(i) => members(e, &format!("{prefix}{name}[{i}]."), bodies, out),
                        None => out.skipped.push(format!("{prefix}{name}: generate element with no genvar value")),
                    }
                }
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// slang's type text: one packed dimension with integer bounds, either direction, signed or
    /// not. Several dimensions, an unpacked one (`$`) or a named type are not one vector's range.
    #[test]
    fn a_range_is_one_packed_dimension() {
        assert_eq!(one_dimension("logic[11:8]"), Some((11, 8)));
        assert_eq!(one_dimension("logic signed[0:3]"), Some((0, 3)));
        assert_eq!(one_dimension("reg[3:0]"), Some((3, 0)));
        for no in ["logic", "logic[3:0][7:0]", "logic[7:0]$[0:3]", "word_t", "logic[W-1:0]"] {
            assert_eq!(one_dimension(no), None, "{no}");
        }
    }

    /// The names are the netlist's: top-level by name, an instance's by its path (`u_sub.t`),
    /// a body slang printed once and then referred to by address is read through the reference,
    /// a generate-array element is `g[<genvar value>]`, and a scalar is not listed.
    #[test]
    fn ranges_are_named_as_the_netlist_names_them() {
        let ast = serde_json::json!({ "design": { "kind": "Root", "members": [
            { "kind": "CompilationUnit", "name": "" },
            { "kind": "Instance", "name": "top", "body": { "kind": "InstanceBody", "addr": 1, "members": [
                { "kind": "Port", "name": "q", "type": "logic[11:8]", "direction": "Out" },
                { "kind": "Net", "name": "q", "type": "logic[11:8]" },
                { "kind": "Port", "name": "x", "type": "logic", "direction": "In" },
                { "kind": "Variable", "name": "r", "type": "logic[8:11]" },
                { "kind": "Variable", "name": "m", "type": "logic[3:0][7:0]" },
                { "kind": "Instance", "name": "u_sub", "body": { "kind": "InstanceBody", "addr": 7, "members": [
                    { "kind": "Variable", "name": "t", "type": "logic[5:4]" } ] } },
                { "kind": "GenerateBlockArray", "name": "g", "members": [
                    { "kind": "Genvar", "name": "i" },
                    { "kind": "GenerateBlock", "name": "", "isUninstantiated": false, "members": [
                        { "kind": "Parameter", "name": "i", "value": "2" },
                        { "kind": "Instance", "name": "u_in", "body": "7 sub" } ] } ] },
                { "kind": "GenerateBlock", "name": "", "isUninstantiated": false, "members": [] }
            ] } }
        ] }, "definitions": [] });
        let r = declared_ranges(&ast);
        let want: BTreeMap<String, (i64, i64)> =
            [("q", (11, 8)), ("r", (8, 11)), ("u_sub.t", (5, 4)), ("g[2].u_in.t", (5, 4))].iter().map(|(n, v)| (n.to_string(), *v)).collect();
        assert_eq!(r.ranges, want);
        assert_eq!(r.skipped, ["(unnamed generate block)", "m: type logic[3:0][7:0]"]);
    }
}
