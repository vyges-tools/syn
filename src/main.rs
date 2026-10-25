// SPDX-License-Identifier: Apache-2.0
//! `vyges-syn` — integrated logic synthesis from RTL to a mapped netlist, on the shared AIG core.
//!
//! ## Exit codes
//!
//! ⛔ **"found something" and "could not run" never share a code.** A CI gate that cannot tell a
//! broken tool from a bad design will eventually read a missing engine as a clean run.
//!
//! | code | meaning |
//! | --- | --- |
//! | 0 | ok |
//! | 1 | a finding (the check ran and failed) |
//! | 2 | usage, or input that could not be read |
//! | 3 | the command is NOT IMPLEMENTED in this build |

use std::process::ExitCode;

const USAGE: &str = "\
vyges physical syn — integrated logic synthesis from RTL to a mapped netlist, on the shared AIG core

USAGE:
  vyges physical syn run  <job>  RTL to a technology-mapped netlist
  vyges physical syn ir-normalize <in.ir> -o OUT.ir
                                  read a netlist in the IR text form, normalize it (topological
                                  order, dead logic dropped, loops broken) and write it back
  vyges physical syn sv-elaborate --raw -o OUT.ir <slang arguments...>
                                  elaborate SystemVerilog and write the netlist as the frontend
                                  built it (before any pass), in the IR text form
  vyges physical syn --describe
  vyges physical syn --help
  vyges physical syn --version

OPTIONS:
  -o FILE               write the report (or the output database) to FILE
  --json                machine-readable output instead of the text report
  -q, --quiet           suppress non-essential output
  -v, --verbose         extra detail on stderr
  --describe            print a machine-readable JSON description of the command
  --bug-report          file a bug (central: vyges/community)
  --feature-request     request a feature (central)

EXIT STATUS:
  0  ok
  1  a finding — the check ran and failed
  2  usage or unreadable input
  3  refused — this build does not implement the command yet
";

/// The commands this engine will answer. Each is refused (exit 3) until its stage is built.
pub const COMMANDS: &[&str] = &["run", "ir-normalize", "sv-elaborate"];

const DESCRIBE: &str = r#"{
  "schema": "vyges-tool-descriptor/1.1",
  "name": "syn",
  "summary": "Integrated logic synthesis from RTL to a mapped netlist, on the shared AIG core.",
  "maturity": "discovered",
  "provenance_limitations": [
    "`ir-normalize` and `sv-elaborate --raw` are built; `run` and `sv-elaborate` without `--raw` refuse with exit 3."
  ],
  "invocation": { "args_template": ["run"], "emits_json": true },
  "inputs": { "type": "object", "properties": {} },
  "artifacts": [],
  "assertion": { "id": "syn-ok", "field": "status", "pass_when": { "equals": "ok" } },
  "consumes": []
}"#;

fn refuse(what: &str) -> ExitCode {
    vyges_events::emit(
        &vyges_events::Event::new("vyges-syn", vyges_events::Severity::Error, format!("{what} is not implemented in this build"))
            .with_code("SYN-REFUSED"),
    );
    ExitCode::from(3)
}

/// `ir-normalize IN -o OUT`: parse, normalize, dump.
fn ir_normalize(args: &[String]) -> ExitCode {
    let (mut input, mut out) = (None, None);
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "-o" if i + 1 < args.len() => {
                out = Some(args[i + 1].clone());
                i += 1;
            }
            a if input.is_none() && !a.starts_with('-') => input = Some(a.to_string()),
            a => {
                eprintln!("vyges-syn ir-normalize: unexpected argument `{a}`");
                return ExitCode::from(2);
            }
        }
        i += 1;
    }
    let (Some(input), Some(out)) = (input, out) else {
        eprintln!("vyges-syn ir-normalize: needs <in.ir> -o OUT.ir");
        return ExitCode::from(2);
    };
    let text = match std::fs::read_to_string(&input) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("vyges-syn: cannot read {input}: {e}");
            return ExitCode::from(2);
        }
    };
    let mut g = match vyges_syn::ir::parse::parse(&text, None) {
        Ok(g) => g,
        Err(e) => {
            eprintln!("vyges-syn: {input}: {e}");
            return ExitCode::from(2);
        }
    };
    g.normalize();
    if let Err(e) = std::fs::write(&out, g.dump()) {
        eprintln!("vyges-syn: cannot write {out}: {e}");
        return ExitCode::from(2);
    }
    ExitCode::SUCCESS
}

/// `sv-elaborate --raw -o OUT <slang arguments...>`: elaborate, dump the graph as built.
fn sv_elaborate(args: &[String]) -> ExitCode {
    let (mut raw, mut out, mut rest) = (false, None, Vec::new());
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--raw" if rest.is_empty() => raw = true,
            "-o" if rest.is_empty() && i + 1 < args.len() => {
                out = Some(args[i + 1].clone());
                i += 1;
            }
            "--" if rest.is_empty() => {}
            a => rest.push(a.to_string()),
        }
        i += 1;
    }
    let Some(out) = out else {
        eprintln!("vyges-syn sv-elaborate: needs -o OUT.ir");
        return ExitCode::from(2);
    };
    if !raw {
        // The passes after elaboration (import, constant folding) are not built yet.
        return refuse("sv-elaborate without --raw");
    }
    match vyges_syn::elab::frontend::elaborate(&rest, &[]) {
        Ok(g) => {
            if let Err(e) = std::fs::write(&out, g.dump()) {
                eprintln!("vyges-syn: cannot write {out}: {e}");
                return ExitCode::from(2);
            }
            ExitCode::SUCCESS
        }
        Err(vyges_syn::elab::frontend::Failed::Reported) => {
            println!("[ERROR SYN-0001] Elaboration failed.");
            ExitCode::from(1)
        }
        Err(vyges_syn::elab::frontend::Failed::Error(code, msg)) => {
            println!("[ERROR SYN-{code:04}] {msg}");
            ExitCode::from(1)
        }
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        None | Some("-h") | Some("--help") => {
            print!("{USAGE}");
            ExitCode::SUCCESS
        }
        Some("-V") | Some("--version") => {
            println!("vyges-syn {} ({})", env!("CARGO_PKG_VERSION"), env!("VYGES_GIT_SHA"));
            println!("Copyright 2026 Vyges. Apache-2.0.");
            ExitCode::SUCCESS
        }
        Some("--describe") => {
            println!("{DESCRIBE}");
            ExitCode::SUCCESS
        }
        Some("ir-normalize") => ir_normalize(&args[1..]),
        Some("sv-elaborate") => sv_elaborate(&args[1..]),
        Some(cmd) if COMMANDS.contains(&cmd) => refuse(cmd),
        Some(other) => {
            eprintln!("vyges-syn: unknown command `{other}`\n\n{USAGE}");
            ExitCode::from(2)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_descriptor_is_valid_json_with_a_legal_maturity() {
        let d: serde_json::Value = serde_json::from_str(DESCRIBE).expect("descriptor is valid JSON");
        assert_eq!(d["schema"], "vyges-tool-descriptor/1.1");
        assert_eq!(d["name"], "syn");
        // Anything else is read as `discovered` and every verdict becomes `unknown`.
        let m = d["maturity"].as_str().unwrap();
        assert!(["discovered", "structured", "workflow-validated"].contains(&m), "{m}");
    }

    #[test]
    fn the_usage_spells_the_engine_under_its_group() {
        // The dispatcher REFUSES a wrong group prefix, so the help must spell the right one.
        for c in COMMANDS {
            assert!(USAGE.contains(&format!("vyges physical syn {c}")), "{c}");
        }
    }
}
