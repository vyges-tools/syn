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

use vyges_syn::events;

const USAGE: &str = "\
vyges physical syn — integrated logic synthesis from RTL to a mapped netlist, on the shared AIG core

USAGE:
  vyges physical syn run  <job>  RTL to a technology-mapped netlist
  vyges physical syn ir-normalize <in.ir> -o OUT.ir
                                  read a netlist in the IR text form, normalize it (topological
                                  order, dead logic dropped, loops broken) and write it back
  vyges physical syn sv-elaborate [--raw] [--liberty LIB]... -o OUT.ir <slang arguments...>
                                  elaborate SystemVerilog and write the netlist in the IR text
                                  form, cleaned up (library cells imported, constants folded);
                                  --raw: as the frontend built it, before any pass; --liberty:
                                  read a library, whose cells the design may instantiate
  vyges physical syn ir-pass [--liberty LIB]... <in.ir> -o OUT.ir PASS...
                                  read a netlist in the IR text form (its library cells imported),
                                  run the passes in order, write it back. PASS: normalize, opt,
                                  bitblast, bitblast-no-arith, liveness, abc-fraig, abc-dc2
                                  (the ABC round trips of synthesize), map-sequentials,
                                  map-combinationals, gate-fuse, stats (printed)
  vyges physical syn ir-pass [--liberty LIB]... -o OUT.ir PASS... --sv <slang arguments...>
                                  the same on the design as sv-elaborate leaves it, in memory
                                  (what the text form does not carry, register reset and clear
                                  values, kept)
  vyges physical syn synthesize [--liberty LIB]... [--lef LEF]... -o OUT.v <slang arguments...>
                                  elaborate SystemVerilog, synthesize it onto the libraries' cells
                                  and write the mapped netlist as structural Verilog; the LEFs (the
                                  technology first) give the cells' masters
  vyges physical syn --describe
  vyges physical syn --help
  vyges physical syn --version

OPTIONS:
  -o FILE               write the report (or the output database) to FILE
  --json                machine-readable output instead of the text report
  -q, --quiet           raise the causal trail's floor to error (VYGES_LOG)
  -v, --verbose         lower it to debug: each step of the command
                        (both go BEFORE the command: after it, -v is slang's)
  --describe            print a machine-readable JSON description of the command
  --bug-report          file a bug (central: vyges/community)
  --feature-request     request a feature (central)

EVENTS:
  The causal trail (vyges-events JSON lines) goes to stderr; netlists, reports and log lines go
  to stdout or -o. SYN-INPUT, SYN-REFUSED, SYN-STEP (debug) and SYN-DONE (every command: its
  status and exit code). An explicit VYGES_LOG wins over -q and -v.

EXIT STATUS:
  0  ok
  1  a finding — the check ran and failed
  2  usage or unreadable input
  3  refused — this build does not implement the command yet
";

/// The commands this engine will answer. Each is refused (exit 3) until its stage is built.
pub const COMMANDS: &[&str] = &["run", "ir-normalize", "sv-elaborate", "ir-pass", "synthesize"];

const DESCRIBE: &str = r#"{
  "schema": "vyges-tool-descriptor/1.1",
  "name": "syn",
  "summary": "Integrated logic synthesis from RTL to a mapped netlist, on the shared AIG core.",
  "maturity": "discovered",
  "provenance_limitations": [
    "`ir-normalize`, `sv-elaborate`, `ir-pass` and `synthesize` are built; `run` refuses with exit 3."
  ],
  "invocation": { "args_template": ["run"], "emits_json": true },
  "inputs": { "type": "object", "properties": {} },
  "artifacts": [],
  "assertion": { "id": "syn-ok", "field": "status", "pass_when": { "eq": "ok" } },
  "consumes": []
}"#;

fn refuse(what: &str) -> ExitCode {
    events::refused(&format!("{what} is not implemented in this build"));
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
            events::input(&format!("cannot read {input}: {e}"));
            return ExitCode::from(2);
        }
    };
    let mut g = match vyges_syn::ir::parse::parse(&text, None) {
        Ok(g) => g,
        Err(e) => {
            events::input(&format!("{input}: {e}"));
            return ExitCode::from(2);
        }
    };
    g.normalize();
    if let Err(e) = std::fs::write(&out, g.dump()) {
        events::input(&format!("cannot write {out}: {e}"));
        return ExitCode::from(2);
    }
    ExitCode::SUCCESS
}

/// `ir-pass [--liberty LIB]... IN -o OUT PASS...`: read as the reference's `syn::parse` reads (parse,
/// then the library cells imported), run each pass, dump. `--sv ARGS...` in place of IN: the graph
/// `sv_elaborate` leaves, never written out in between.
fn ir_pass(args: &[String]) -> ExitCode {
    let (mut input, mut out, mut passes) = (None, None, Vec::new());
    let mut sv: Option<Vec<String>> = None;
    let mut libs = vyges_syn::library::Libraries::default();
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--sv" => {
                sv = Some(args[i + 1..].to_vec());
                break;
            }
            "-o" if i + 1 < args.len() => {
                out = Some(args[i + 1].clone());
                i += 1;
            }
            "--liberty" if i + 1 < args.len() => {
                if let Err(e) = libs.read(&args[i + 1]) {
                    events::input(&format!("cannot read {e}"));
                    return ExitCode::from(2);
                }
                i += 1;
            }
            a if matches!(a, "normalize" | "opt" | "bitblast" | "bitblast-no-arith" | "liveness" | "abc-fraig" | "abc-dc2" | "map-sequentials" | "map-combinationals" | "gate-fuse" | "stats") => {
                passes.push(a.to_string())
            }
            a if input.is_none() && !a.starts_with('-') => input = Some(a.to_string()),
            a => {
                eprintln!("vyges-syn ir-pass: unexpected argument `{a}`");
                return ExitCode::from(2);
            }
        }
        i += 1;
    }
    let Some(out) = out else {
        eprintln!("vyges-syn ir-pass: needs -o OUT.ir");
        return ExitCode::from(2);
    };
    let mut g = match (input, sv) {
        (None, Some(sv)) => match vyges_syn::synthesis::sv_elaborate(&sv, &libs) {
            Ok(g) => g,
            Err(vyges_syn::elab::frontend::Failed::Reported) => {
                println!("[ERROR SYN-0001] Elaboration failed.");
                return ExitCode::from(1);
            }
            Err(vyges_syn::elab::frontend::Failed::Error(code, msg)) => {
                println!("[ERROR SYN-{code:04}] {msg}");
                return ExitCode::from(1);
            }
        },
        (Some(input), None) => {
            let text = match std::fs::read_to_string(&input) {
                Ok(t) => t,
                Err(e) => {
                    events::input(&format!("cannot read {input}: {e}"));
                    return ExitCode::from(2);
                }
            };
            let lookup = |name: &str| libs.find_cell(name);
            let mut g = match vyges_syn::ir::parse::parse(&text, Some(&lookup)) {
                Ok(g) => g,
                Err(e) => {
                    events::input(&format!("{input}: {e}"));
                    return ExitCode::from(2);
                }
            };
            g.check_consistency();
            if let Err(e) = vyges_syn::flow::import::import_targets(&mut g, &libs) {
                println!("[ERROR SYN-{:04}] {}", e.code, e.message);
                return ExitCode::from(1);
            }
            g
        }
        _ => {
            eprintln!("vyges-syn ir-pass: needs one of <in.ir> or --sv <slang arguments...>");
            return ExitCode::from(2);
        }
    };
    let mut abc: Option<vyges_abc_lib::Abc> = None;
    for pass in &passes {
        match pass.as_str() {
            p @ ("abc-fraig" | "abc-dc2") => {
                if abc.is_none() {
                    match vyges_abc_lib::Abc::start() {
                        Ok(a) => abc = Some(a),
                        Err(e) => {
                            events::input(&format!("ABC: {e}"));
                            return ExitCode::from(2);
                        }
                    }
                }
                let script = if p == "abc-fraig" { vyges_syn::synthesis::ABC_FRAIG } else { vyges_syn::synthesis::ABC_DC2 };
                if let Err(e) = vyges_syn::flow::abc::abc_roundtrip(&mut g, abc.as_mut().unwrap(), script, -1) {
                    println!("{e}");
                    return ExitCode::from(1);
                }
            }
            "normalize" => g.normalize(),
            "opt" => vyges_syn::flow::constant_fold::constant_fold(&mut g),
            "bitblast" => vyges_syn::flow::bitblast::bitblast(&mut g, true),
            "map-sequentials" => {
                if let Err(e) = vyges_syn::flow::sequential_mapper::map_sequentials(&mut g, &libs) {
                    println!("[ERROR SYN-{:04}] {}", e.code, e.message);
                    return ExitCode::from(1);
                }
            }
            "map-combinationals" => {
                if let Err(e) = vyges_syn::flow::combinational_mapper::map_combinationals(&mut g, &libs) {
                    println!("[ERROR SYN-{:04}] {}", e.code, e.message);
                    return ExitCode::from(1);
                }
            }
            "stats" => print!("{}", g.stats()),
            "gate-fuse" => vyges_syn::flow::opt_gatefusion::gate_fusion_opt(&mut g, &libs),
            "liveness" => {
                let (regs, combs) = vyges_syn::flow::liveness::liveness_opt(&mut g, false);
                println!("[INFO SYN-0056] liveness: replaced {regs} register bits, {combs} combinational bits");
            }
            _ => vyges_syn::flow::bitblast::bitblast(&mut g, false),
        }
    }
    if let Err(e) = std::fs::write(&out, g.dump()) {
        events::input(&format!("cannot write {out}: {e}"));
        return ExitCode::from(2);
    }
    ExitCode::SUCCESS
}

/// `synthesize [--liberty LIB]... [--lef LEF]... -o OUT.v <slang arguments...>`: elaborate,
/// synthesize, export into a database holding the LEFs, write it as Verilog.
fn synthesize(args: &[String]) -> ExitCode {
    let (mut out, mut lefs, mut rest) = (None, Vec::new(), Vec::new());
    let mut libs = vyges_syn::library::Libraries::default();
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--liberty" if rest.is_empty() && i + 1 < args.len() => {
                if let Err(e) = libs.read(&args[i + 1]) {
                    events::input(&format!("cannot read {e}"));
                    return ExitCode::from(2);
                }
                i += 1;
            }
            "--lef" if rest.is_empty() && i + 1 < args.len() => {
                lefs.push(args[i + 1].clone());
                i += 1;
            }
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
        eprintln!("vyges-syn synthesize: needs -o OUT.v");
        return ExitCode::from(2);
    };
    let mut db = vyges_opendb::Db::new();
    for lef in &lefs {
        if let Err(e) = db.read_lef(lef) {
            events::input(&format!("cannot read {lef}: {e}"));
            return ExitCode::from(2);
        }
    }
    let mut g = match vyges_syn::synthesis::sv_elaborate(&rest, &libs) {
        Ok(g) => g,
        Err(vyges_syn::elab::frontend::Failed::Reported) => {
            println!("[ERROR SYN-0001] Elaboration failed.");
            return ExitCode::from(1);
        }
        Err(vyges_syn::elab::frontend::Failed::Error(code, msg)) => {
            println!("[ERROR SYN-{code:04}] {msg}");
            return ExitCode::from(1);
        }
    };
    events::step("synthesize", &format!("elaborated {}", if g.name.is_empty() { "the design" } else { &g.name }));
    let mut abc = match vyges_abc_lib::Abc::start() {
        Ok(a) => a,
        Err(e) => {
            events::input(&format!("ABC: {e}"));
            return ExitCode::from(2);
        }
    };
    if let Err(e) = vyges_syn::synthesis::synthesize(&mut g, &libs, &mut abc) {
        println!("{e}");
        return ExitCode::from(1);
    }
    events::step("synthesize", "mapped onto the libraries' cells; exporting");
    if let Err(e) = vyges_syn::flow::export::export_to_odb(&mut g, &mut db) {
        println!("{e}");
        return ExitCode::from(1);
    }
    let verilog = match vyges_opendb::verilog::write_verilog(&db, false, &[]) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("vyges-syn: {e}");
            return ExitCode::from(1);
        }
    };
    if let Err(e) = std::fs::write(&out, verilog) {
        events::input(&format!("cannot write {out}: {e}"));
        return ExitCode::from(2);
    }
    events::step("synthesize", &format!("wrote {out}"));
    ExitCode::SUCCESS
}

/// `sv-elaborate [--raw] [--liberty LIB]... -o OUT <slang arguments...>`: elaborate (and clean up), dump the graph.
fn sv_elaborate(args: &[String]) -> ExitCode {
    let (mut raw, mut out, mut rest) = (false, None, Vec::new());
    let mut libs = vyges_syn::library::Libraries::default();
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--raw" if rest.is_empty() => raw = true,
            "--liberty" if rest.is_empty() && i + 1 < args.len() => {
                if let Err(e) = libs.read(&args[i + 1]) {
                    events::input(&format!("cannot read {e}"));
                    return ExitCode::from(2);
                }
                i += 1;
            }
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
    let result = if raw {
        vyges_syn::elab::frontend::elaborate(&rest, &libs.blackboxes())
    } else {
        vyges_syn::synthesis::sv_elaborate(&rest, &libs)
    };
    match result {
        Ok(g) => {
            if let Err(e) = std::fs::write(&out, g.dump()) {
                events::input(&format!("cannot write {out}: {e}"));
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

/// The exit code's number, for the trail.
fn code_of(c: ExitCode) -> u8 {
    (0..=u8::MAX).find(|&n| ExitCode::from(n) == c).unwrap_or(u8::MAX)
}

/// The trail's flags: before the command only, since a command's arguments run on into slang's.
const TRAIL_FLAGS: &[&str] = &["-q", "--quiet", "-v", "--verbose"];

pub fn main() -> ExitCode {
    let all: Vec<String> = std::env::args().skip(1).collect();
    let lead = all.iter().take_while(|a| TRAIL_FLAGS.contains(&a.as_str())).count();
    // ⛔ Both flags SET SOMETHING: `vyges-events` reads its floor from `VYGES_LOG` once, so they
    // land there before the first event. An explicit `VYGES_LOG` in the environment wins.
    if std::env::var_os("VYGES_LOG").is_none() {
        if all[..lead].iter().any(|a| a == "-q" || a == "--quiet") {
            std::env::set_var("VYGES_LOG", "error");
        } else if lead > 0 {
            std::env::set_var("VYGES_LOG", "debug");
        }
    }
    let args = &all[lead..];
    let code = run(args);
    if let Some(cmd) = args.first().filter(|c| COMMANDS.contains(&c.as_str())) {
        events::done(cmd, code_of(code));
    }
    code
}

fn run(args: &[String]) -> ExitCode {
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
        Some("ir-pass") => ir_pass(&args[1..]),
        Some("synthesize") => synthesize(&args[1..]),
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

    // Rule: the trail's DONE event reports the number the process exits with.
    #[test]
    fn the_trail_reports_the_exit_code_given() {
        for n in [0, 1, 2, 3] {
            assert_eq!(code_of(ExitCode::from(n)), n);
        }
    }

    #[test]
    fn the_descriptor_is_valid_json_with_a_legal_maturity() {
        let d: serde_json::Value = serde_json::from_str(DESCRIBE).expect("descriptor is valid JSON");
        assert_eq!(d["schema"], "vyges-tool-descriptor/1.1");
        assert_eq!(d["name"], "syn");
        // Anything else is read as `discovered` and every verdict becomes `unknown`.
        let m = d["maturity"].as_str().unwrap();
        assert!(["discovered", "structured", "workflow-validated"].contains(&m), "{m}");
        // `eq` is the schema's predicate; `equals` is dropped at runtime and the verdict is unknown.
        assert_eq!(d["assertion"]["pass_when"]["eq"], "ok");
    }

    #[test]
    fn the_usage_spells_the_engine_under_its_group() {
        // The dispatcher REFUSES a wrong group prefix, so the help must spell the right one.
        for c in COMMANDS {
            assert!(USAGE.contains(&format!("vyges physical syn {c}")), "{c}");
        }
    }
}
