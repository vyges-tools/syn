// SPDX-License-Identifier: Apache-2.0
//! The `vyges-events` causal trail for this engine.
//!
//! Every event goes to **stderr**; the netlist, the report and the reference-format log lines go to stdout (or
//! `-o`), so a caller can parse one without the other. `code` is the clustering key and `objects`
//! are the cross-stage co-reference keys.
//!
//! Codes are stable, and each names *a situation*, not a message:
//!
//! | code | meaning |
//! |---|---|
//! | `SYN-INPUT` | an input could not be read or written (exit 2) |
//! | `SYN-REFUSED` | the command, or an option of it, is not implemented in this build (exit 3) |
//! | `SYN-STEP` | one step of a command, at `debug` — the trail `-v` turns on |
//! | `SYN-DONT-USE` | a `--dont-use` pattern matched no library cell, at `warn` (the run goes on) |
//! | `SYN-DONE` | one invocation finished; its command, status and exit code |
//!
//! ⛔ **`SYN-DONE` is emitted for EVERY invocation of a command, whatever the outcome.** A run
//! that refused or failed says so in the trail at `error` rather than leaving the caller to infer
//! it from an exit code it may not have kept.

use vyges_events::{emit, Event, Severity};

const TOOL: &str = "vyges-syn";

/// An input could not be read, or an output not written.
pub fn input(msg: &str) {
    emit(&Event::new(TOOL, Severity::Error, msg.to_string()).with_code("SYN-INPUT"));
}

/// The command (or what it was asked to do) is not implemented in this build.
pub fn refused(why: &str) {
    emit(&Event::new(TOOL, Severity::Error, why.to_string()).with_code("SYN-REFUSED"));
}

/// A `--dont-use` pattern that names no library cell: most likely a typo, or the wrong library.
pub fn dont_use_unmatched(pattern: &str) {
    emit(
        &Event::new(TOOL, Severity::Warn, format!("--dont-use {pattern}: no library cell matches"))
            .with_code("SYN-DONT-USE")
            .with_objects(vec![format!("pattern:{pattern}")]),
    );
}

/// One step of a command, at `debug`.
pub fn step(command: &str, what: &str) {
    emit(
        &Event::new(TOOL, Severity::Debug, format!("{command}: {what}"))
            .with_code("SYN-STEP")
            .with_objects(vec![format!("command:{command}")]),
    );
}

/// What an exit code means, as the trail reports it.
pub fn status(code: u8) -> &'static str {
    match code {
        0 => "ok",
        1 => "finding",
        2 => "input",
        3 => "refused",
        _ => "failed",
    }
}

/// One invocation finished: `info` when it succeeded, `error` otherwise.
pub fn done(command: &str, code: u8) {
    let status = status(code);
    let sev = if code == 0 { Severity::Info } else { Severity::Error };
    emit(
        &Event::new(TOOL, sev, format!("{command}: {status} (exit {code})"))
            .with_code("SYN-DONE")
            .with_objects(vec![format!("command:{command}"), format!("status:{status}")]),
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    // Rule: the exit codes are the engine's contract (main.rs): a finding and a failure to run
    // never share a status word.
    #[test]
    fn each_exit_code_has_its_own_status() {
        assert_eq!([status(0), status(1), status(2), status(3), status(9)], ["ok", "finding", "input", "refused", "failed"]);
    }
}
