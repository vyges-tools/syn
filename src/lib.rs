// SPDX-License-Identifier: Apache-2.0
//! `vyges_syn` — integrated logic synthesis from RTL to a mapped netlist, on the shared AIG core.
//!
//! Stages are added here one at a time, each named after the step it performs and kept in the order
//! the command runs them.

// The crate's own name inside it: the command-line entry ([`cli_main`]) is built into the
// library too, and its `vyges_syn::…` paths resolve here.
extern crate self as vyges_syn;

pub mod elab;
pub mod events;
pub mod flow;
pub mod ir;
pub mod library;
pub mod synthesis;

/// The `vyges-syn` command-line entry (the binary's `main`), built into the library too so a
/// suite binary can link every engine and run the one it is invoked as.
#[cfg(feature = "suite")]
#[doc(hidden)]
#[path = "main.rs"]
pub mod cli_main;
