// SPDX-License-Identifier: Apache-2.0
//! `vyges_syn` — integrated logic synthesis from RTL to a mapped netlist, on the shared AIG core.
//!
//! Stages are added here one at a time, each named after the step it performs and kept in the order
//! the command runs them.

pub mod elab;
pub mod ir;
