// SPDX-License-Identifier: Apache-2.0
//! The word-level netlist synthesis works on: nets, instances, the graph, and its text form.

pub mod constant;
pub mod dump;
pub mod graph;
pub mod instance;
pub mod net;
pub mod parse;
pub mod stats;

pub use graph::{Equivalence, Graph, InstId};
pub use instance::{BinOp, Instance, Kind, ShiftOp};
pub use net::{Bundle, Const, ControlNet, Net, Trit};
