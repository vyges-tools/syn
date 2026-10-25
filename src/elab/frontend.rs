// SPDX-License-Identifier: Apache-2.0
//! The SystemVerilog frontend (slang + sv-elab, in `vyges-slang-lib`) driving the graph builder.
//!
//! The frontend asks for one node at a time; each request goes to the [`Backend`] of the graph it
//! names. Graph 0 is the top instance's and is the result; the frontend starts others for
//! instances it elaborates on their own, and those are built and then dropped.

use vyges_slang_lib::elab::{self as fe, Call};

use super::backend::{Backend, BinaryOp, ElabError, PortConnection, PortDir, UnaryOp};
use crate::ir::net::{Bundle, Net};
use crate::ir::Graph;

fn unary(op: fe::UnaryOp) -> UnaryOp {
    use fe::UnaryOp as F;
    match op {
        F::Plus => UnaryOp::Plus,
        F::Minus => UnaryOp::Minus,
        F::BitwiseNot => UnaryOp::BitwiseNot,
        F::BitwiseAnd => UnaryOp::BitwiseAnd,
        F::BitwiseOr => UnaryOp::BitwiseOr,
        F::BitwiseXor => UnaryOp::BitwiseXor,
        F::BitwiseNand => UnaryOp::BitwiseNand,
        F::BitwiseNor => UnaryOp::BitwiseNor,
        F::BitwiseXnor => UnaryOp::BitwiseXnor,
        F::LogicalNot => UnaryOp::LogicalNot,
        F::Preincrement | F::Predecrement | F::Postincrement | F::Postdecrement => UnaryOp::Other,
    }
}

fn binary(op: fe::BinaryOp) -> BinaryOp {
    use fe::BinaryOp as F;
    match op {
        F::Add => BinaryOp::Add,
        F::Subtract => BinaryOp::Subtract,
        F::Multiply => BinaryOp::Multiply,
        F::Divide => BinaryOp::Divide,
        F::Mod => BinaryOp::Mod,
        F::BinaryAnd => BinaryOp::BinaryAnd,
        F::BinaryOr => BinaryOp::BinaryOr,
        F::BinaryXor => BinaryOp::BinaryXor,
        F::BinaryXnor => BinaryOp::BinaryXnor,
        F::Equality => BinaryOp::Equality,
        F::Inequality => BinaryOp::Inequality,
        F::CaseEquality => BinaryOp::CaseEquality,
        F::CaseInequality => BinaryOp::CaseInequality,
        F::GreaterThanEqual => BinaryOp::GreaterThanEqual,
        F::GreaterThan => BinaryOp::GreaterThan,
        F::LessThanEqual => BinaryOp::LessThanEqual,
        F::LessThan => BinaryOp::LessThan,
        F::LogicalAnd => BinaryOp::LogicalAnd,
        F::LogicalOr => BinaryOp::LogicalOr,
        F::LogicalShiftLeft => BinaryOp::LogicalShiftLeft,
        F::LogicalShiftRight => BinaryOp::LogicalShiftRight,
        F::ArithmeticShiftLeft => BinaryOp::ArithmeticShiftLeft,
        F::ArithmeticShiftRight => BinaryOp::ArithmeticShiftRight,
        F::WildcardEquality | F::WildcardInequality | F::LogicalImplication | F::LogicalEquivalence | F::Power => {
            BinaryOp::Other
        }
    }
}

fn nets(v: &[u32]) -> Bundle {
    v.iter().map(|&n| Net(n)).collect()
}

fn ids(b: Bundle) -> Vec<u32> {
    b.into_iter().map(|n| n.0).collect()
}

/// What the frontend logs, printed as the reference's logger prints it.
fn print_log(level: fe::LogLevel, code: i32, message: &str) {
    match level {
        fe::LogLevel::Info => println!("{message}"),
        fe::LogLevel::Warning => println!("[WARNING SYN-{code:04}] {message}"),
    }
}

/// Every graph the frontend builds; graph 0 is the result.
#[derive(Default)]
pub struct Frontend {
    graphs: Vec<Backend>,
}

impl Frontend {
    fn graph(&mut self, g: i32) -> &mut Backend {
        let g = g as usize;
        while self.graphs.len() <= g {
            self.graphs.push(Backend::new());
        }
        &mut self.graphs[g]
    }

    fn dispatch(b: &mut Backend, call: Call<'_>) -> Result<Bundle, ElabError> {
        let none = |r: Result<(), ElabError>| r.map(|()| Bundle::new());
        match call {
            Call::Unop { op, a, a_signed, y_width } => b.unop(unary(op), nets(a), a_signed, y_width),
            Call::Biop { op, a, b: bb, a_signed, b_signed, y_width } => {
                b.biop(binary(op), nets(a), nets(bb), a_signed, b_signed, y_width)
            }
            Call::Demux { a, s } => b.demux(nets(a), nets(s)),
            Call::Bwmux { a, b: bb, s } => b.bwmux(nets(a), nets(bb), nets(s)),
            Call::Bmux { a, s } => b.bmux(nets(a), nets(s)),
            Call::Shift { a, s, s_signed, width } => b.shift(nets(a), nets(s), s_signed, width),
            Call::Shiftx { a, s, s_signed, width } => b.shiftx(nets(a), nets(s), s_signed, width),
            Call::Mux { a, b: bb, s } => b.mux(nets(a), nets(bb), Net(s)),
            Call::Placeholder { width, name, public_name } => b.add_placeholder_signal(width, name, public_name),
            Call::Connect { target, source } => none(b.connect(&nets(target), &nets(source))),
            // Initial values and memory contents are not carried into the graph.
            Call::SetInit { .. } | Call::MemoryInit { .. } | Call::NewGraph { .. } => Ok(Bundle::new()),
            Call::Input { name, signal } => none(b.add_input(name, nets(signal))),
            Call::Output { name, signal } => none(b.add_output(name, nets(signal))),
            Call::Instance { cell_type, ports } => {
                let ports = ports
                    .into_iter()
                    .map(|p| PortConnection {
                        name: p.name.to_string(),
                        direction: match p.direction {
                            fe::Dir::Input => PortDir::Input,
                            fe::Dir::Output => PortDir::Output,
                            fe::Dir::InOut => PortDir::InOut,
                        },
                        value: nets(p.value),
                    })
                    .collect();
                none(b.add_instance(cell_type, ports))
            }
            Call::DualEdgeAldff { .. } => none(b.add_dual_edge_aldff()),
            Call::Dff { clk, d, q, clk_polarity, .. } => none(b.add_dff(&nets(clk), &nets(d), &nets(q), clk_polarity)),
            Call::Dffe { clk, en, d, q, clk_polarity, en_polarity, .. } => {
                none(b.add_dffe(&nets(clk), &nets(en), &nets(d), &nets(q), clk_polarity, en_polarity))
            }
            Call::Aldff { clk, aload, d, q, ad, clk_polarity, aload_polarity, .. } => none(b.add_aldff(
                &nets(clk),
                &nets(aload),
                &nets(d),
                &nets(q),
                &nets(ad),
                clk_polarity,
                aload_polarity,
            )),
        }
    }
}

impl fe::Backend for Frontend {
    fn call(&mut self, graph: i32, call: Call<'_>) -> Result<Vec<u32>, fe::ElabError> {
        Self::dispatch(self.graph(graph), call)
            .map(ids)
            .map_err(|e| fe::ElabError { code: e.code as i32, message: e.message })
    }

    fn log(&mut self, level: fe::LogLevel, code: i32, message: &str) {
        print_log(level, code, message);
    }
}

/// Why elaboration produced no graph.
#[derive(Debug, PartialEq, Eq)]
pub enum Failed {
    /// Stopped by options, sources or diagnostics (slang reported them).
    Reported,
    /// Ended with an error: its message code and text.
    Error(u32, String),
}

/// The reference command splits its argument string on whitespace: so do we.
pub fn split_args(args: &[String]) -> Vec<String> {
    args.join(" ").split_whitespace().map(str::to_string).collect()
}

/// Elaborates the design the slang arguments name: the top instance's graph, as the frontend
/// built it (no pass run over it).
pub fn elaborate(args: &[String], blackboxes: &[fe::BlackboxCell]) -> Result<Graph, Failed> {
    use std::io::Write;
    let _ = std::io::stdout().flush();
    let words = split_args(args);
    let refs: Vec<&str> = words.iter().map(String::as_str).collect();
    let mut fe_state = Frontend::default();
    match fe::elaborate(&refs, None, blackboxes, &mut fe_state) {
        Ok(top) => {
            let mut g = std::mem::take(&mut fe_state.graph(0).graph);
            g.name = top;
            Ok(g)
        }
        Err(fe::Failure::Failed) => Err(Failed::Reported),
        Err(fe::Failure::Error(e)) => Err(Failed::Error(e.code.max(0) as u32, e.message)),
        Err(fe::Failure::Exception(m)) | Err(fe::Failure::Nul(m)) => Err(Failed::Error(0, m)),
    }
}
