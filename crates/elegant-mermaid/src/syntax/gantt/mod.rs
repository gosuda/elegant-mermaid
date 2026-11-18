//! Syntax of the `gantt` kind: lexer, grammar, and diagnostics of
//! `spec/grammar/gantt.md`.

pub mod ast;
pub mod lexer;
pub mod parser;

pub use lexer::is_space;
pub use parser::parse;

use crate::diag::{Diagnostic, Severity};

pub(crate) const C_UNEXPECTED: &str = "gantt/unexpected-token";

pub(crate) const C_UNKNOWN: &str = "gantt/unknown-statement";

pub(crate) const C_UNTERMINATED: &str = "gantt/unterminated";

pub(crate) fn diagnostic(
    code: &'static str,
    message: String,
    span: crate::source::Span,
) -> Diagnostic {
    let row = crate::r#gen::diagnostics::DIAGNOSTICS
        .iter()
        .find(|row| row.code == code);
    let severity = match row.map_or("error", |row| row.severity) {
        "warning" => Severity::Warning,
        "info" => Severity::Info,
        _ => Severity::Error,
    };
    Diagnostic {
        code,
        severity,
        message,
        span,
        related: Vec::new(),
        help: row.map_or("", |row| row.help).into(),
        fixes: Vec::new(),
    }
}

#[cfg(test)]
#[allow(clippy::panic, clippy::unwrap_used, clippy::expect_used)]
mod tests;
