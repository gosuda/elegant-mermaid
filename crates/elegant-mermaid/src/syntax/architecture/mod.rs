//! Syntax of the `architecture` kind: lexer, grammar, and diagnostics of
//! `spec/grammar/architecture.md`.

pub mod ast;
pub mod lexer;
pub mod parser;

pub use parser::parse;

use crate::diag::{Diagnostic, Severity};

pub(crate) const C_UNEXPECTED: &str = "architecture/unexpected-token";

pub(crate) const C_UNKNOWN: &str = "architecture/unknown-statement";

pub(crate) const C_UNTERMINATED: &str = "architecture/unterminated";

pub(crate) const C_DIRECTION: &str = "architecture/invalid-direction";

pub(crate) const C_TOO_FEW: &str = "architecture/align-too-few-members";

pub(crate) fn diagnostic(
    code: &'static str,
    message: String,
    span: crate::source::Span,
) -> Diagnostic {
    let row = crate::r#gen::diagnostics::DIAGNOSTICS
        .iter()
        .find(|row| row.code == code);
    Diagnostic {
        code,
        severity: row.map_or(Severity::Error, |row| severity(row.severity)),
        message,
        span,
        related: Vec::new(),
        help: row.map_or("", |row| row.help).into(),
        fixes: Vec::new(),
    }
}

fn severity(word: &str) -> Severity {
    match word {
        "warning" => Severity::Warning,
        "info" => Severity::Info,
        _ => Severity::Error,
    }
}

#[cfg(test)]
mod tests;
