//! Syntax of the `quadrant` kind: lexer modes, grammar, and diagnostics of
//! `spec/grammar/quadrant.md`.

pub mod ast;
mod entities;
pub mod lexer;
pub mod parser;

pub use parser::parse;

use crate::diag::{Diagnostic, Severity};

pub(crate) const C_UNEXPECTED: &str = "quadrant/unexpected-token";

pub(crate) const C_UNKNOWN: &str = "quadrant/unknown-statement";

pub(crate) const C_UNTERMINATED: &str = "quadrant/unterminated";

pub(crate) fn diagnostic(
    code: &'static str,
    message: String,
    span: crate::source::Span,
) -> Diagnostic {
    Diagnostic {
        code,
        severity: Severity::Error,
        message,
        span,
        related: Vec::new(),
        help: crate::r#gen::diagnostics::DIAGNOSTICS
            .iter()
            .find(|row| row.code == code)
            .map_or("", |row| row.help)
            .into(),
        fixes: Vec::new(),
    }
}

#[cfg(test)]
mod tests;
