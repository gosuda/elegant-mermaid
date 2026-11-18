//! Syntax of the `journey` kind: lexer, grammar, and diagnostics of
//! `spec/grammar/journey.md`.

pub mod ast;
pub mod lexer;
pub mod parser;

pub use lexer::{is_space, trim};
pub use parser::parse;

use crate::diag::{Diagnostic, Severity};

pub(crate) const C_UNEXPECTED: &str = "journey/unexpected-token";

pub(crate) const C_UNKNOWN: &str = "journey/unknown-statement";

pub(crate) const C_UNTERMINATED: &str = "journey/unterminated";

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
#[allow(clippy::panic, clippy::unwrap_used, clippy::expect_used)]
mod tests;
