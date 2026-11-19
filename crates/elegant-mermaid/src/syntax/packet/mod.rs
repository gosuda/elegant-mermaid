//! Syntax of the `packet` kind: lexer, grammar, and diagnostics of
//! `spec/grammar/packet.md`.

pub mod ast;
pub mod lexer;
pub mod parser;

pub use parser::parse;

use crate::diag::{Diagnostic, Severity};

pub(crate) const C_UNEXPECTED: &str = "packet/unexpected-token";

pub(crate) const C_UNKNOWN: &str = "packet/unknown-statement";

pub(crate) const C_UNTERMINATED: &str = "packet/unterminated";

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
