//! Syntax of the `treeview` kind: lexical rules, box-drawing input, grammar,
//! and diagnostics of `spec/grammar/treeview.md`.

pub mod ast;
mod boxdraw;
mod lexer;
pub mod parser;
mod prepare;
mod text;

pub use parser::{Parsed, parse};

use crate::diag::{Diagnostic, Severity};

pub(crate) const C_UNEXPECTED: &str = "treeview/unexpected-token";

pub(crate) const C_UNKNOWN: &str = "treeview/unknown-statement";

pub(crate) const C_UNTERMINATED: &str = "treeview/unterminated";

pub(crate) const C_EMPTY_BOX: &str = "treeview/empty-box-node";

pub(crate) const C_MIXED: &str = "treeview/mixed-indentation";

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
