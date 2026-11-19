pub mod ast;
pub mod lexer;
mod lexer_rules;
pub mod parser;
mod parser_nodes;
mod parser_statements;
pub use parser::parse;

pub(crate) fn diagnostic(
    code: &'static str,
    message: String,
    span: crate::source::Span,
) -> crate::diag::Diagnostic {
    crate::diag::Diagnostic {
        code,
        severity: crate::diag::Severity::Error,
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
