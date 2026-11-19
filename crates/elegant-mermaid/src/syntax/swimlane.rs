//! The `swimlane` kind: the flowchart grammar with the `swimlane-beta` header.
//!
//! The normative text is `spec/grammar/swimlane.md`. The grammar, the lexer modes,
//! and the model resolution are the flowchart ones; only the header keyword and the
//! diagnostic prefix differ.

use crate::diag::Diagnostic;
use crate::source::Span;
use crate::syntax::flowchart::parser::Parsed;

/// Parses `src`, skipping the removed spans that preprocessing found, with every
/// kind-specific diagnostic under the `swimlane/` prefix.
pub fn parse(src: &str, removed: &[Span]) -> Parsed {
    let mut parsed = crate::syntax::flowchart::parse(src, removed);
    for diagnostic in &mut parsed.diagnostics {
        remap(diagnostic);
    }
    parsed
}

fn remap(diagnostic: &mut Diagnostic) {
    let Some(name) = diagnostic.code.strip_prefix("flowchart/") else {
        return;
    };
    let code: &'static str = crate::r#gen::diagnostics::DIAGNOSTICS
        .iter()
        .map(|row| row.code)
        .find(|candidate| candidate.strip_prefix("swimlane/") == Some(name))
        .unwrap_or(diagnostic.code);
    diagnostic.code = code;
    diagnostic.help = help_text(code);
}

fn help_text(code: &str) -> String {
    crate::r#gen::diagnostics::DIAGNOSTICS
        .iter()
        .find(|row| row.code == code)
        .map(|row| row.help)
        .unwrap_or("")
        .to_owned()
}
