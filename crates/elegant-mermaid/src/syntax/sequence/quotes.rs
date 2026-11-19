//! The `sequence/quote-unclosed` warning: a participant or actor name or alias
//! that starts a quote and does not close it. Quotes stay ordinary text, so the
//! grammar does not change and the warning is the only effect.

use crate::diag::{Diagnostic, Edit, Fix, FixSafety, Severity};
use crate::r#gen::lintrules::LINT_RULES;
use crate::source::Span;

use super::C_QUOTE_UNCLOSED;

const BLANKS: [char; 2] = [' ', '\t'];
const CLOSE_QUOTE_TITLE: &str = "Insert the closing quote";

pub(super) fn unclosed(source: &str, token: Span) -> Option<Diagnostic> {
    let raw = source.get(token.start..token.end)?;
    let body = raw.trim_start_matches(BLANKS);
    let start = token.start + (raw.len() - body.len());
    let body = body.trim_end_matches(BLANKS);
    if !body.starts_with('"') || body.matches('"').count() % 2 == 0 {
        return None;
    }
    let span = Span {
        start,
        end: start + body.len(),
    };
    let row = LINT_RULES.iter().find(|row| row.code == C_QUOTE_UNCLOSED)?;
    Some(Diagnostic {
        code: C_QUOTE_UNCLOSED,
        severity: Severity::Warning,
        message: row.summary.to_owned(),
        span,
        related: Vec::new(),
        help: row.help.to_owned(),
        fixes: vec![Fix {
            title: CLOSE_QUOTE_TITLE.to_owned(),
            safety: FixSafety::Unsafe,
            edits: vec![Edit {
                span: Span {
                    start: span.end,
                    end: span.end,
                },
                new_text: "\"".to_owned(),
            }],
        }],
    })
}
