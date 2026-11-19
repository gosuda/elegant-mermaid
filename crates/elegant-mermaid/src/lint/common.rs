use crate::diag::{Diagnostic, Severity};
use crate::r#gen::lintrules::LintRule;
use crate::source::Span;

/// The internal view of one block that a common rule reads.
pub struct Block<'a> {
    pub source: &'a str,
    #[expect(
        dead_code,
        reason = "the CLI maps block spans to hosts; the core view stays block-relative"
    )]
    pub host_offset: usize,
    pub header: Span,
    pub kind: Option<&'static str>,
    pub frontmatter: Option<Span>,
}

pub(crate) fn acc_title_missing(b: &Block<'_>, row: &LintRule) -> Vec<Diagnostic> {
    missing_statement(b, row, "accTitle")
}

pub(crate) fn acc_descr_missing(b: &Block<'_>, row: &LintRule) -> Vec<Diagnostic> {
    missing_statement(b, row, "accDescr")
}

/// Warns when the header token ends in `-beta` (ASCII case folded) and names
/// the token itself: `block` is not beta, `block-beta` is.
pub(crate) fn no_experimental(b: &Block<'_>, row: &LintRule) -> Vec<Diagnostic> {
    let Some(token) = b.source.get(b.header.start..b.header.end) else {
        return Vec::new();
    };
    if !beta_token(token) {
        return Vec::new();
    }
    vec![row_diagnostic(
        row,
        row.summary.replace("KIND", token),
        b.header,
        Vec::new(),
    )]
}

fn beta_token(token: &str) -> bool {
    const SUFFIX: &str = "-beta";
    token.len() >= SUFFIX.len()
        && token.as_bytes()[token.len() - SUFFIX.len()..].eq_ignore_ascii_case(SUFFIX.as_bytes())
}

fn missing_statement(b: &Block<'_>, row: &LintRule, name: &str) -> Vec<Diagnostic> {
    if has_statement(b, name) {
        return Vec::new();
    }
    vec![row_diagnostic(
        row,
        row.summary.to_owned(),
        b.header,
        Vec::new(),
    )]
}

fn has_statement(b: &Block<'_>, name: &str) -> bool {
    for (start, end) in crate::lint::suppression::lines(b.source) {
        if b.frontmatter.is_some_and(|front| start < front.end) {
            continue;
        }
        let line = &b.source[start..end];
        let trimmed = line.trim_start_matches([' ', '\t']);
        if trimmed.starts_with("%%") {
            continue;
        }
        let Some(rest) = trimmed.strip_prefix(name) else {
            continue;
        };
        if rest.trim_start_matches([' ', '\t']).starts_with(':') {
            return true;
        }
    }
    false
}

/// Builds a rule diagnostic. The engine overwrites the severity with the
/// effective value, so the placeholder here never reaches the output.
pub(crate) fn row_diagnostic(
    row: &LintRule,
    message: String,
    span: Span,
    related: Vec<crate::diag::Related>,
) -> Diagnostic {
    Diagnostic {
        code: row.code,
        severity: Severity::Info,
        message,
        span,
        related,
        help: row.help.to_owned(),
        fixes: Vec::new(),
    }
}
