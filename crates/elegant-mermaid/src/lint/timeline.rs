use crate::{diag::Diagnostic, r#gen::lintrules::LintRule, model::timeline::Model, source::Span};

fn finding(row: &LintRule, span: Span) -> Diagnostic {
    super::common::row_diagnostic(row, row.summary.to_owned(), span, Vec::new())
}

pub(crate) fn no_entries(model: &Model, header: Span, row: &LintRule) -> Vec<Diagnostic> {
    if model.sections.is_empty() && model.periods.is_empty() {
        vec![finding(row, header)]
    } else {
        Vec::new()
    }
}

pub(crate) fn empty_section(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    model
        .sections
        .iter()
        .enumerate()
        .filter(|(i, _)| !model.periods.iter().any(|p| p.section == Some(*i)))
        .map(|(_, s)| finding(row, s.span))
        .collect()
}

pub(crate) fn empty_event(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    model
        .periods
        .iter()
        .flat_map(|p| &p.events)
        .filter(|e| e.text.trim().is_empty())
        .map(|e| finding(row, e.span))
        .collect()
}
