use crate::{diag::Diagnostic, r#gen::lintrules::LintRule, model::radar::Model, source::Span};

fn finding(row: &LintRule, span: Span) -> Diagnostic {
    super::common::row_diagnostic(row, row.summary.to_owned(), span, Vec::new())
}

pub(crate) fn no_curves(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    if model.curves.is_empty() {
        vec![finding(row, model.header_span)]
    } else {
        Vec::new()
    }
}

pub(crate) fn curve_length_mismatch(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    model
        .curves
        .iter()
        .filter(|c| c.positional && c.entry_count != model.axes.len())
        .map(|c| finding(row, c.span))
        .collect()
}

pub(crate) fn duplicate_axis(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    let mut seen = std::collections::BTreeSet::new();
    model
        .axes
        .iter()
        .filter(|a| !seen.insert(a.label.as_str()))
        .map(|a| finding(row, a.span))
        .collect()
}
