use crate::{diag::Diagnostic, r#gen::lintrules::LintRule, model::packet::Model, source::Span};

fn finding(row: &LintRule, span: Span) -> Diagnostic {
    super::common::row_diagnostic(row, row.summary.to_owned(), span, Vec::new())
}

pub(crate) fn no_fields(model: &Model, header: Span, row: &LintRule) -> Vec<Diagnostic> {
    if model.fields.is_empty() {
        vec![finding(row, header)]
    } else {
        Vec::new()
    }
}

pub(crate) fn empty_labels(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    model
        .fields
        .iter()
        .filter(|f| f.label.trim().is_empty())
        .map(|f| finding(row, f.label_span))
        .collect()
}
