use crate::{diag::Diagnostic, r#gen::lintrules::LintRule, model::xychart::Model, source::Span};

fn finding(row: &LintRule, span: Span) -> Diagnostic {
    super::common::row_diagnostic(row, row.summary.to_owned(), span, Vec::new())
}

pub(crate) fn missing_x_axis(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    if !model.plots.is_empty() && model.x.span.start == model.x.span.end {
        vec![finding(row, model.header_span)]
    } else {
        Vec::new()
    }
}

pub(crate) fn missing_y_axis(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    if !model.plots.is_empty() && model.y.span.start == model.y.span.end {
        vec![finding(row, model.header_span)]
    } else {
        Vec::new()
    }
}

pub(crate) fn no_series(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    if model.plots.is_empty() {
        vec![finding(row, model.header_span)]
    } else {
        Vec::new()
    }
}

pub(crate) fn series_length_mismatch(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    let mut n = model.x.band.then_some(model.x.categories.len());
    let mut out = Vec::new();
    for plot in &model.plots {
        let expected = *n.get_or_insert(plot.raw_point_count);
        if plot.raw_point_count != expected {
            out.push(finding(row, plot.span));
        }
    }
    out
}
