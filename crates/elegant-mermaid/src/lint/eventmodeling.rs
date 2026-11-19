use crate::{
    diag::Diagnostic, r#gen::lintrules::LintRule, model::eventmodeling::Model, source::Span,
};

fn finding(row: &LintRule, span: Span) -> Diagnostic {
    super::common::row_diagnostic(row, row.summary.to_owned(), span, Vec::new())
}

pub(crate) fn undefined_frame(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    model
        .frames
        .iter()
        .flat_map(|frame| &frame.sources)
        .filter(|reference| reference.source.is_none())
        .map(|reference| finding(row, reference.span))
        .collect()
}

pub(crate) fn invalid_flow(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for target in &model.frames {
        for reference in &target.sources {
            let Some(source) = reference.source else {
                continue;
            };
            let name = &model.frames[source].name;
            if model.frames.iter().any(|frame| {
                &frame.name == name && !allowed(&frame.entity_type, &target.entity_type)
            }) {
                out.push(finding(row, reference.span));
            }
        }
    }
    out
}

fn allowed(from: &str, to: &str) -> bool {
    match to {
        "cmd" | "command" => matches!(from, "ui" | "pcr" | "processor"),
        "evt" | "event" => matches!(from, "cmd" | "command"),
        "rmo" | "readmodel" => matches!(from, "evt" | "event"),
        "pcr" | "processor" | "ui" => matches!(from, "rmo" | "readmodel"),
        _ => false,
    }
}
