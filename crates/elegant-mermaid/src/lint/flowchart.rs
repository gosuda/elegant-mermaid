use crate::diag::{Diagnostic, Related};
use crate::r#gen::lintrules::LintRule;
use crate::model::flowchart::{Decl, Model};

pub(crate) fn duplicate_ids(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for node in &model.nodes {
        let mut first: Option<&Decl> = None;
        for decl in &node.decls {
            let Some(label) = &decl.label else {
                continue;
            };
            match first {
                None => first = Some(decl),
                Some(known) if known.label.as_deref() != Some(label.as_str()) => {
                    out.push(crate::lint::common::row_diagnostic(
                        row,
                        row.summary.to_owned(),
                        decl.span,
                        vec![Related {
                            span: known.span,
                            message: "first declared here".to_owned(),
                        }],
                    ));
                }
                Some(_) => {}
            }
        }
    }
    out
}

pub(crate) fn subgraph_id_collisions(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    model
        .subgraph_collisions
        .iter()
        .map(|span| {
            crate::lint::common::row_diagnostic(row, row.summary.to_owned(), *span, Vec::new())
        })
        .collect()
}

pub(crate) fn label_at_in_unquoted(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    model
        .unquoted_at_spans
        .iter()
        .map(|span| {
            crate::lint::common::row_diagnostic(row, row.summary.to_owned(), *span, Vec::new())
        })
        .collect()
}
