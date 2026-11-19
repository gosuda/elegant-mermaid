use crate::{
    diag::Diagnostic,
    r#gen::lintrules::LintRule,
    model::architecture::{EdgeDeclaration, Model},
};
use std::collections::BTreeSet;

pub(crate) fn no_elements(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    if model.element_declarations == 0 {
        vec![super::common::row_diagnostic(
            row,
            row.summary.to_owned(),
            model.header_span,
            Vec::new(),
        )]
    } else {
        Vec::new()
    }
}
pub(crate) fn no_edges(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    if model.element_declarations > 0 && model.edge_declarations.is_empty() {
        vec![super::common::row_diagnostic(
            row,
            row.summary.to_owned(),
            model.header_span,
            Vec::new(),
        )]
    } else {
        Vec::new()
    }
}
pub(crate) fn duplicate_edge(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    let mut seen = BTreeSet::new();
    let mut out = Vec::new();
    for declaration in &model.edge_declarations {
        let edge = match declaration {
            EdgeDeclaration::Resolved(index) => &model.edges[*index],
            EdgeDeclaration::Rejected(edge) => edge.as_ref(),
        };
        let key = (
            edge.from.as_str(),
            edge.to.as_str(),
            edge.from_side.as_str(),
            edge.to_side.as_str(),
            edge.from_group,
            edge.to_group,
            edge.from_into,
            edge.to_into,
        );
        if !seen.insert(key) {
            out.push(super::common::row_diagnostic(
                row,
                row.summary.to_owned(),
                edge.span,
                Vec::new(),
            ));
        }
    }
    out
}
#[cfg(test)]
#[path = "architecture_test.rs"]
mod tests;
