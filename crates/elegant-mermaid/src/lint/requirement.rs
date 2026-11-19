use crate::diag::Diagnostic;
use crate::r#gen::lintrules::LintRule;
use crate::model::requirement::{IdDeclaration, Model, NodeRef};
use std::collections::BTreeSet;

pub(crate) fn run(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    let mut seen = BTreeSet::new();
    match row.code {
        "requirement/duplicate-name" => {
            for declaration in &model.declarations {
                let name = match declaration.node {
                    NodeRef::Requirement(index) => &model.requirements[index].name,
                    NodeRef::Element(index) => &model.elements[index].name,
                };
                if !name.is_empty() && !seen.insert(name.as_str()) {
                    out.push(super::common::row_diagnostic(
                        row,
                        row.summary.to_owned(),
                        declaration.span,
                        Vec::new(),
                    ));
                }
            }
        }
        "requirement/duplicate-id" => {
            for declaration in &model.id_declarations {
                let value = match declaration {
                    IdDeclaration::Field { requirement, field } => {
                        &model.requirements[*requirement].fields[*field].value
                    }
                    IdDeclaration::Discarded(value) => value,
                };
                if !seen.insert(value.value.as_str()) {
                    out.push(super::common::row_diagnostic(
                        row,
                        row.summary.to_owned(),
                        value.span,
                        Vec::new(),
                    ));
                }
            }
        }
        "requirement/undefined-reference" => {
            for relation in &model.relationships {
                let mut endpoints = [
                    (&relation.from, relation.from_node),
                    (&relation.to, relation.to_node),
                ];
                if endpoints[0].0.span.start > endpoints[1].0.span.start {
                    endpoints.swap(0, 1);
                }
                for (value, node) in endpoints {
                    if node.is_none() {
                        out.push(super::common::row_diagnostic(
                            row,
                            row.summary.to_owned(),
                            value.span,
                            Vec::new(),
                        ));
                    }
                }
            }
        }
        _ => {}
    }
    out
}

#[cfg(test)]
#[path = "requirement_tests.rs"]
mod tests;
