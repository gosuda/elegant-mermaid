use crate::diag::Diagnostic;
use crate::r#gen::lintrules::LintRule;
use crate::model::class::Model;
use std::collections::BTreeSet;

pub(crate) fn run(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    match row.code {
        "class/duplicate-class" => {
            let mut seen = vec![false; model.classes.len()];
            for declaration in &model.declarations {
                if seen[declaration.class] {
                    out.push(super::common::row_diagnostic(
                        row,
                        row.summary.to_owned(),
                        declaration.span,
                        Vec::new(),
                    ));
                }
                seen[declaration.class] = true;
            }
        }
        "class/no-duplicate-methods" => {
            for class in &model.classes {
                let mut seen = BTreeSet::new();
                for member in &class.method_candidates {
                    if !seen.insert(member.key.as_str()) {
                        out.push(super::common::row_diagnostic(
                            row,
                            row.summary.to_owned(),
                            member.span,
                            Vec::new(),
                        ));
                    }
                }
            }
            out.sort_by_key(|diagnostic| diagnostic.span.start);
        }
        _ => {}
    }
    out
}

#[cfg(test)]
#[path = "class_tests.rs"]
mod tests;
