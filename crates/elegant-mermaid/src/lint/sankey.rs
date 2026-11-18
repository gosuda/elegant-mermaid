use crate::diag::Diagnostic;
use crate::r#gen::lintrules::LintRule;
use crate::model::sankey::{Model, ValueKind};
use std::collections::BTreeSet;

pub(crate) fn run(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    let mut seen = BTreeSet::new();
    for link in &model.links {
        let duplicate = !seen.insert((link.source, link.target));
        let matches = row.code == "sankey/non-positive-value"
            && link.value.kind == ValueKind::Finite
            && link.value.thousandths <= 0
            || row.code == "sankey/duplicate-link" && duplicate
            || row.code == "sankey/self-loop" && link.source == link.target;
        if matches {
            out.push(super::common::row_diagnostic(
                row,
                row.summary.to_owned(),
                link.span,
                Vec::new(),
            ));
        }
    }
    out
}

#[cfg(test)]
mod tests {
    #[test]
    fn sankey_source_predicates() {
        for (code, trigger, clean) in [
            ("sankey/non-positive-value", "A,B,0\n", "A,B,1\n"),
            ("sankey/duplicate-link", "A,B,1\nA,B,2\n", "A,B,1\nB,A,2\n"),
            ("sankey/self-loop", "A,A,1\n", "A,B,1\n"),
        ] {
            let row = crate::r#gen::lintrules::LINT_RULES
                .iter()
                .find(|r| r.code == code);
            assert!(row.is_some(), "missing rule {code}");
            let Some(row) = row else {
                continue;
            };
            for (body, count) in [(trigger, 1), (clean, 0)] {
                let source = format!("sankey-beta\n{body}");
                let (ast, diagnostics) = crate::syntax::sankey::parser::parse(&source, &[]);
                assert!(diagnostics.is_empty(), "{diagnostics:?}");
                let (model, _) = crate::model::sankey::resolve(&source, &ast);
                let findings = super::run(&model, row);
                assert_eq!(findings.len(), count, "{code}: {source}");
                for finding in findings {
                    assert_eq!(finding.code, code);
                    assert_eq!(finding.message, row.summary);
                    assert_eq!(finding.help, row.help);
                    assert!(
                        finding.span.start < finding.span.end && finding.span.end <= source.len()
                    );
                }
            }
        }
    }
}
