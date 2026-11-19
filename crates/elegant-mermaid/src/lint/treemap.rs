use crate::diag::Diagnostic;
use crate::r#gen::lintrules::LintRule;
use crate::model::treemap::Model;
use std::collections::BTreeSet;

pub(crate) fn run(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    let mut seen = BTreeSet::new();
    let mut leaves = 0;
    for node in &model.nodes {
        if node.leaf {
            leaves += 1;
            if row.code == "treemap/zero-value"
                && node.exact_zero
                && let Some(value_span) = node.value_span
            {
                out.push(super::common::row_diagnostic(
                    row,
                    row.summary.to_owned(),
                    value_span,
                    Vec::new(),
                ));
            }
            if row.code == "treemap/branch-with-value" && node.next_more_indented {
                out.push(super::common::row_diagnostic(
                    row,
                    row.summary.to_owned(),
                    node.name_span,
                    Vec::new(),
                ));
            }
        }
        if !seen.insert((node.parent, node.name.as_str()))
            && row.code == "treemap/duplicate-sibling"
        {
            out.push(super::common::row_diagnostic(
                row,
                row.summary.to_owned(),
                node.name_span,
                Vec::new(),
            ));
        }
    }
    if row.code == "treemap/no-leaves" && leaves == 0 {
        out.push(super::common::row_diagnostic(
            row,
            row.summary.to_owned(),
            model.span,
            Vec::new(),
        ));
    }
    out
}

#[cfg(test)]
mod tests {
    #[test]
    fn treemap_source_predicates() -> Result<(), Box<dyn std::error::Error>> {
        for (code, trigger, clean) in [
            ("treemap/zero-value", "\"A\": 0\n", "\"A\": 1\n"),
            ("treemap/zero-value", "\"A\": 0.\n", "\"A\": 0.0001\n"),
            ("treemap/zero-value", "\"A\": 0_0\n", "\"A\": 0.0001\n"),
            ("treemap/zero-value", "\"A\": 0,0\n", "\"A\": 0.0001\n"),
            (
                "treemap/duplicate-sibling",
                "\"B\"\n\"A\": 1\n  \"B\"\n",
                "\"B\"\n\"A\"\n  \"B\"\n",
            ),
            ("treemap/no-leaves", "\"Group\"\n", "\"A\": 1\n"),
            (
                "treemap/duplicate-sibling",
                "\"A\": 1\n\"A\": 2\n",
                "\"P\"\n  \"A\": 1\n\"Q\"\n  \"A\": 2\n",
            ),
            (
                "treemap/branch-with-value",
                "\"A\": 1\n  \"B\": 2\n",
                "\"A\": 1\n\"B\": 2\n",
            ),
        ] {
            let row = crate::r#gen::lintrules::LINT_RULES
                .iter()
                .find(|r| r.code == code)
                .ok_or("missing lint registry row")?;
            for (body, count) in [(trigger, 1), (clean, 0)] {
                let source = format!("treemap\n{body}");
                let (ast, diagnostics) = crate::syntax::treemap::parse(&source, &[]);
                assert!(diagnostics.is_empty(), "{diagnostics:?}");
                let (model, diagnostics) = crate::model::treemap::resolve(&source, &ast);
                assert!(diagnostics.is_empty(), "{diagnostics:?}");
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
        Ok(())
    }

    #[test]
    fn valued_leaves_do_not_parent_siblings() -> Result<(), Box<dyn std::error::Error>> {
        let source = "treemap\n\"B\"\n\"A\": 1\n  \"B\"\n";
        let (ast, diagnostics) = crate::syntax::treemap::parse(source, &[]);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let (model, diagnostics) = crate::model::treemap::resolve(source, &ast);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        for (code, start) in [
            ("treemap/duplicate-sibling", 21),
            ("treemap/branch-with-value", 12),
        ] {
            let row = crate::r#gen::lintrules::LINT_RULES
                .iter()
                .find(|row| row.code == code)
                .ok_or("missing lint registry row")?;
            let findings = super::run(&model, row);
            assert_eq!(findings.len(), 1, "{code}: {findings:?}");
            assert_eq!(findings[0].span.start, start, "{code}");
        }
        Ok(())
    }
}
