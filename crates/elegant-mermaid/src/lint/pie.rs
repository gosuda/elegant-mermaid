use crate::{diag::Diagnostic, r#gen::lintrules::LintRule, model::pie::Model};

pub(crate) fn run(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    let mut seen = std::collections::BTreeSet::new();
    for item in &model.occurrences {
        let label = item.section.map_or(item.label.as_str(), |index| {
            model.sections[index].label.as_str()
        });
        let duplicate = !seen.insert(label);
        if row.code == "pie/duplicate-label" && duplicate {
            out.push(super::common::row_diagnostic(
                row,
                row.summary.into(),
                item.label_span,
                Vec::new(),
            ));
        }
        if row.code == "pie/zero-value" && item.exact_zero {
            out.push(super::common::row_diagnostic(
                row,
                row.summary.into(),
                item.number_span,
                Vec::new(),
            ));
        }
    }
    if row.code == "pie/no-data" && model.occurrences.is_empty() {
        out.push(super::common::row_diagnostic(
            row,
            row.summary.into(),
            model.header,
            Vec::new(),
        ));
    }
    out
}

#[cfg(test)]
mod tests {
    #[test]
    fn source_predicates() {
        let cases = [
            (
                "pie/duplicate-label",
                "pie\n\"A\":1\n\"A\":2\n",
                "pie\n\"A\":1\n\"B\":2\n",
            ),
            ("pie/zero-value", "pie\n\"A\":0\n", "pie\n\"A\":0.0001\n"),
            ("pie/no-data", "pie\n", "pie\n\"A\":1\n"),
            (
                "pie/duplicate-label",
                "pie\n\"A\":0.0001\n\"A\":0\n",
                "pie\n\"A\":-1\n",
            ),
            (
                "pie/zero-value",
                "pie\n\"A\":0.0001\n\"A\":0\n",
                "pie\n\"A\":-1\n",
            ),
            ("pie/no-data", "pie\n", "pie\n\"A\":-1\n"),
        ];
        for (code, trigger, clean) in cases {
            for row in crate::r#gen::lintrules::LINT_RULES
                .iter()
                .filter(|r| r.code == code)
            {
                for (text, want) in [(trigger, 1), (clean, 0)] {
                    let parsed = crate::syntax::pie::parse(text, &[]);
                    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
                    let (model, diagnostics) = crate::model::pie::resolve(text, &parsed.document);
                    assert!(
                        diagnostics.iter().all(|d| d.code == "pie/negative-value"),
                        "{diagnostics:?}"
                    );
                    let got = super::run(&model, row);
                    assert_eq!(got.len(), want, "{code}: {got:?}");
                    assert!(
                        got.iter().all(|d| d.code == code
                            && d.message == row.summary
                            && d.help == row.help)
                    );
                }
            }
        }
    }
}
