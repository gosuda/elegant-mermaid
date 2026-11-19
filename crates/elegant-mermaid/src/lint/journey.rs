use crate::{diag::Diagnostic, r#gen::lintrules::LintRule, model::journey::Model};

pub(crate) fn run(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    match row.code {
        "journey/empty-section" => {
            let mut task = 0;
            for section in &model.sections {
                while task < model.tasks.len()
                    && model.tasks[task].section_span.start < section.span.start
                {
                    task += 1;
                }
                if task == model.tasks.len() || model.tasks[task].section_span != section.span {
                    out.push(super::common::row_diagnostic(
                        row,
                        row.summary.into(),
                        section.span,
                        Vec::new(),
                    ));
                }
            }
        }
        "journey/task-without-actor" => {
            for task in &model.tasks {
                if task.without_actor {
                    out.push(super::common::row_diagnostic(
                        row,
                        row.summary.into(),
                        task.name_span,
                        Vec::new(),
                    ));
                }
            }
        }
        "journey/no-tasks" if model.tasks.is_empty() => {
            out.push(super::common::row_diagnostic(
                row,
                row.summary.into(),
                model.header_span,
                Vec::new(),
            ));
        }
        _ => {}
    }
    out
}

#[cfg(test)]
mod tests {
    #[test]
    fn source_predicates() {
        let cases = [
            (
                "journey/empty-section",
                "journey\nsection A\nsection A\nTask:3:Bob\n",
                "journey\nsection A\nTask:3:Bob\nsection A\nTask:3:Bob\n",
            ),
            (
                "journey/task-without-actor",
                "journey\nTask:3\n",
                "journey\nTask:3:Bob\n",
            ),
            ("journey/no-tasks", "journey\n", "journey\nTask:3:Bob\n"),
            (
                "journey/task-without-actor",
                "journey\nTask:3: , ,\n",
                "journey\nTask:3: \u{a0}\n",
            ),
        ];
        for (code, trigger, clean) in cases {
            for row in crate::r#gen::lintrules::LINT_RULES
                .iter()
                .filter(|r| r.code == code)
            {
                for (text, want) in [(trigger, 1), (clean, 0)] {
                    let parsed = crate::syntax::journey::parse(text, &[]);
                    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
                    let (model, diagnostics) =
                        crate::model::journey::resolve(text, &parsed.document);
                    assert!(diagnostics.is_empty(), "{diagnostics:?}");
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
