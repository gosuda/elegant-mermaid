use crate::{diag::Diagnostic, r#gen::lintrules::LintRule, model::gantt::Model};
use std::collections::BTreeSet;

pub(crate) fn run(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    let ids: BTreeSet<&str> = model.tasks.iter().map(|t| t.id.as_str()).collect();
    let mut seen = BTreeSet::new();
    let mut occupied = vec![false; model.sections.len()];
    for task in &model.tasks {
        if let Some(section) = task.section.and_then(|i| occupied.get_mut(i)) {
            *section = true;
        }
        if !task.generated
            && !seen.insert(task.id.as_str())
            && row.code == "gantt/duplicate-task-id"
        {
            out.push(super::common::row_diagnostic(
                row,
                row.summary.to_owned(),
                task.data_span,
                Vec::new(),
            ));
        }
        if row.code == "gantt/undefined-dependency" {
            for operand in [&task.start, &task.end] {
                let mut words = operand.text.split_whitespace();
                if matches!(words.next(), Some("after" | "until")) {
                    for id in words {
                        if !ids.contains(id) {
                            out.push(super::common::row_diagnostic(
                                row,
                                row.summary.to_owned(),
                                operand.span,
                                Vec::new(),
                            ));
                        }
                    }
                }
            }
        }
    }
    if row.code == "gantt/empty-section" {
        for (section, used) in model.sections.iter().zip(occupied) {
            if !used {
                out.push(super::common::row_diagnostic(
                    row,
                    row.summary.to_owned(),
                    section.span,
                    Vec::new(),
                ));
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    #[test]
    fn gantt_rules() {
        let cases = [
            (
                "gantt/duplicate-task-id",
                "A :a, 2024-01-01, 1d\nB :a, 2024-01-02, 1d",
                "A :a, 2024-01-01, 1d\nB :b, 2024-01-02, 1d",
            ),
            (
                "gantt/undefined-dependency",
                "A :a, after missing, 1d",
                "A :a, 2024-01-01, 1d\nB :b, after a, 1d",
            ),
            (
                "gantt/empty-section",
                "section Empty",
                "section Full\nA :a, 2024-01-01, 1d",
            ),
        ];
        for (code, bad, good) in cases {
            for (body, expected) in [(bad, true), (good, false)] {
                let source = format!("gantt\n{body}\n");
                let document = crate::parse(&source);
                let config = crate::LintConfig {
                    select: vec![code.to_owned()],
                    ..Default::default()
                };
                assert_eq!(
                    crate::lint(&document, &config)
                        .iter()
                        .any(|d| d.code == code),
                    expected,
                    "{code}: {body}"
                );
            }
        }
    }
}
