#[test]
fn consumer_rules_trigger_and_nontrigger() {
    for (code, source, expected) in [
        (
            "kanban/duplicate-column",
            "kanban\n  s[S]\n    a[A]\n  a[Column]\n",
            1,
        ),
        (
            "kanban/duplicate-task-id",
            "kanban\n  s[S]\n    a[A]\n  a[Column]\n",
            0,
        ),
        (
            "kanban/duplicate-task-id",
            "kanban\n  s[S]\n    a[A]\n    a[Again]\n",
            1,
        ),
        ("kanban/no-columns", "kanban\n", 1),
        ("kanban/no-columns", "kanban\n  s[S]\n", 0),
        ("kanban/empty-column", "kanban\n  s[S]\n", 1),
        ("kanban/empty-column", "kanban\n  s[S]\n    a[A]\n", 0),
        ("kanban/duplicate-column", "kanban\n  s[S]\n  s[S]\n", 1),
        ("kanban/duplicate-column", "kanban\n  s[S]\n  t[T]\n", 0),
        ("kanban/duplicate-task-id", "kanban\n  s[S]\n    s[A]\n", 1),
        ("kanban/duplicate-task-id", "kanban\n  s[S]\n    a[A]\n", 0),
    ] {
        let document = crate::parse(source);
        let config = crate::LintConfig {
            select: vec![code.to_owned()],
            ..Default::default()
        };
        let diagnostics = crate::lint(&document, &config);
        let findings: Vec<_> = diagnostics.iter().filter(|d| d.code == code).collect();
        assert_eq!(findings.len(), expected, "{code} on {source:?}");
        for diagnostic in findings {
            assert!(!diagnostic.message.is_empty() && !diagnostic.help.is_empty());
            assert!(
                diagnostic.span.start <= diagnostic.span.end && diagnostic.span.end <= source.len()
            );
        }
        assert!(!document.diagnostics().iter().any(|d| d.code == code));
    }
}
