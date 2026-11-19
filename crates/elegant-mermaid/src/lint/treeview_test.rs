#[test]
fn consumer_rules_trigger_and_nontrigger() {
    for (code, source, expected) in [
        ("treeview/no-nodes", "treeView-beta\n", 1),
        ("treeview/no-nodes", "treeView-beta\na\n", 0),
        (
            "treeview/duplicate-sibling",
            "treeView-beta\na\na/ :::x\n",
            1,
        ),
        ("treeview/duplicate-sibling", "treeView-beta\na\nb\n", 0),
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
