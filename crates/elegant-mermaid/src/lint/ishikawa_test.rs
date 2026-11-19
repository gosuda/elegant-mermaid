#[test]
fn consumer_rules_trigger_and_nontrigger() {
    for (code, source, expected) in [
        ("ishikawa/no-causes", "ishikawa\nproblem\n", 1),
        ("ishikawa/no-causes", "ishikawa\nproblem\n  category\n", 0),
        (
            "ishikawa/empty-category",
            "ishikawa\nproblem\n  category\n",
            1,
        ),
        (
            "ishikawa/empty-category",
            "ishikawa\nproblem\n  category\n    cause\n",
            0,
        ),
        (
            "ishikawa/duplicate-sibling",
            "ishikawa\nproblem\n  category\n    cause\n    cause\n",
            1,
        ),
        (
            "ishikawa/duplicate-sibling",
            "ishikawa\nproblem\n  category\n    cause\n    other\n",
            0,
        ),
        (
            "ishikawa/deep-nesting",
            "ishikawa\nproblem\n  a\n    b\n      c\n        d\n          e\n            f\n",
            2,
        ),
        ("ishikawa/deep-nesting", "ishikawa\nproblem\n  a\n", 0),
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
