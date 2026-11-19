fn row(code: &'static str) -> crate::r#gen::lintrules::LintRule {
    crate::r#gen::lintrules::LintRule {
        code,
        severity: "warning",
        summary: "rule message",
        help: "rule help",
        rationale: "",
        fix_safety: "none",
        aliases: &[],
        source: "own",
        status: "adopted",
        reason: "",
    }
}

#[test]
fn duplicate_commit_warning_is_resolver_owned_and_suppressible() {
    let code = "gitgraph/duplicate-commit-id";
    for (source, expected) in [
        ("gitGraph\ncommit id: \"a\"\ncommit id: \"a\"\n", 1),
        ("gitGraph\ncommit id: \"a\"\ncommit id: \"b\"\n", 0),
    ] {
        let document = crate::parse(source);
        assert!(!document.has_errors(), "{:?}", document.diagnostics());
        let warnings: Vec<_> = document
            .diagnostics()
            .iter()
            .filter(|diagnostic| diagnostic.code == code)
            .collect();
        assert_eq!(warnings.len(), expected);
        for warning in warnings {
            assert_eq!(warning.severity, crate::Severity::Warning);
            assert_eq!(warning.message, "commit id a already exists");
        }
        let lint = crate::lint(&document, &crate::LintConfig::default());
        assert!(!lint.iter().any(|diagnostic| diagnostic.code == code));
        let diagnostics = crate::lint_document(&document, &crate::LintConfig::default());
        assert_eq!(
            diagnostics
                .iter()
                .filter(|diagnostic| diagnostic.code == code)
                .count(),
            expected
        );
        let off = crate::lint_document(
            &document,
            &crate::LintConfig {
                off: vec![code.into()],
                ..Default::default()
            },
        );
        assert_eq!(
            off.iter()
                .filter(|diagnostic| diagnostic.code == code)
                .count(),
            expected
        );
    }
    let suppressed = crate::parse(
        "gitGraph\n%% emd-disable-diagram gitgraph/duplicate-commit-id: test\ncommit id: \"a\"\ncommit id: \"a\"\n",
    );
    assert!(!suppressed.has_errors());
    assert!(
        !crate::lint_document(&suppressed, &crate::LintConfig::default())
            .iter()
            .any(|diagnostic| diagnostic.code == code)
    );
}

#[test]
fn duplicate_tag_trigger_and_non_trigger() {
    let row = &row("gitgraph/duplicate-tag");
    for (source, expected) in [
        ("gitGraph\ncommit tag: \"v1\"\ncommit tag: \"v1\"\n", 1),
        ("gitGraph\ncommit tag: \"v1\"\ncommit tag: \"v2\"\n", 0),
    ] {
        let parsed = crate::syntax::gitgraph::parse(source, &[]);
        let (model, _) = crate::model::gitgraph::resolve(source, &parsed.document);
        let got = super::duplicate_tag(&model, row);
        assert_eq!(got.len(), expected, "{source}");
        for diagnostic in got {
            assert_eq!(diagnostic.code, row.code);
            assert_eq!(diagnostic.message, row.summary);
            assert_eq!(diagnostic.help, row.help);
            assert!(
                diagnostic.span.start <= diagnostic.span.end && diagnostic.span.end <= source.len()
            );
        }
    }
}

#[test]
fn no_commits_trigger_and_non_trigger() {
    let row = &row("gitgraph/no-commits");
    for (source, expected) in [("gitGraph\n", 1), ("gitGraph\ncommit\n", 0)] {
        let parsed = crate::syntax::gitgraph::parse(source, &[]);
        let (model, _) = crate::model::gitgraph::resolve(source, &parsed.document);
        let got = super::no_commits(&model, row);
        assert_eq!(got.len(), expected, "{source}");
        for diagnostic in got {
            assert_eq!(diagnostic.code, row.code);
            assert_eq!(diagnostic.message, row.summary);
            assert_eq!(diagnostic.help, row.help);
            assert!(
                diagnostic.span.start <= diagnostic.span.end && diagnostic.span.end <= source.len()
            );
        }
    }
}
