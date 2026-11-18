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
fn duplicate_sibling_trigger_and_non_trigger() {
    let row = &row("mindmap/duplicate-sibling");
    for (source, expected) in [
        ("mindmap\n  root\n    same\n    same\n", 1),
        ("mindmap\n  root\n    same\n    other\n", 0),
    ] {
        let parsed = crate::syntax::mindmap::parse(source, &[]);
        let (model, _) = crate::model::mindmap::resolve(source, &parsed.document);
        let got = super::duplicate_sibling(&model, row);
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
fn no_nodes_trigger_and_non_trigger() {
    let row = &row("mindmap/no-nodes");
    for (source, expected) in [("mindmap\n", 1), ("mindmap\n  root\n", 0)] {
        let parsed = crate::syntax::mindmap::parse(source, &[]);
        let (model, _) = crate::model::mindmap::resolve(source, &parsed.document);
        let got = super::no_nodes(&model, row);
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
fn deep_nesting_trigger_and_non_trigger() {
    let row = &row("mindmap/deep-nesting");
    for (source, expected) in [
        (
            "mindmap\n  root\n    a\n      b\n        c\n          d\n            e\n              f\n",
            2,
        ),
        ("mindmap\n  root\n    a\n", 0),
    ] {
        let parsed = crate::syntax::mindmap::parse(source, &[]);
        let (model, _) = crate::model::mindmap::resolve(source, &parsed.document);
        let got = super::deep_nesting(&model, row);
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
