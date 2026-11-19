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
fn no_activate_without_deactivate_trigger_and_non_trigger() {
    let row = &row("sequence/no-activate-without-deactivate");
    for (source, expected) in [
        ("sequenceDiagram\nparticipant A\nactivate A\n", 1),
        (
            "sequenceDiagram\nparticipant A\nactivate A\ndeactivate A\n",
            0,
        ),
    ] {
        let parsed = crate::syntax::sequence::parse(source, &[]);
        let (model, _) = crate::model::sequence::resolve(source, &parsed.document);
        let got = super::no_activate_without_deactivate(&model, row);
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
fn prefer_explicit_participants_trigger_and_non_trigger() {
    let row = &row("sequence/prefer-explicit-participants");
    for (source, expected) in [
        ("sequenceDiagram\nA->>B: hi\n", 2),
        (
            "sequenceDiagram\nparticipant A\nparticipant B\nA->>B: hi\n",
            0,
        ),
    ] {
        let parsed = crate::syntax::sequence::parse(source, &[]);
        let (model, _) = crate::model::sequence::resolve(source, &parsed.document);
        let got = super::prefer_explicit_participants(&model, row);
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
fn duplicate_participant_trigger_and_non_trigger() {
    let row = &row("sequence/duplicate-participant");
    for (source, expected) in [
        ("sequenceDiagram\nparticipant A\nparticipant A\n", 1),
        ("sequenceDiagram\nparticipant A\n", 0),
    ] {
        let parsed = crate::syntax::sequence::parse(source, &[]);
        let (model, _) = crate::model::sequence::resolve(source, &parsed.document);
        let got = super::duplicate_participant(&model, row);
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
