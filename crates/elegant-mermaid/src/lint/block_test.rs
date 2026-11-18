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
fn no_blocks_trigger_and_non_trigger() {
    let row = &row("block/no-blocks");
    for (source, expected) in [("block-beta\n", 1), ("block-beta\nA[\"alpha\"]\n", 0)] {
        let parsed = crate::syntax::block::parse(source, &[]);
        let (model, _) = crate::model::block::resolve(source, &parsed.document);
        let got = super::no_blocks(&model, row);
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
