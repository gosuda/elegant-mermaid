use crate::diag::FixSafety;

#[test]
fn source_diagnostics_and_fixes() {
    let cases = [
        (
            "Dogs: 10",
            "pie/label-requires-quotes",
            FixSafety::Safe,
            "\"Dogs\": 10",
        ),
        (
            "\"Dogs\" 10",
            "pie/missing-colon",
            FixSafety::Safe,
            "\"Dogs\" : 10",
        ),
        ("\"Dogs\":", "pie/missing-number", FixSafety::Safe, ""),
        (
            "\"Dogs : 10",
            "pie/quote-unclosed",
            FixSafety::Unsafe,
            "\"Dogs\" : 10",
        ),
        (
            "\"He said \"Hi\"\": 1",
            "pie/label-double-in-double",
            FixSafety::Safe,
            "",
        ),
    ];
    for (input, code, safety, fixed) in cases {
        let source = format!("pie\n{input}\n");
        let parsed = super::parse(&source, &[]);
        assert_eq!(
            parsed.diagnostics.len(),
            1,
            "{code}: {:?}",
            parsed.diagnostics
        );
        let diagnostic = &parsed.diagnostics[0];
        assert_eq!(diagnostic.code, code);
        assert!(!diagnostic.help.is_empty());
        if fixed.is_empty() {
            assert!(diagnostic.fixes.is_empty());
            continue;
        }
        assert_eq!(diagnostic.fixes.len(), 1);
        assert_eq!(diagnostic.fixes[0].safety, safety);
        let edit = &diagnostic.fixes[0].edits[0];
        let result = format!(
            "{}{}{}",
            &source[..edit.span.start],
            edit.new_text,
            &source[edit.span.end..]
        );
        assert_eq!(result, format!("pie\n{fixed}\n"));
        assert!(super::parse(&result, &[]).diagnostics.is_empty());
    }
    for input in ["\"Dogs\": 10", "\"He said \\\"Hi\\\"\": 1"] {
        let source = format!("pie\n{input}\n");
        assert!(super::parse(&source, &[]).diagnostics.is_empty());
    }
}
