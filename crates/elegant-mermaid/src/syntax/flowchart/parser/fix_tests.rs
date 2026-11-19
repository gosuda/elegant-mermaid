use super::*;
#[cfg(test)]
mod fix_contract_tests {
    use super::*;

    #[test]
    fn flowchart_diagnostic_fix_contracts() {
        let safe = FixSafety::Safe;
        let unsafe_fix = FixSafety::Unsafe;
        for (code, src, start, end, title, safety, edit_start, edit_end, text) in [
            (
                "flowchart/arrow-invalid",
                "A -> B",
                2,
                4,
                "Replace -> with -->",
                safe,
                2,
                4,
                "-->",
            ),
            (
                "flowchart/link-missing",
                "A B",
                2,
                3,
                "Insert --> between the two nodes",
                unsafe_fix,
                2,
                2,
                "--> ",
            ),
            (
                "flowchart/end-without-subgraph",
                " end\n",
                1,
                4,
                "Remove the stray end line",
                unsafe_fix,
                0,
                5,
                "",
            ),
            (
                "flowchart/meta-unsupported",
                " title foo\n",
                1,
                10,
                "Remove the unsupported meta line",
                unsafe_fix,
                0,
                11,
                "",
            ),
            (
                "flowchart/unclosed-node-bracket",
                "A[foo",
                1,
                5,
                "Add the closing bracket",
                unsafe_fix,
                5,
                5,
                "]",
            ),
            (
                "flowchart/node-mixed-brackets",
                "A(foo]",
                5,
                6,
                "Close with the matching bracket",
                safe,
                5,
                6,
                ")",
            ),
            (
                "flowchart/node-empty",
                "A[]",
                1,
                2,
                "Remove the empty bracket pair",
                safe,
                1,
                3,
                "",
            ),
            (
                "flowchart/label-escaped-quote",
                "A[\"x\\\"y\"]",
                4,
                6,
                "Replace the quote with &quot;",
                safe,
                4,
                6,
                "&quot;",
            ),
            (
                "flowchart/label-double-in-single",
                "A[x\"y]",
                3,
                4,
                "Replace the quote with &quot;",
                safe,
                3,
                4,
                "&quot;",
            ),
            (
                "flowchart/label-backtick",
                "A[x`y]",
                3,
                4,
                "Remove the backtick",
                safe,
                3,
                4,
                "",
            ),
            (
                "flowchart/dir-kw-invalid",
                "graph directionx LR",
                6,
                16,
                "Replace the keyword with direction",
                safe,
                6,
                16,
                "direction",
            ),
            (
                "flowchart/dir-missing",
                "graph",
                0,
                5,
                "Insert the default direction TD",
                safe,
                5,
                5,
                " TD",
            ),
            (
                "flowchart/link-unsupported-marker",
                "A --x--> B",
                2,
                8,
                "Remove the unsupported one-sided marker",
                unsafe_fix,
                2,
                8,
                "---->",
            ),
            (
                "flowchart/quote-unclosed",
                "A[\"foo]",
                2,
                7,
                "Insert the closing quote",
                unsafe_fix,
                6,
                6,
                "\"",
            ),
            (
                "flowchart/label-quote-in-unquoted",
                "A[foo\"bar\"]",
                5,
                6,
                "Wrap the label in quotes",
                safe,
                2,
                10,
                "\"foo&quot;bar&quot;\"",
            ),
        ] {
            let mut diagnostic = crate::syntax::flowchart::diagnostic(
                code,
                Severity::Error,
                String::new(),
                Span { start, end },
            );
            attach_fixes(src, std::slice::from_mut(&mut diagnostic));
            assert_eq!(diagnostic.fixes.len(), 1, "{code}");
            let fix = &diagnostic.fixes[0];
            assert_eq!((fix.title.as_str(), fix.safety), (title, safety), "{code}");
            assert_eq!(fix.edits.len(), 1, "{code}");
            assert_eq!(
                fix.edits[0].span,
                Span {
                    start: edit_start,
                    end: edit_end
                },
                "{code}"
            );
            assert_eq!(fix.edits[0].new_text, text, "{code}");
        }
    }
}
