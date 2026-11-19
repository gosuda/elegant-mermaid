use super::preprocess;
use crate::source::Span;

fn removed(src: &str) -> Vec<Span> {
    preprocess(src).removed
}

#[test]
fn comment_line_absorbs_blank_lines_before_it() {
    let src = "flowchart TD\nA-->B\n\n  \n  %% c\nC-->D\n";
    assert_eq!(removed(src), [Span { start: 19, end: 30 }]);
}

#[test]
fn blank_lines_without_a_comment_are_kept() {
    let src = "flowchart TD\nA-->B\n\n  \nC-->D\n";
    assert!(removed(src).is_empty());
}

#[test]
fn adjacent_comment_lines_share_one_removed_span() {
    let src = "flowchart TD\n%% a\n%% b\nA\n";
    assert_eq!(removed(src), [Span { start: 13, end: 23 }]);
}

#[test]
fn comment_line_absorbs_directive_lines_among_blank_lines() {
    let src = "flowchart TD\n%%{x: 1}%%\n\n%%{y: 2}%%\n%% c\nA-->B\n";
    assert_eq!(removed(src), [Span { start: 13, end: 41 }]);
}

#[test]
fn bare_percent_comment_boundaries() {
    for ending in ["", "\n", "\r\n", "\r"] {
        for comment in ["%%", " \t%%", "%% text", "%% {not a directive}"] {
            let src = format!("info\n{comment}{ending}");
            assert_eq!(
                removed(&src),
                [Span {
                    start: 5,
                    end: src.len()
                }],
                "{src:?}"
            );
        }
    }
}

#[test]
fn percent_inside_statement_is_label_content() {
    for line in [
        r#"A["%%"]"#,
        r#"A["text %% label"]"#,
        "A --> B %% trailing",
        "%",
        " \t%",
    ] {
        let src = format!("flowchart TD\n{line}\r\n");
        assert!(removed(&src).is_empty(), "{src:?}");
    }
}

#[test]
fn percent_directive_takes_precedence_over_comment() {
    for ending in ["", "\n", "\r\n", "\r"] {
        let src = format!("%%{{wrap}}%%{ending}info");
        let got = preprocess(&src);
        assert!(got.wrap);
        assert_eq!(got.removed, [Span { start: 0, end: 10 }]);
    }
}
