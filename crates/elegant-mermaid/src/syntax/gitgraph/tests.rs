use super::ast::{Start, StatementKind};
use super::lexer::lengths;
use super::parse;
use crate::source::Span;

fn parsed(source: &str) -> (Start, Vec<String>) {
    let result = parse(source, &[]);
    let messages = result
        .diagnostics
        .iter()
        .map(|d| format!("{}: {}", d.code, d.message))
        .collect();
    (result.document, messages)
}

fn only(source: &str) -> Vec<String> {
    parsed(source).1
}

#[test]
fn header_forms() {
    for (source, header, direction) in [
        ("gitGraph\ncommit", "gitGraph", None),
        ("gitGraph:\ncommit", "gitGraph:", None),
        ("gitGraph :\ncommit", "gitGraph", None),
        ("gitGraph LR:\ncommit", "gitGraph", Some("LR")),
        ("gitGraph TB:\ncommit", "gitGraph", Some("TB")),
        ("gitGraph  BT :\ncommit", "gitGraph", Some("BT")),
    ] {
        let (start, messages) = parsed(source);
        assert!(messages.is_empty(), "{source}: {messages:?}");
        assert_eq!(start.header.kind, header, "{source}");
        assert_eq!(start.statements.len(), 1, "{source}");
        assert_eq!(
            start.direction.as_ref().map(|t| t.kind),
            direction,
            "{source}"
        );
    }
}

#[test]
fn direction_without_colon_is_rejected() {
    let result = parse("gitGraph LR\ncommit", &[]);
    assert_eq!(
        result
            .diagnostics
            .iter()
            .map(|d| d.message.as_str())
            .collect::<Vec<_>>(),
        vec!["unexpected \n, expected one of: :"]
    );
    assert_eq!(result.diagnostics[0].span, Span { start: 11, end: 12 });
}

#[test]
fn statement_forms() {
    let source = "gitGraph\n\
        commit id: \"a\" \"bare\" tag: \"t1\" tag: 't2' type: REVERSE\n\
        commit msg: \"m\"\n\
        branch feature/x-1.0 order: 3\n\
        checkout \"quoted name\"\n\
        switch main\n\
        merge dev id: \"m\" tag: \"v\" type: HIGHLIGHT\n\
        cherry-pick id: \"a\" parent: \"p\" tag: \"c\"\n";
    let (start, messages) = parsed(source);
    assert!(messages.is_empty(), "{messages:?}");
    assert_eq!(start.statements.len(), 7);
    let StatementKind::Commit(commit) = &start.statements[0].kind else {
        panic!("commit expected");
    };
    assert_eq!(commit.id.as_ref().map(|v| v.text.as_str()), Some("a"));
    assert_eq!(
        commit.message.as_ref().map(|v| v.text.as_str()),
        Some("bare")
    );
    assert_eq!(
        commit
            .tags
            .iter()
            .map(|v| v.text.as_str())
            .collect::<Vec<_>>(),
        vec!["t1", "t2"]
    );
    assert_eq!(
        commit.commit_type.as_ref().map(|v| v.text.as_str()),
        Some("REVERSE")
    );
    let StatementKind::Branch(branch) = &start.statements[2].kind else {
        panic!("branch expected");
    };
    assert_eq!(branch.name.text, "feature/x-1.0");
    assert_eq!(branch.order.as_ref().map(|o| o.value), Some(3));
    let StatementKind::Checkout(switch) = &start.statements[4].kind else {
        panic!("switch expected");
    };
    assert!(switch.switch);
    let StatementKind::Merge(merge) = &start.statements[5].kind else {
        panic!("merge expected");
    };
    assert_eq!(merge.branch.text, "dev");
    let StatementKind::CherryPicking(pick) = &start.statements[6].kind else {
        panic!("cherry-pick expected");
    };
    assert_eq!(pick.parent.as_ref().map(|v| v.text.as_str()), Some("p"));
}

#[test]
fn statement_spans_exclude_trailing_trivia() {
    let (start, messages) = parsed("gitGraph\ncommit id: \"a\"   %% note\nbranch x\n");
    assert!(messages.is_empty());
    assert_eq!(start.statements[0].span, Span { start: 9, end: 23 });
    assert_eq!(start.statements[1].span, Span { start: 34, end: 42 });
}

#[test]
fn repeated_scalars_keep_the_last_value() {
    let (start, messages) =
        parsed("gitGraph\ncommit id: \"a\" id: \"b\" type: NORMAL type: HIGHLIGHT\n");
    assert!(messages.is_empty());
    let StatementKind::Commit(commit) = &start.statements[0].kind else {
        panic!("commit expected");
    };
    assert_eq!(commit.id.as_ref().map(|v| v.text.as_str()), Some("b"));
    assert_eq!(
        commit.commit_type.as_ref().map(|v| v.text.as_str()),
        Some("HIGHLIGHT")
    );
}

#[test]
fn keywords_need_boundaries() {
    assert_eq!(
        only("gitGraph\ncommitted\ncommit-1 id: \"x\"\nbranch commit\n"),
        vec![
            "gitgraph/unknown-statement: unknown statement committed",
            "gitgraph/unknown-statement: unknown statement commit-1",
            "gitgraph/unexpected-token: unexpected commit, expected one of: REFERENCE, STRING",
        ]
    );
    assert!(only("gitGraph\nbranch \"commit\"\nbranch cherry-pick-2\n").is_empty());
}

#[test]
fn integer_token_follows_the_authority_pattern() {
    for (text, want) in [
        ("0", 1),
        ("7", 1),
        ("42", 2),
        ("1.5", 0),
        ("12.5", 1),
        ("007", 1),
        ("x", 0),
    ] {
        assert_eq!(lengths(text).0, want, "{text}");
    }
    assert_eq!(
        only("gitGraph\nbranch a order: 1.5\n"),
        vec!["gitgraph/unexpected-token: unexpected 1.5, expected one of: INT"]
    );
    assert_eq!(
        only("gitGraph\nbranch 123\n"),
        vec!["gitgraph/unexpected-token: unexpected 123, expected one of: REFERENCE, STRING"]
    );
}

#[test]
fn string_escapes() {
    let (start, messages) = parsed("gitGraph\ncommit id: \"a\\\"b\\nc\\\\d\\q\"\n");
    assert!(messages.is_empty());
    let StatementKind::Commit(commit) = &start.statements[0].kind else {
        panic!("commit expected");
    };
    assert_eq!(
        commit.id.as_ref().map(|v| v.text.as_str()),
        Some("a\"b\nc\\dq")
    );
}

#[test]
fn recovery_continues_after_a_rejected_statement() {
    let (start, messages) = parsed("gitGraph\ncommit id: foo\ncommit id: \"a\" extra\ncommit\n");
    assert_eq!(
        messages,
        vec![
            "gitgraph/unexpected-token: unexpected foo, expected one of: STRING",
            "gitgraph/unexpected-token: unexpected extra, expected one of: EOF, NEWLINE, STRING, id:, msg:, tag:, type:",
        ]
    );
    assert_eq!(start.statements.len(), 1);
}

#[test]
fn unknown_statement_spans_the_line() {
    let result = parse("gitGraph\nfoo bar \"baz\"\ncommit\n", &[]);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].message, "unknown statement foo");
    assert_eq!(result.diagnostics[0].span, Span { start: 9, end: 22 });
    assert_eq!(result.document.statements.len(), 1);
}

#[test]
fn unterminated_produces_only_the_opener_diagnostic() {
    for (source, start, end) in [
        ("gitGraph\ncommit id: \"abc", 20, 24),
        ("gitGraph\ncommit msg: 'abc\ncommit", 21, 32),
        ("gitGraph\naccDescr {\nnever", 18, 25),
    ] {
        let result = parse(source, &[]);
        assert_eq!(result.diagnostics.len(), 1, "{source}");
        assert_eq!(
            result.diagnostics[0].code, "gitgraph/unterminated",
            "{source}"
        );
        assert_eq!(result.diagnostics[0].span, Span { start, end }, "{source}");
    }
}

#[test]
fn metadata_values() {
    let source = "gitGraph\ntitle   My   diagram \naccTitle:  T\t\t t \naccDescr: d %% c\naccDescr {\n  one   two\n\n  three  \n}\ntitle\n";
    let (start, messages) = parsed(source);
    assert!(messages.is_empty());
    let got: Vec<String> = start
        .statements
        .iter()
        .map(|s| match &s.kind {
            StatementKind::Metadata(meta) => format!("{}={}", meta.field, meta.value),
            other => panic!("metadata expected, got {other:?}"),
        })
        .collect();
    assert_eq!(
        got,
        vec![
            "title=My diagram",
            "accTitle=T t",
            "accDescr=d",
            "accDescr=one two\nthree",
            "title="
        ]
    );
}

#[test]
fn comments_and_line_endings() {
    let (start, messages) =
        parsed("gitGraph\r\n%% only a comment\r\ncommit %% trailing\r\n\r\ncommit\rbranch x\n");
    assert!(messages.is_empty(), "{messages:?}");
    assert_eq!(start.statements.len(), 3);
}

#[test]
fn removed_spans_are_skipped() {
    let source = "---\ntitle: x\n---\ngitGraph\ncommit\n";
    let result = parse(source, &[Span { start: 0, end: 17 }]);
    assert!(result.diagnostics.is_empty());
    assert_eq!(result.document.header.kind, "gitGraph");
    assert_eq!(result.document.statements.len(), 1);
}
