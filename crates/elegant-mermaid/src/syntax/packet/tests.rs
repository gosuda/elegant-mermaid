use super::ast::{Metadata, PacketBlock, Start, StatementKind};
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

fn block(start: &Start, index: usize) -> &PacketBlock {
    let StatementKind::PacketBlock(block) = &start.statements[index].kind else {
        panic!("packet block expected at {index}");
    };
    block
}

#[test]
fn header_forms() {
    for (source, header) in [
        ("packet\n0: \"a\"", "packet"),
        ("packet-beta\n0: \"a\"", "packet-beta"),
        ("\n\npacket %% comment\n0: \"a\"", "packet"),
        ("packet 0: \"a\"", "packet"),
    ] {
        let (start, messages) = parsed(source);
        assert!(messages.is_empty(), "{source}: {messages:?}");
        assert_eq!(start.header.kind, header, "{source}");
        assert_eq!(start.statements.len(), 1, "{source}");
    }
}

#[test]
fn block_forms() {
    let (start, messages) =
        parsed("packet\n0-15: \"range\"\n16: 'single'\n+8: \"relative\"\n 24 - 31 : \"spaced\"\n");
    assert!(messages.is_empty(), "{messages:?}");
    assert_eq!(start.statements.len(), 4);
    let first = block(&start, 0);
    assert_eq!(first.start.map(|o| o.value), Some(0));
    assert_eq!(first.end.map(|o| o.value), Some(15));
    assert!(first.bits.is_none());
    assert_eq!(first.label.text, "range");
    assert_eq!(start.statements[0].span, Span { start: 7, end: 20 });
    let single = block(&start, 1);
    assert_eq!(single.start.map(|o| o.value), Some(16));
    assert!(single.end.is_none());
    let relative = block(&start, 2);
    assert!(relative.start.is_none());
    assert_eq!(relative.bits.map(|o| o.value), Some(8));
    assert_eq!(start.statements[2].span, Span { start: 34, end: 48 });
    let spaced = block(&start, 3);
    assert_eq!(spaced.start.map(|o| o.value), Some(24));
    assert_eq!(spaced.end.map(|o| o.value), Some(31));
}

#[test]
fn metadata_statements() {
    let (start, messages) = parsed(
        "packet\ntitle  Hi   there %% c\naccTitle: T  U\naccDescr: d\naccDescr {\n a  b\n\n c\n}\n  title x\ntitle\n0: \"x\"",
    );
    assert!(messages.is_empty(), "{messages:?}");
    let got: Vec<(&str, &str)> = start
        .statements
        .iter()
        .filter_map(|s| match &s.kind {
            StatementKind::Metadata(Metadata { field, value }) => Some((*field, value.as_str())),
            StatementKind::PacketBlock(_) => None,
        })
        .collect();
    assert_eq!(
        got,
        vec![
            ("title", "Hi there"),
            ("accTitle", "T U"),
            ("accDescr", "d"),
            ("accDescr", "a b\nc"),
            ("title", "x"),
            ("title", ""),
        ]
    );
}

#[test]
fn string_conversion() {
    let (start, messages) =
        parsed("packet\n0-3: \"a\\nb\\qc\\\\d\\0e\\\"f\"\n4: 'it\\'s'\n5: \"x\ny\"");
    assert!(messages.is_empty(), "{messages:?}");
    assert_eq!(block(&start, 0).label.text, "a\nbqc\\d\0e\"f");
    assert_eq!(block(&start, 1).label.text, "it's");
    assert_eq!(block(&start, 2).label.text, "x\ny");
}

#[test]
fn integer_rules() {
    assert_eq!(lengths("01"), 1);
    assert_eq!(lengths("12.5"), 1);
    assert_eq!(lengths("12"), 2);
    assert_eq!(lengths("a"), 0);
    assert_eq!(
        parsed("packet\n01-3: \"a\"").1,
        vec!["packet/unexpected-token: unexpected 1, expected one of: -, :"]
    );
    assert_eq!(
        parsed("packet\n0.5: \"a\"").1,
        vec!["packet/unexpected-token: unexpected ., expected one of: -, :"]
    );
    let (start, messages) = parsed("packet\n99999999999999999999: \"a\"");
    assert!(messages.is_empty());
    assert_eq!(block(&start, 0).start.map(|o| o.value), Some(2_147_483_647));
}

#[test]
fn unexpected_tokens() {
    for (source, want) in [
        (
            "packet\n0-3 \"x\"",
            "packet/unexpected-token: unexpected \"x\", expected one of: :",
        ),
        (
            "packet\n0 \"x\"",
            "packet/unexpected-token: unexpected \"x\", expected one of: -, :",
        ),
        (
            "packet\n0-: \"x\"",
            "packet/unexpected-token: unexpected :, expected one of: INT",
        ),
        (
            "packet\n+: \"x\"",
            "packet/unexpected-token: unexpected :, expected one of: INT",
        ),
        (
            "packet\n0-3: 4",
            "packet/unexpected-token: unexpected 4, expected one of: STRING",
        ),
        (
            "packet\n0-3: \"a\" 4-7: \"b\"",
            "packet/unexpected-token: unexpected 4, expected one of: EOF, NEWLINE",
        ),
        (
            "packet\n0-3: \"a\"title",
            "packet/unexpected-token: unexpected title, expected one of: EOF, NEWLINE",
        ),
    ] {
        assert_eq!(parsed(source).1, vec![want], "{source}");
    }
    let (start, messages) = parsed("packet\ntitle x 0: \"a\"\n");
    assert!(messages.is_empty());
    assert_eq!(start.statements.len(), 1);
}

#[test]
fn unknown_statements() {
    let result = parse("packet\nfoo bar\n-3: \"x\"\n0: \"ok\"", &[]);
    let messages: Vec<String> = result
        .diagnostics
        .iter()
        .map(|d| format!("{}: {}", d.code, d.message))
        .collect();
    assert_eq!(
        messages,
        vec![
            "packet/unknown-statement: unknown statement f",
            "packet/unknown-statement: unknown statement -",
        ]
    );
    assert_eq!(result.diagnostics[0].span, Span { start: 7, end: 14 });
    assert_eq!(result.diagnostics[1].span, Span { start: 15, end: 22 });
    assert_eq!(result.document.statements.len(), 1);
}

#[test]
fn unterminated_constructs() {
    for (source, span, text) in [
        (
            "packet\n0: \"never",
            Span { start: 10, end: 16 },
            "unterminated \"",
        ),
        (
            "packet\n0: 'never\n1: 'x'",
            Span { start: 22, end: 23 },
            "unterminated '",
        ),
        (
            "packet\naccDescr {\n a",
            Span { start: 16, end: 20 },
            "unterminated {",
        ),
        (
            "packet\n0-3: \"a\\",
            Span { start: 12, end: 15 },
            "unterminated \"",
        ),
    ] {
        let result = parse(source, &[]);
        let last = result.diagnostics.last().expect(source);
        assert_eq!(last.code, "packet/unterminated", "{source}");
        assert_eq!(last.span, span, "{source}");
        assert_eq!(last.message, text, "{source}");
    }
}

#[test]
fn backslash_before_line_end_is_not_a_string() {
    let result = parse("packet\n0-3: \"a\\\nb\"", &[]);
    assert_eq!(result.diagnostics[0].code, "packet/unexpected-token");
}

#[test]
fn removed_spans_are_skipped() {
    let source = "---\ntitle: x\n---\npacket\n0: \"a\"";
    let result = parse(source, &[Span { start: 0, end: 17 }]);
    assert!(result.diagnostics.is_empty());
    assert_eq!(result.document.statements.len(), 1);
}

#[test]
fn lone_carriage_return_ends_lines() {
    let (start, messages) = parsed("packet\r0: \"a\"\r\n1: \"b\"");
    assert!(messages.is_empty(), "{messages:?}");
    assert_eq!(start.statements.len(), 2);
}
