use crate::diag::Diagnostic;
use crate::source::Span;

use super::ast::{Start, StatementKind};
use super::parse;

fn run(source: &str) -> (Start, Vec<Diagnostic>) {
    let parsed = parse(source, &[]);
    (parsed.document, parsed.diagnostics)
}

fn messages(diagnostics: &[Diagnostic]) -> Vec<String> {
    diagnostics
        .iter()
        .map(|d| format!("{}: {}", d.code, d.message))
        .collect()
}

fn statements(start: &Start) -> Vec<String> {
    let mut out = Vec::new();
    for line in &start.document.lines {
        let Some(statement) = &line.statement else {
            continue;
        };
        out.push(match &statement.kind {
            StatementKind::Title(node) => format!("title={}", node.token.value),
            StatementKind::Section(node) => format!("section={}", node.token.value),
            StatementKind::Period(node) => format!("period={}", node.token.value),
            StatementKind::Event(node) => format!("event={}", node.token.value),
            StatementKind::AccTitle(node) => format!("accTitle={}", node.value.value),
            StatementKind::AccDescr(node) => format!("accDescr={}", node.value.value),
            StatementKind::AccDescrBlock(node) => format!("block={}", node.value.value),
        });
    }
    out
}

fn statement_spans(start: &Start) -> Vec<Span> {
    start
        .document
        .lines
        .iter()
        .filter_map(|line| line.statement.as_ref().map(|statement| statement.span))
        .collect()
}

fn body(source: &str) -> Vec<String> {
    let (start, diagnostics) = run(source);
    assert!(diagnostics.is_empty(), "{source:?}: {diagnostics:?}");
    statements(&start)
}

fn strings(items: &[&str]) -> Vec<String> {
    items.iter().map(|item| (*item).to_owned()).collect()
}

#[test]
fn header_forms() {
    for (source, direction, header) in [
        ("timeline\n", "", "timeline"),
        ("timeline LR\n", "LR", "timeline LR"),
        ("timeline TD\n", "TD", "timeline TD"),
        ("TIMELINE \t td\n", "TD", "TIMELINE \t td"),
        ("timeline   lr", "LR", "timeline   lr"),
    ] {
        let (start, diagnostics) = run(source);
        assert!(diagnostics.is_empty(), "{source:?}");
        assert_eq!(start.header.direction, direction, "{source:?}");
        assert_eq!(start.header.token.text, header, "{source:?}");
    }
}

#[test]
fn direction_needs_a_word_boundary() {
    let (start, diagnostics) = run("timeline LRx");
    assert!(diagnostics.is_empty());
    assert_eq!(start.header.direction, "");
    assert_eq!(statements(&start), strings(&["period=LRx"]));
    let (start, diagnostics) = run("timeline TDé");
    assert!(diagnostics.is_empty());
    assert_eq!(start.header.direction, "TD");
    assert_eq!(statements(&start), strings(&["period=é"]));
}

#[test]
fn header_without_boundary_is_rejected() {
    let (_, diagnostics) = run("timelinex\n");
    assert_eq!(
        messages(&diagnostics),
        strings(&[
            "timeline/unexpected-token: unexpected timelinex, expected one of: timeline, timeline_lr, timeline_td"
        ])
    );
    assert_eq!(diagnostics[0].span, Span { start: 0, end: 9 });
    let (_, diagnostics) = run("");
    assert_eq!(
        messages(&diagnostics),
        strings(&[
            "timeline/unexpected-token: unexpected end of input, expected one of: timeline, timeline_lr, timeline_td"
        ])
    );
}

#[test]
fn statement_forms() {
    assert_eq!(
        body(
            "timeline TD\n  title  History of X\n  accTitle: A title \n  accDescr: A description\n  accDescr {\n   multi\n   line\n  }\n  section Early Era\n  2002 : LinkedIn\n       : Second event\n  Plain period\n"
        ),
        strings(&[
            "title= History of X",
            "accTitle=A title ",
            "accDescr=A description",
            "block=multi\n   line\n  ",
            "section=Early Era",
            "period=2002 ",
            "event=LinkedIn",
            "event=Second event",
            "period=Plain period",
        ])
    );
}

#[test]
fn colon_rules() {
    assert_eq!(
        body("timeline\na : b : c"),
        strings(&["period=a ", "event=b ", "event=c"])
    );
    assert_eq!(
        body("timeline\na : http://x.y/z?q=1"),
        strings(&["period=a ", "event=http://x.y/z?q=1"])
    );
    assert_eq!(
        body("timeline\na : b :c"),
        strings(&["period=a ", "event=b :c"])
    );
    assert_eq!(
        body("timeline\na:\n  x"),
        strings(&["period=a", "event=  x"])
    );
    assert_eq!(
        body("timeline\na: ;x;"),
        strings(&["period=a", "event=;x;"])
    );
}

#[test]
fn hash_and_comment_rules() {
    assert_eq!(
        body("timeline\na # comment\n: #35; b"),
        strings(&["period=a ", "event=#35; b"])
    );
    assert_eq!(body("timeline\na #35; b"), strings(&["period=a #35; b"]));
    assert_eq!(
        body("timeline\n# only a comment\na\n%% another\n"),
        strings(&["period=a"])
    );
    assert_eq!(body("timeline\na b %% c"), strings(&["period=a b %% c"]));
}

#[test]
fn keywords_need_their_whitespace_and_payload() {
    assert_eq!(body("timeline\ntitle"), strings(&["period=title"]));
    assert_eq!(
        body("timeline\ntitle \n x"),
        strings(&["period=title ", "period=x"])
    );
    assert_eq!(body("timeline\nsection"), strings(&["period=section"]));
    assert_eq!(body("timeline\ntitles x"), strings(&["period=titles x"]));
    assert_eq!(
        body("timeline\nsection a : b"),
        strings(&["section=a ", "event=b"])
    );
    assert_eq!(
        body("timeline\ntitle\n  next line"),
        strings(&["title=  next line"])
    );
}

#[test]
fn keywords_fold_ascii_only() {
    assert_eq!(
        body("timeline\nTITLE x\nSeCtIoN y\nACCTITLE: z"),
        strings(&["title=x", "section=y", "accTitle=z"])
    );
}

#[test]
fn accessibility_blocks() {
    let source = "timeline\naccDescr {a}\naccDescr {  }\naccDescr{\n}\n";
    let (start, diagnostics) = run(source);
    assert!(diagnostics.is_empty());
    assert_eq!(statements(&start), strings(&["block=a"]));
    let statement = start.document.lines[1].statement.as_ref().unwrap();
    assert_eq!(statement.span, Span { start: 9, end: 21 });
    let StatementKind::AccDescrBlock(node) = &statement.kind else {
        panic!("not a block");
    };
    assert_eq!(node.value.open, Span { start: 9, end: 19 });
    assert_eq!(node.value.payload, Span { start: 19, end: 20 });
    assert_eq!(node.value.close, Span { start: 20, end: 21 });
}

#[test]
fn unterminated_block_spans_to_the_end() {
    let source = "timeline\n2002 : a\naccDescr {\nnever closed\n";
    let (start, diagnostics) = run(source);
    assert_eq!(
        messages(&diagnostics),
        strings(&["timeline/unterminated: unterminated {"])
    );
    assert_eq!(
        diagnostics[0].span,
        Span {
            start: 27,
            end: source.len()
        }
    );
    assert_eq!(statements(&start), strings(&["period=2002 ", "event=a"]));
}

#[test]
fn empty_accessibility_value_at_the_end_is_rejected() {
    for source in [
        "timeline\naccTitle:",
        "timeline\naccDescr:\n",
        "timeline\naccTitle:\n  \n",
    ] {
        let (_, diagnostics) = run(source);
        assert_eq!(diagnostics.len(), 1, "{source:?}");
        assert!(
            diagnostics[0]
                .message
                .contains("unexpected end of input, expected one of: acc_"),
            "{source:?}"
        );
        assert_eq!(diagnostics[0].span.start, source.len(), "{source:?}");
    }
}

#[test]
fn accessibility_opener_swallows_following_whitespace() {
    assert_eq!(
        body("timeline\naccTitle:\n\n   next\n"),
        strings(&["accTitle=next"])
    );
}

#[test]
fn invalid_colon_starts_an_unknown_statement_that_ends_with_its_line() {
    let source = "timeline\n: \nfoo\n#c\n:";
    let (start, diagnostics) = run(source);
    assert_eq!(
        messages(&diagnostics),
        strings(&[
            "timeline/unknown-statement: unknown statement :",
            "timeline/unknown-statement: unknown statement :"
        ])
    );
    assert_eq!(diagnostics[0].span, Span { start: 9, end: 10 });
    assert_eq!(diagnostics[1].span, Span { start: 19, end: 20 });
    assert_eq!(statements(&start), strings(&["period=foo"]));
}

#[test]
fn stray_header_token_skips_the_rest_of_its_line() {
    let source = "timeline\ntimeline foo : bar\nbaz";
    let (start, diagnostics) = run(source);
    assert_eq!(
        messages(&diagnostics),
        strings(&["timeline/unknown-statement: unknown statement timeline"])
    );
    assert_eq!(diagnostics[0].span, Span { start: 9, end: 27 });
    assert_eq!(statements(&start), strings(&["period=baz"]));
}

#[test]
fn removed_spans_are_skipped_and_spans_stay_in_host_coordinates() {
    let front = "---\na: b\n---\n";
    let directive = "%%{init}%%";
    let source = format!("{front}timeline\ntitle X {directive} Y\n2002 : e\n");
    let at = source.find(directive).unwrap();
    let removed = [
        Span {
            start: 0,
            end: front.len(),
        },
        Span {
            start: at,
            end: at + directive.len(),
        },
    ];
    let parsed = parse(&source, &removed);
    assert!(parsed.diagnostics.is_empty());
    let start = parsed.document;
    assert_eq!(
        start.header.token.span,
        Span {
            start: front.len(),
            end: front.len() + "timeline".len()
        }
    );
    let StatementKind::Title(title) = &start.document.lines[1].statement.as_ref().unwrap().kind
    else {
        panic!("not a title");
    };
    assert_eq!(title.token.value, "X  Y");
    assert_eq!(
        title.token.span,
        Span {
            start: source.find("title").unwrap(),
            end: at + directive.len() + " Y".len()
        }
    );
}

#[test]
fn line_endings_normalise_and_spans_keep_the_host_bytes() {
    let source = "timeline\r\n2002 : a\r\n: b\rc\r\n";
    let (start, diagnostics) = run(source);
    assert!(diagnostics.is_empty());
    assert_eq!(
        statements(&start),
        strings(&["period=2002 ", "event=a", "event=b", "period=c"])
    );
    assert_eq!(
        statement_spans(&start),
        vec![
            Span { start: 10, end: 15 },
            Span { start: 15, end: 18 },
            Span { start: 20, end: 23 },
            Span { start: 24, end: 25 },
        ]
    );
}

#[test]
fn document_spans_cover_header_through_last_line() {
    let source = "timeline\na\n";
    let (start, _) = run(source);
    assert_eq!(
        start.span,
        Span {
            start: 0,
            end: source.len()
        }
    );
    let (empty, _) = run("timeline");
    assert_eq!(empty.span, Span { start: 0, end: 8 });
    assert_eq!(empty.document.span, Span { start: 8, end: 8 });
}

#[test]
fn spans_never_split_multibyte_text() {
    let source = "timeline\ntitle é€𝄞\n日本 : 語\n\u{a0}x : \u{3000}y";
    let (start, _) = run(source);
    for line in &start.document.lines {
        assert!(source.is_char_boundary(line.span.start));
        assert!(source.is_char_boundary(line.span.end));
    }
}
