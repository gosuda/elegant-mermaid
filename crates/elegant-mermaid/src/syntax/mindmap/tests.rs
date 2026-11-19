use super::ast::{Description, Node, Start, Token};
use super::lexer::{K_END, Scanner};
use super::parse;
use crate::diag::Diagnostic;
use crate::source::Span;

fn kinds(src: &str) -> Vec<&'static str> {
    let mut scanner = Scanner::new(src, &[]);
    let mut out = Vec::new();
    loop {
        let token = scanner.next();
        out.push(token.kind);
        if token.kind == K_END {
            return out;
        }
    }
}

fn parsed(src: &str) -> (Start, Vec<Diagnostic>) {
    let parsed = parse(src, &[]);
    (parsed.document, parsed.diagnostics)
}

fn codes(ds: &[Diagnostic]) -> Vec<&'static str> {
    ds.iter().map(|d| d.code).collect()
}

fn messages(ds: &[Diagnostic]) -> Vec<&str> {
    ds.iter().map(|d| d.message.as_str()).collect()
}

fn first_node(start: &Start) -> Option<&Node> {
    start
        .document
        .items
        .iter()
        .find_map(|item| item.statement.node.as_ref())
}

fn text(src: &str, span: Span) -> &str {
    src.get(span.start..span.end).unwrap_or("")
}

fn descr_text(node: Option<&Node>) -> &str {
    node.and_then(|n| n.descr.as_ref()).map_or("", |t| &t.text)
}

#[test]
fn lexer_appends_virtual_newline_and_splits_lines() {
    assert_eq!(
        kinds("mindmap\n  root"),
        ["MINDMAP", "NL", "SPACELIST", "NODE_ID", "NL", "EOF", "END"]
    );
    assert_eq!(kinds("mindmap\n"), ["MINDMAP", "SPACELINE", "EOF", "END"]);
    assert_eq!(
        kinds("mindmap  \n  root"),
        [
            "MINDMAP",
            "SPACELINE",
            "SPACELIST",
            "NODE_ID",
            "NL",
            "EOF",
            "END"
        ]
    );
}

#[test]
fn lexer_folds_header_and_stops_at_word_boundary() {
    assert_eq!(kinds("MindMap\n").first(), Some(&"MINDMAP"));
    assert_eq!(kinds("mindmapper"), ["NODE_ID", "NL", "EOF", "END"]);
    assert_eq!(
        kinds("mindmap-x"),
        ["MINDMAP", "NODE_ID", "NL", "EOF", "END"]
    );
}

#[test]
fn lexer_shape_openers_follow_source_order() {
    for (opener, closer) in [
        ("-)", ")"),
        ("(-", ")"),
        ("))", ")"),
        (")", ")"),
        ("((", "))"),
        ("{{", "}}"),
        ("(", ")"),
        ("[", "]"),
    ] {
        assert_eq!(
            kinds(&format!("a{opener}b{closer}")),
            [
                "NODE_ID",
                "NODE_DSTART",
                "NODE_DESCR",
                "NODE_DEND",
                "NL",
                "EOF",
                "END"
            ],
            "{opener}"
        );
    }
    assert_eq!(
        kinds("((b))"),
        ["NODE_DSTART", "NODE_DESCR", "NODE_DEND", "NL", "EOF", "END"]
    );
}

#[test]
fn lexer_node_mode_keeps_permissive_descriptions() {
    let (start, ds) = parsed("mindmap\n  a[b\"c(d]\n");
    assert_eq!(
        messages(&ds),
        ["unexpected d], expected one of: EOF, NL, SPACELINE"]
    );
    assert_eq!(descr_text(first_node(&start)), "b\"c");
    let (start, ds) = parsed("mindmap\n  a[b\"c\"d]\n");
    assert!(ds.is_empty());
    assert_eq!(descr_text(first_node(&start)), "b\"c\"d");
    let (start, ds) = parsed("mindmap\n  a[line1\nline2]\n");
    assert!(ds.is_empty());
    assert_eq!(descr_text(first_node(&start)), "line1\nline2");
}

#[test]
fn lexer_rejects_braces_in_initial() {
    let (_, ds) = parsed("mindmap\n{x}\n");
    assert_eq!(codes(&ds), ["mindmap/unknown-statement"]);
    assert_eq!(messages(&ds), ["unknown statement {"]);
    let (_, ds) = parsed("mindmap\n  {x}\n");
    assert_eq!(
        messages(&ds),
        ["unexpected {, expected one of: CLASS, EOF, ICON, NL, NODE_DSTART, NODE_ID, SPACELINE"]
    );
}

#[test]
fn inline_decorations_stay_node_text() {
    let (start, ds) = parsed("mindmap\n  root ::icon(x)\n");
    assert!(ds.is_empty());
    let node = first_node(&start);
    assert_eq!(
        node.and_then(|n| n.id.as_ref()).map(|t| t.text.as_str()),
        Some("root ::icon")
    );
    assert_eq!(descr_text(node), "x");
}

#[test]
fn description_kinds() {
    for (src, want) in [
        ("a", Description::Bare),
        ("a[b]", Description::Plain),
        ("a[\"b\"]", Description::Quoted),
        ("a[\"`b`\"]", Description::Markdown),
    ] {
        let (start, ds) = parsed(&format!("mindmap\n  {src}\n"));
        assert!(ds.is_empty(), "{src}");
        assert_eq!(
            first_node(&start).map(|n| n.description),
            Some(want),
            "{src}"
        );
    }
    let (start, _) = parsed("mindmap\n  a[`b`]\n");
    assert_eq!(
        first_node(&start).map(|n| n.description),
        Some(Description::Plain)
    );
    assert_eq!(descr_text(first_node(&start)), "`b`");
}

#[test]
fn empty_quoted_description_invents_no_token() {
    let (_, ds) = parsed("mindmap\n  a[\"\"]\n");
    assert_eq!(codes(&ds), ["mindmap/unexpected-token"]);
    assert_eq!(messages(&ds), ["unexpected ], expected one of: NODE_DESCR"]);
}

#[test]
fn blank_statements_and_stops() {
    let (start, ds) = parsed("mindmap\n  root\n\n  \n    a\n");
    assert!(ds.is_empty());
    assert_eq!(start.document.items.len(), 2);
    let (start, ds) = parsed("mindmap\n");
    assert!(ds.is_empty());
    assert!(
        start
            .document
            .items
            .first()
            .is_some_and(|item| item.statement.blank.is_some())
    );
}

#[test]
fn header_requires_one_newline_before_indented_statement() {
    let (_, ds) = parsed("mindmap\n\n  root\n");
    assert_eq!(codes(&ds), ["mindmap/unexpected-token"]);
    assert_eq!(
        messages(&ds),
        ["unexpected   , expected one of: EOF, NL, SPACELINE"]
    );
    let (_, ds) = parsed("mindmap  \n  root\n");
    assert_eq!(codes(&ds), ["mindmap/unexpected-token"]);
}

#[test]
fn empty_document_needs_a_statement() {
    let (_, ds) = parsed("mindmap");
    assert_eq!(codes(&ds), ["mindmap/unexpected-token"]);
    assert_eq!(
        messages(&ds),
        [
            "unexpected end of input, expected one of: CLASS, ICON, NODE_DSTART, NODE_ID, SPACELINE, SPACELIST"
        ]
    );
    assert_eq!(ds.first().map(|d| d.span), Some(Span { start: 7, end: 7 }));
}

#[test]
fn unexpected_token_lists_accepted_kinds() {
    let (_, ds) = parsed("mindmap\n  a[b]c\n");
    assert_eq!(
        messages(&ds),
        ["unexpected c, expected one of: EOF, NL, SPACELINE"]
    );
    assert_eq!(
        ds.first().map(|d| d.span),
        Some(Span { start: 14, end: 15 })
    );
    let (_, ds) = parsed("mindmap\n  a[\n");
    assert_eq!(codes(&ds), ["mindmap/unterminated"]);
}

#[test]
fn recovery_resumes_after_the_line_end() {
    let (start, ds) = parsed("mindmap\n  root\n    a[b]c\n    d\n");
    assert_eq!(codes(&ds), ["mindmap/unexpected-token"]);
    let ids: Vec<&str> = start
        .document
        .items
        .iter()
        .filter_map(|item| item.statement.node.as_ref()?.id.as_ref())
        .map(|t| t.text.as_str())
        .collect();
    assert_eq!(ids, ["root", "a", "d"]);
}

#[test]
fn recovery_continues_through_open_shapes_across_lines() {
    let (start, ds) = parsed("mindmap\n  root\n    a[\"x\"y\nz]\n    d\n");
    assert_eq!(codes(&ds), ["mindmap/unexpected-token"]);
    let last = start
        .document
        .items
        .last()
        .and_then(|item| item.statement.node.as_ref())
        .and_then(|n| n.id.as_ref());
    assert_eq!(last.map(|t| t.text.as_str()), Some("d"));
}

#[test]
fn unknown_statement_spans_to_the_line_end() {
    let (start, ds) = parsed("mindmap\n{x y}\n  z\n");
    assert_eq!(codes(&ds), ["mindmap/unknown-statement"]);
    assert_eq!(ds.first().map(|d| d.span), Some(Span { start: 8, end: 13 }));
    assert_eq!(
        first_node(&start)
            .and_then(|n| n.id.as_ref())
            .map(|t| t.text.as_str()),
        Some("z")
    );
}

#[test]
fn unterminated_spans_opener_to_end_of_input() {
    for (src, message, start) in [
        ("mindmap\n  a[b", "unterminated [", 11),
        ("mindmap\n  a((b", "unterminated ((", 11),
        ("mindmap\n  a[\"b", "unterminated \"", 12),
        ("mindmap\n  a[\"`b", "unterminated \"`", 12),
        ("mindmap\n  a\n  ::icon(x", "unterminated ::icon(", 14),
        ("mindmap\n  a\n  ::ICON(x", "unterminated ::ICON(", 14),
    ] {
        let (_, ds) = parsed(src);
        assert_eq!(ds.len(), 1, "{src}");
        let d = &ds[0];
        assert_eq!(d.code, "mindmap/unterminated", "{src}");
        assert_eq!(d.message, message, "{src}");
        assert_eq!(
            d.span,
            Span {
                start,
                end: src.len()
            },
            "{src}"
        );
    }
}

#[test]
fn class_mode_at_end_of_input_is_a_blank_class() {
    let (start, ds) = parsed("mindmap\n  a\n  :::");
    assert!(ds.is_empty());
    assert!(
        start
            .document
            .items
            .iter()
            .all(|item| item.statement.class.is_none())
    );
}

#[test]
fn decoration_spans_include_delimiters() {
    let src = "mindmap\n  a\n  ::icon(fa fa-book)\n  :::cls x\n";
    let (start, ds) = parsed(src);
    assert!(ds.is_empty());
    let icon: Option<&Token> = start
        .document
        .items
        .iter()
        .find_map(|item| item.statement.icon.as_ref());
    let class: Option<&Token> = start
        .document
        .items
        .iter()
        .find_map(|item| item.statement.class.as_ref());
    let (icon, class) = (
        icon.map(|t| (t.span, &t.text)),
        class.map(|t| (t.span, &t.text)),
    );
    assert_eq!(
        icon.map(|(span, text_)| (text(src, span), text_.as_str())),
        Some(("::icon(fa fa-book)", "fa fa-book"))
    );
    assert_eq!(
        class.map(|(span, text_)| (text(src, span), text_.as_str())),
        Some((":::cls x", "cls x"))
    );
}

#[test]
fn empty_icon_and_class_create_no_decoration() {
    let (start, ds) = parsed("mindmap\n  a\n  ::icon()\n  :::\n");
    assert!(ds.is_empty());
    assert!(
        start
            .document
            .items
            .iter()
            .all(|item| { item.statement.icon.is_none() && item.statement.class.is_none() })
    );
}

#[test]
fn crlf_and_lone_cr_are_line_ends() {
    for src in ["mindmap\r\n  root\r\n    a\r\n", "mindmap\n  root\r    a\r"] {
        let (start, ds) = parsed(src);
        assert!(ds.is_empty(), "{src}");
        assert_eq!(start.document.items.len(), 2, "{src}");
        let root = start
            .document
            .items
            .first()
            .and_then(|item| item.statement.node.as_ref())
            .and_then(|n| n.id.as_ref());
        assert_eq!(root.map(|t| t.text.as_str()), Some("root"));
    }
}

#[test]
fn removed_spans_keep_source_offsets() {
    let src = "---\ntitle: t\n---\nmindmap\n  root\n";
    let removed = [Span { start: 0, end: 17 }];
    let parsed = parse(src, &removed);
    assert!(parsed.diagnostics.is_empty());
    let node = first_node(&parsed.document);
    assert_eq!(node.map(|n| text(src, n.span)), Some("root"));
    let header = parsed.document.header.as_ref();
    assert_eq!(header.map(|t| text(src, t.span)), Some("mindmap"));
}

#[test]
fn leading_blank_lines_precede_the_header() {
    let src = "\n\n  mindmap\n  root\n";
    let (start, ds) = parsed(src);
    assert!(ds.is_empty());
    assert_eq!(
        start.header.as_ref().map(|t| text(src, t.span)),
        Some("mindmap")
    );
    assert_eq!(first_node(&start).map(|n| text(src, n.span)), Some("root"));
}

#[test]
fn statement_span_excludes_the_stop() {
    let src = "mindmap\n  root\n    a[b]\n";
    let (start, ds) = parsed(src);
    assert!(ds.is_empty());
    let item = &start.document.items[1];
    assert_eq!(text(src, item.statement.span), "    a[b]");
    assert_eq!(text(src, item.stop.span), "\n");
}

#[test]
fn parse_never_panics_on_hostile_input() {
    let hostile = [
        String::new(),
        "mindmap".to_owned(),
        ":::".to_owned(),
        "(".repeat(50),
        format!("mindmap\n{}", "a[\"`".repeat(20)),
        "mindmap\n\u{0}\u{fffd}".to_owned(),
    ];
    for src in &hostile {
        let _ = parse(src, &[]);
    }
}
