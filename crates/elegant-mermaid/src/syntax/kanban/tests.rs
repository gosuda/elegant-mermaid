#![expect(
    clippy::unwrap_used,
    clippy::expect_used,
    reason = "tests assert on fixtures whose absence is a failing test"
)]

use super::ast::{Node, Start, Statement, Token};
use super::lexer::{K_END, Scanner};
use super::parse;
use crate::diag::Diagnostic;
use crate::source::Span;
use crate::syntax::preprocess::preprocess;

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

fn first_statement(start: &Start) -> &Statement {
    start
        .document
        .items
        .iter()
        .map(|item| &item.statement)
        .find(|statement| statement.node.is_some())
        .expect("a node statement")
}

fn first_node(start: &Start) -> &Node {
    first_statement(start).node.as_ref().expect("a node")
}

fn slice(src: &str, span: Span) -> &str {
    src.get(span.start..span.end).unwrap_or("")
}

#[test]
fn lexer_splits_columns_cards_and_separators() {
    assert_eq!(
        kinds("kanban\n  root"),
        ["KANBAN", "NL", "SPACELIST", "NODE_ID", "NL", "EOF", "END"]
    );
    assert_eq!(kinds("kanban\n"), ["KANBAN", "SPACELINE", "EOF", "END"]);
    assert_eq!(
        kinds("kanban  \n  root"),
        [
            "KANBAN",
            "SPACELINE",
            "SPACELIST",
            "NODE_ID",
            "NL",
            "EOF",
            "END"
        ]
    );
    assert_eq!(
        kinds("kanban\n  id[Todo]"),
        [
            "KANBAN",
            "NL",
            "SPACELIST",
            "NODE_ID",
            "NODE_DSTART",
            "NODE_DESCR",
            "NODE_DEND",
            "NL",
            "EOF",
            "END"
        ]
    );
}

#[test]
fn header_folds_case_and_stops_at_word_boundary() {
    assert_eq!(kinds("KanBan\n").first(), Some(&"KANBAN"));
    assert_eq!(kinds("kanbans"), ["NODE_ID", "NL", "EOF", "END"]);
    assert_eq!(kinds("kanban-x"), ["KANBAN", "NODE_ID", "NL", "EOF", "END"]);
}

#[test]
fn shape_data_tokens_keep_values_and_source_spans() {
    let src = "kanban\n  a[b]@{ ticket: X }\n";
    let (start, ds) = parsed(src);
    assert!(ds.is_empty());
    let statement = first_statement(&start);
    let data = statement.data.as_ref().expect("shape data");
    assert_eq!(slice(src, data.span), "@{ ticket: X }");
    assert_eq!(data.value(), " ticket: X ");
    assert_eq!(data.tokens.first().map(|t| t.text.as_str()), Some(""));
    assert_eq!(
        slice(src, data.tokens.first().map(|t| t.span).unwrap()),
        "@{"
    );
    assert_eq!(slice(src, statement.span), "  a[b]@{ ticket: X }");
    assert_eq!(
        kinds(src),
        [
            "KANBAN",
            "NL",
            "SPACELIST",
            "NODE_ID",
            "NODE_DSTART",
            "NODE_DESCR",
            "NODE_DEND",
            "SHAPE_DATA",
            "SHAPE_DATA",
            "SPACELINE",
            "EOF",
            "END"
        ]
    );
}

#[test]
fn shape_data_empty_braces_are_defined() {
    let src = "kanban\n  a@{}\n";
    let (start, ds) = parsed(src);
    assert!(ds.is_empty());
    let statement = first_statement(&start);
    assert_eq!(first_node(&start).id.as_ref().unwrap().text, "a");
    let data = statement.data.as_ref().expect("shape data");
    assert_eq!(data.value(), "");
    assert_eq!(slice(src, data.span), "@{}");
}

#[test]
fn shape_data_quoted_line_breaks_become_br() {
    let (start, ds) = parsed("kanban\n  a[b]@{ label: \"x\n     y\n\n z\", n: 1 }\n");
    assert!(ds.is_empty());
    assert_eq!(
        first_statement(&start).data.as_ref().unwrap().value(),
        " label: \"x<br/>y<br/>z\", n: 1 "
    );
    let (crlf, ds) = parsed("kanban\r\n  a[b]@{ label: \"x\r\n  y\" }\r\n");
    assert!(ds.is_empty());
    assert_eq!(
        first_statement(&crlf).data.as_ref().unwrap().value(),
        " label: \"x<br/>y\" "
    );
}

#[test]
fn shape_data_braces_inside_quotes_do_not_close() {
    let src = "kanban\n  a@{ label: \"}\" }\n";
    let (start, ds) = parsed(src);
    assert!(ds.is_empty());
    let data = first_statement(&start).data.as_ref().unwrap();
    assert_eq!(data.value(), " label: \"}\" ");
    assert_eq!(slice(src, data.span), "@{ label: \"}\" }");
}

#[test]
fn shape_data_blocks_concatenate() {
    let (start, ds) = parsed("kanban\n  a@{ x: 1 }@{ y: 2 }\n");
    assert!(ds.is_empty());
    assert_eq!(
        first_statement(&start).data.as_ref().unwrap().value(),
        " x: 1  y: 2 "
    );
}

#[test]
fn shape_data_multiline_block() {
    let src = "kanban\n  a[b]@{\n    ticket: 1\n    assigned: z\n  }\n";
    let (start, ds) = parsed(src);
    assert!(ds.is_empty());
    let statement = first_statement(&start);
    assert_eq!(
        statement.data.as_ref().unwrap().value(),
        "\n    ticket: 1\n    assigned: z\n  "
    );
    assert_eq!(
        slice(src, statement.span),
        "  a[b]@{\n    ticket: 1\n    assigned: z\n  }"
    );
}

#[test]
fn shape_data_caret_is_lexical_error() {
    let (_, ds) = parsed("kanban\n  a@{ x: ^ }\n");
    assert_eq!(codes(&ds), ["kanban/unexpected-token"]);
    assert_eq!(
        messages(&ds),
        ["unexpected ^, expected one of: EOF, NL, SHAPE_DATA, SPACELINE"]
    );
    assert_eq!(ds[0].span.end - ds[0].span.start, 1);
}

#[test]
fn at_sign_outside_metadata_is_not_an_identifier_character() {
    let (_, ds) = parsed("kanban\n  a@b\n");
    assert_eq!(
        messages(&ds),
        ["unexpected @, expected one of: EOF, NL, SHAPE_DATA, SPACELINE"]
    );
    let (_, ds) = parsed("kanban\n@{ x }\n");
    assert_eq!(codes(&ds), ["kanban/unknown-statement"]);
    assert_eq!(ds[0].message, "unknown statement @{");
}

#[test]
fn metadata_after_decoration_is_rejected() {
    let (_, ds) = parsed("kanban\n  a\n  ::icon(x)@{ y: 1 }\n");
    assert_eq!(codes(&ds), ["kanban/unexpected-token"]);
    assert_eq!(
        messages(&ds),
        ["unexpected @{, expected one of: EOF, NL, SPACELINE"]
    );
}

#[test]
fn unterminated_metadata_reports_opener() {
    let src = "kanban\n  a[b]@{ x: 1";
    let (_, ds) = parsed(src);
    assert_eq!(codes(&ds), ["kanban/unterminated"]);
    assert_eq!(ds[0].message, "unterminated @{");
    assert_eq!(slice(src, ds[0].span), "@{ x: 1");
    let src = "kanban\n  a@{ x: \"open";
    let (_, ds) = parsed(src);
    assert_eq!(codes(&ds), ["kanban/unterminated"]);
    assert_eq!(slice(src, ds[0].span), "@{ x: \"open");
}

#[test]
fn unterminated_node_icon_and_markdown() {
    for (src, want) in [
        ("kanban\n  a[b", "[b"),
        ("kanban\n  a[\"b", "\"b"),
        ("kanban\n  a[\"`b", "\"`b"),
        ("kanban\n  a\n  ::icon(", "::icon("),
    ] {
        let (_, ds) = parsed(src);
        assert_eq!(codes(&ds), ["kanban/unterminated"], "{src}");
        assert_eq!(slice(src, ds[0].span), want, "{src}");
    }
}

#[test]
fn inline_decorations_stay_node_text() {
    let (start, ds) = parsed("kanban\n  root ::icon(x)\n");
    assert!(ds.is_empty());
    let node = first_node(&start);
    assert_eq!(node.id.as_ref().unwrap().text, "root ::icon");
    assert_eq!(node.descr.as_ref().unwrap().text, "x");
}

#[test]
fn node_id_keeps_trailing_spaces() {
    let (start, ds) = parsed("kanban\n  id1   @{ x: 1 }\n");
    assert!(ds.is_empty());
    assert_eq!(first_node(&start).id.as_ref().unwrap().text, "id1   ");
}

#[test]
fn decorations_and_indent() {
    let (start, ds) = parsed("kanban\n  col[Todo]\n    ::icon(fa fa-book)\n    :::urgent big\n");
    assert!(ds.is_empty());
    let find = |pick: fn(&Statement) -> Option<&Token>| {
        start
            .document
            .items
            .iter()
            .find_map(|item| pick(&item.statement))
            .map(|token| token.text.clone())
    };
    assert_eq!(find(|s| s.icon.as_ref()).as_deref(), Some("fa fa-book"));
    assert_eq!(find(|s| s.class.as_ref()).as_deref(), Some("urgent big"));
}

#[test]
fn semicolon_is_ordinary_node_text() {
    let (start, ds) = parsed("kanban\n  a;b[c;d]\n");
    assert!(ds.is_empty());
    let node = first_node(&start);
    assert_eq!(node.id.as_ref().unwrap().text, "a;b");
    assert_eq!(node.descr.as_ref().unwrap().text, "c;d");
}

#[test]
fn recovery_resumes_at_next_line() {
    let (start, ds) = parsed("kanban\n  a[b]c\n  d[e]\n");
    assert_eq!(codes(&ds), ["kanban/unexpected-token"]);
    let ids: Vec<&str> = start
        .document
        .items
        .iter()
        .filter_map(|item| item.statement.node.as_ref()?.id.as_ref())
        .map(|id| id.text.as_str())
        .collect();
    assert!(ids.contains(&"d"));
}

#[test]
fn empty_delimiter_label_has_no_production() {
    let (_, ds) = parsed("kanban\n  a[\"\"]\n");
    assert_eq!(codes(&ds), ["kanban/unexpected-token"]);
    assert_eq!(ds[0].message, "unexpected ], expected one of: NODE_DESCR");
}

#[test]
fn missing_header() {
    let (_, ds) = parsed("  a\n");
    assert_eq!(codes(&ds), ["kanban/unexpected-token"]);
}

#[test]
fn spans_stay_inside_source() {
    for src in [
        "kanban\n  a[b]@{ x: \"\u{e9}\n y\" }\n  ::icon(\u{e9})\n",
        "kanban\n\u{a0}\u{a0}a@{\u{e9}",
        "kanban\n  a@{ \u{e9}^ }\n",
    ] {
        let (start, ds) = parsed(src);
        for d in &ds {
            assert!(d.span.start <= d.span.end && d.span.end <= src.len());
            assert!(src.is_char_boundary(d.span.start) && src.is_char_boundary(d.span.end));
        }
        for item in &start.document.items {
            assert!(item.statement.span.end <= src.len());
        }
    }
}

#[test]
fn corpus_parses_without_diagnostics() {
    let root = concat!(env!("CARGO_MANIFEST_DIR"), "/../../corpus/kanban");
    let mut checked = 0;
    for source in std::fs::read_dir(root).expect("corpus directory") {
        let source = source.expect("entry").path();
        for file in std::fs::read_dir(&source).expect("source directory") {
            let path = file.expect("entry").path();
            let src = std::fs::read_to_string(&path).expect("corpus file");
            let removed = preprocess(&src).removed;
            let parsed = parse(&src, &removed);
            assert!(parsed.diagnostics.is_empty(), "{}", path.display());
            checked += 1;
        }
    }
    assert!(checked > 0);
}
