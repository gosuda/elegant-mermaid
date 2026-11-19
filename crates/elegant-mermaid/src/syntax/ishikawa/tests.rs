use super::ast::Start;
use super::lexer::{K_END, K_NL, Scanner};
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

fn messages(ds: &[Diagnostic]) -> Vec<&str> {
    ds.iter().map(|d| d.message.as_str()).collect()
}

fn texts(start: &Start) -> Vec<&str> {
    start
        .document
        .items
        .iter()
        .filter_map(|item| item.statement.text.as_ref())
        .map(|token| token.text.as_str())
        .collect()
}

fn span(start: usize, end: usize) -> Span {
    Span { start, end }
}

#[test]
fn lexer_appends_virtual_newline_and_splits_lines() {
    assert_eq!(
        kinds("ishikawa-beta\n  Effect"),
        ["ISHIKAWA", "NL", "SPACELIST", "TEXT", "NL", "EOF", "END"]
    );
    assert_eq!(kinds("ishikawa\n"), ["ISHIKAWA", "SPACELINE", "EOF", "END"]);
    assert_eq!(
        kinds("ishikawa  \n  Effect"),
        [
            "ISHIKAWA",
            "SPACELINE",
            "SPACELIST",
            "TEXT",
            "NL",
            "EOF",
            "END"
        ]
    );
}

#[test]
fn lexer_folds_header_and_tries_beta_first() {
    for header in ["ishikawa", "ISHIKAWA", "Ishikawa-Beta", "ishikawa-beta"] {
        let (start, ds) = parsed(&format!("{header}\n  Effect\n"));
        assert!(ds.is_empty(), "{header}");
        assert_eq!(start.header.map(|t| t.text), Some(header.to_owned()));
    }
    assert_eq!(
        kinds("ishikawa-betax"),
        ["ISHIKAWA", "TEXT", "NL", "EOF", "END"]
    );
    assert_eq!(kinds("ishikawax"), ["TEXT", "NL", "EOF", "END"]);
    assert_eq!(kinds("ishikawa_x"), ["TEXT", "NL", "EOF", "END"]);
}

#[test]
fn text_token_takes_whole_line() {
    let (start, ds) =
        parsed("ishikawa-beta\n  Effect\n    \"a\" {b} (c) [d]; e %% not a comment  \n");
    assert!(ds.is_empty());
    assert_eq!(
        texts(&start),
        ["Effect", "\"a\" {b} (c) [d]; e %% not a comment  "]
    );
}

#[test]
fn comment_lines_and_blank_lines_are_whitespace_statements() {
    let (start, ds) = parsed("%% lead\nishikawa-beta\n  %% note\n  Effect\n\n   \n  Cause\n");
    assert!(ds.is_empty());
    assert_eq!(start.leading.len(), 2);
    assert_eq!(texts(&start), ["Effect", "Cause"]);
    let blanks = start
        .document
        .items
        .iter()
        .filter(|item| item.statement.blank.is_some())
        .count();
    assert!(blanks > 0);
}

#[test]
fn indent_token_is_retained_separately_from_text() {
    let (start, ds) = parsed("ishikawa-beta\n\t Effect\n        Cause\n");
    assert!(ds.is_empty());
    let items = &start.document.items;
    let (Some(first), Some(second)) = (items.first(), items.get(1)) else {
        assert!(items.len() >= 2, "two statements expected");
        return;
    };
    let (Some(indent), Some(text)) = (&first.statement.indent, &first.statement.text) else {
        assert!(
            first.statement.indent.is_some() && first.statement.text.is_some(),
            "indent and text expected"
        );
        return;
    };
    assert_eq!(indent.text, "\t ");
    assert_eq!(text.text, "Effect");
    assert_eq!(indent.span, span(14, 16));
    assert_eq!(text.span, span(16, 22));
    assert_eq!(first.statement.span, span(14, 22));
    assert_eq!(
        second.statement.indent.as_ref().map(|t| t.text.len()),
        Some(8)
    );
}

#[test]
fn spans_skip_removed_regions() {
    let src = "---\nx: y\n---\nishikawa-beta\n  Effect\n";
    let parsed = parse(src, &[span(0, 13)]);
    assert!(parsed.diagnostics.is_empty());
    assert_eq!(parsed.document.header.map(|t| t.span), Some(span(13, 26)));
    let first = parsed
        .document
        .document
        .items
        .first()
        .and_then(|item| item.statement.text.as_ref());
    assert_eq!(first.map(|t| t.span), Some(span(29, 35)));
}

#[test]
fn missing_header() {
    let (_, ds) = parsed("Effect\n");
    assert_eq!(
        messages(&ds),
        ["unexpected Effect, expected one of: ISHIKAWA, SPACELINE"]
    );
    assert_eq!(
        ds.first().map(|d| (d.code, d.span)),
        Some(("ishikawa/unexpected-token", span(0, 6)))
    );
}

#[test]
fn header_without_document_is_rejected() {
    let (_, ds) = parsed("ishikawa-beta");
    assert_eq!(
        messages(&ds),
        ["unexpected end of input, expected one of: SPACELINE, SPACELIST, TEXT"]
    );
    assert_eq!(
        ds.first().map(|d| (d.code, d.span)),
        Some(("ishikawa/unexpected-token", span(13, 13)))
    );
}

#[test]
fn header_line_end_is_a_blank_document() {
    for src in ["ishikawa-beta\n", "ishikawa\n\n\n", "ishikawa-beta  \n"] {
        let (start, ds) = parsed(src);
        assert!(ds.is_empty(), "{src}");
        assert!(texts(&start).is_empty(), "{src}");
        assert!(!start.document.items.is_empty(), "{src}");
    }
}

#[test]
fn body_header_word_is_a_statement_error() {
    let (start, ds) = parsed("ishikawa-beta\n  Effect\nishikawa other\n  Cause\n");
    assert_eq!(messages(&ds), ["unknown statement ishikawa"]);
    assert_eq!(
        ds.first().map(|d| (d.code, d.span)),
        Some(("ishikawa/unknown-statement", span(23, 37)))
    );
    assert_eq!(texts(&start), ["Effect", "Cause"]);
}

#[test]
fn indented_body_header_word_is_an_indented_error() {
    let (start, ds) = parsed("ishikawa-beta\n  Effect\n  ishikawa-beta\n  Cause\n");
    assert_eq!(
        messages(&ds),
        ["unexpected ishikawa-beta, expected one of: EOF, NL, SPACELINE, TEXT"]
    );
    assert_eq!(texts(&start), ["Effect", "Cause"]);
}

#[test]
fn statement_without_indentation_is_an_effect_candidate() {
    let (start, ds) = parsed("ishikawa-beta\nEffect\n  Cause\n");
    assert!(ds.is_empty());
    assert!(
        start
            .document
            .items
            .first()
            .is_some_and(|item| item.statement.indent.is_none())
    );
    assert_eq!(texts(&start), ["Effect", "Cause"]);
}

#[test]
fn document_span_and_stops() {
    let src = "ishikawa-beta\n  Effect\n\n\n  Cause";
    let (start, ds) = parsed(src);
    assert!(ds.is_empty());
    assert_eq!(start.span, span(0, src.len()));
    let last = start.document.items.last();
    assert_eq!(
        last.and_then(|item| item.statement.text.as_ref())
            .map(|t| t.text.as_str()),
        Some("Cause")
    );
    assert_eq!(
        last.and_then(|item| item.stop.tokens.first())
            .map(|t| t.kind),
        Some(K_NL)
    );
}
