use super::ast::{Pie, StatementKind};
use super::lexer::{float_length, integer_length};
use super::parse;
use crate::source::Span;

fn parsed(source: &str) -> (Pie, Vec<String>) {
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

fn sections(pie: &Pie) -> Vec<(String, String)> {
    pie.body
        .iter()
        .filter_map(|statement| match &statement.kind {
            StatementKind::PieSection(section) => {
                Some((section.label.text.clone(), section.number.text.clone()))
            }
            StatementKind::TitleAndAccessibilities(_) => None,
        })
        .collect()
}

fn pair(label: &str, number: &str) -> (String, String) {
    (label.to_owned(), number.to_owned())
}

#[test]
fn header_forms() {
    for (source, show_data, count) in [
        ("pie", false, 0),
        ("\n\npie\n", false, 0),
        ("pie showData", true, 0),
        ("pie showData\n\"a\": 1", true, 1),
        ("pie \"a\": 1", false, 1),
        ("pie showData \"a\": 1\n", true, 1),
        ("pie title x\n\"a\": 1", false, 1),
    ] {
        let (pie, messages) = parsed(source);
        assert!(messages.is_empty(), "{source}: {messages:?}");
        assert_eq!(pie.show_data, show_data, "{source}");
        assert_eq!(sections(&pie).len(), count, "{source}");
    }
}

#[test]
fn show_data_keyword_boundary() {
    assert_eq!(
        only("pie showDataX\n"),
        vec!["pie/unknown-statement: unknown statement showDataX"]
    );
    assert_eq!(
        only("pie showData showData\n"),
        vec!["pie/unknown-statement: unknown statement showData"]
    );
}

#[test]
fn section_numbers() {
    for number in ["10", "0", "-3", "42.96", "-0.5", "007.5", "0.0"] {
        let (pie, messages) = parsed(&format!("pie\n\"a\" : {number}\n"));
        assert!(messages.is_empty(), "{number}: {messages:?}");
        assert_eq!(sections(&pie), vec![pair("a", number)], "{number}");
    }
    for number in [
        "+5", ".5", "5.", "1e3", "007", "1,5", "NaN", "0x10", "1.2.3",
    ] {
        assert!(
            !only(&format!("pie\n\"a\" : {number}\n")).is_empty(),
            "{number}"
        );
    }
}

#[test]
fn number_lexing_backtracks() {
    assert_eq!(integer_length("12."), 1);
    assert_eq!(integer_length("1."), 0);
    assert_eq!(integer_length("0."), 0);
    assert_eq!(integer_length("007"), 1);
    assert_eq!(float_length("1.55.3"), 3);
    assert_eq!(float_length("1.5.3"), 0);
    assert_eq!(float_length("0.5"), 3);
}

#[test]
fn string_forms() {
    let (pie, messages) = parsed(
        "pie\n\
        \"double\" : 1\n\
        'single' : 2\n\
        \"it's\" : 3\n\
        'say \"x\"' : 4\n\
        \"a\\\"b\" : 5\n\
        \"tab\\there\" : 6\n\
        \"two\nlines\" : 7\n\
        \"% not a comment\" : 8\n\
        \"\" : 9\n",
    );
    assert!(messages.is_empty(), "{messages:?}");
    let labels: Vec<String> = sections(&pie).into_iter().map(|(label, _)| label).collect();
    assert_eq!(
        labels,
        vec![
            "double",
            "single",
            "it's",
            "say \"x\"",
            "a\"b",
            "tab\there",
            "two\nlines",
            "% not a comment",
            ""
        ]
    );
}

#[test]
fn string_token_keeps_delimiters_in_span() {
    let (pie, messages) = parsed("pie\n  \"a\\\"\" : 4\n");
    assert!(messages.is_empty(), "{messages:?}");
    let statement = &pie.body[0];
    let StatementKind::PieSection(section) = &statement.kind else {
        panic!("not a section");
    };
    assert_eq!(section.label.text, "a\"");
    assert_eq!(section.label.span, Span { start: 6, end: 11 });
    assert_eq!(statement.span, Span { start: 6, end: 15 });
}

#[test]
fn metadata() {
    let (pie, messages) = parsed(
        "pie\n  title   A   B  \n  accTitle:  T  x \n  accDescr: d %% c\naccDescr {\n  a  b\n\n  c\n}\ntitle\n\"a\" : 1",
    );
    assert!(messages.is_empty(), "{messages:?}");
    assert_eq!(pie.body.len(), 2);
    let StatementKind::TitleAndAccessibilities(group) = &pie.body[0].kind else {
        panic!("not metadata");
    };
    let got: Vec<(&str, &str)> = group
        .items
        .iter()
        .map(|item| (item.field, item.value.as_str()))
        .collect();
    assert_eq!(
        got,
        vec![
            ("title", "A B"),
            ("accTitle", "T x"),
            ("accDescr", "d"),
            ("accDescr", "a b\nc"),
            ("title", "")
        ]
    );
}

#[test]
fn inline_title_on_header_line() {
    let (pie, messages) = parsed("pie title Pets adopted\n\"a\" : 1");
    assert!(messages.is_empty(), "{messages:?}");
    let StatementKind::TitleAndAccessibilities(group) = &pie.body[0].kind else {
        panic!("not metadata");
    };
    assert_eq!(group.items[0].value, "Pets adopted");
}

#[test]
fn comments() {
    let (pie, messages) =
        parsed("pie %% header comment\n%% line\n\"a\" : 1 %% trailing\n  %% indented\n\"b\" : 2");
    assert!(messages.is_empty(), "{messages:?}");
    assert_eq!(sections(&pie), vec![pair("a", "1"), pair("b", "2")]);
}

#[test]
fn line_endings() {
    let (pie, messages) = parsed("pie\r\n\"a\" : 1\r\"b\" : 2\n\n\n\"c\" : 3");
    assert!(messages.is_empty(), "{messages:?}");
    assert_eq!(sections(&pie).len(), 3);
}

#[test]
fn section_ends_at_line_end() {
    let result = parse("pie\n\"a\" : 1 \"b\" : 2\n", &[]);
    assert_eq!(
        result.diagnostics[0].message,
        "unexpected \"b\", expected one of: EOF, NEWLINE"
    );
    assert_eq!(result.diagnostics[0].span, Span { start: 12, end: 15 });
}

#[test]
fn error_recovery_skips_to_next_line() {
    let (pie, messages) = parsed("pie\n\"a\" 1 \"x\"\n\"b\" : 2\n");
    assert_eq!(
        messages,
        ["pie/missing-colon: Missing colon between slice label and number."]
    );
    assert_eq!(sections(&pie), vec![pair("b", "2")]);
}

#[test]
fn unknown_statements() {
    let result = parse("pie\nDogs : 1\n\"a\" : 1\nsemi ; colon\n", &[]);
    let messages: Vec<String> = result
        .diagnostics
        .iter()
        .map(|d| format!("{}: {}", d.code, d.message))
        .collect();
    assert_eq!(messages.len(), 2);
    assert!(messages.contains(&"pie/unknown-statement: unknown statement semi".to_owned()));
    let bare_label = result
        .diagnostics
        .iter()
        .find(|d| d.code == "pie/label-requires-quotes");
    assert!(bare_label.is_some());
    assert_eq!(bare_label.map(|d| d.span), Some(Span { start: 4, end: 8 }));
    assert_eq!(sections(&result.document), vec![pair("a", "1")]);
}

#[test]
fn unterminated() {
    for (source, token, start) in [
        ("pie\n\"abc", "\"", 4),
        ("pie\n\"abc\\", "\"", 4),
        ("pie\n'abc : 1\n\"x\" : 2", "'", 4),
        ("pie\naccDescr {\n  never", "{", 13),
    ] {
        let result = parse(source, &[]);
        assert_eq!(result.diagnostics.len(), 1, "{source}");
        let d = &result.diagnostics[0];
        if token == "{" {
            assert_eq!(d.code, "pie/unterminated", "{source}");
            assert_eq!(d.message, format!("unterminated {token}"), "{source}");
            assert_eq!(
                d.span,
                Span {
                    start,
                    end: source.len()
                },
                "{source}"
            );
        } else {
            assert_eq!(d.code, "pie/quote-unclosed", "{source}");
            let end = source[4..]
                .split_once(':')
                .map_or(source.len(), |(head, _)| {
                    4 + head.trim_end_matches([' ', '\t']).len()
                });
            assert_eq!(d.span, Span { start: end, end }, "{source}");
        }
    }
}

#[test]
fn backslash_before_line_end_is_not_a_string() {
    let result = parse("pie\n\"a\\\nb\" : 1\n", &[]);
    assert!(!result.diagnostics.is_empty());
    assert_ne!(result.diagnostics[0].code, "pie/unterminated");
}

#[test]
fn keywords_are_word_bounded() {
    assert_eq!(
        only("pie\npie : 1\n"),
        vec!["pie/unknown-statement: unknown statement pie"]
    );
    assert_eq!(
        only("pie\npie-chart : 1\n"),
        vec!["pie/label-requires-quotes: A slice label is missing quotes (single or double)."]
    );
}

#[test]
fn removed_spans_are_skipped() {
    let result = parse(
        "pie\n%%{init: {}}%%\n\"a\" : 1\n",
        &[Span { start: 4, end: 18 }],
    );
    assert!(result.diagnostics.is_empty());
    assert_eq!(sections(&result.document), vec![pair("a", "1")]);
}

#[test]
fn missing_header() {
    assert_eq!(
        only("\"a\" : 1"),
        vec!["pie/unexpected-token: unexpected \"a\", expected one of: pie"]
    );
}
