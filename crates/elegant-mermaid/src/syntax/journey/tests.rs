use super::ast::{Start, StatementKind};
use super::parse;
use crate::source::Span;
use crate::syntax::preprocess::preprocess;

fn parsed(source: &str) -> (Start, Vec<String>) {
    let removed = preprocess(source).removed;
    let result = parse(source, &removed);
    let messages = result
        .diagnostics
        .iter()
        .map(|d| format!("{}: {}", d.code, d.message))
        .collect();
    (result.document, messages)
}

fn statements(start: &Start) -> Vec<&StatementKind> {
    start
        .document
        .lines
        .iter()
        .filter_map(|line| line.statement.as_ref().map(|s| &s.kind))
        .collect()
}

fn slice(source: &str, span: Span) -> &str {
    &source[span.start..span.end]
}

fn task(kind: &StatementKind) -> &super::ast::Task {
    match kind {
        StatementKind::Task(task) => task,
        other => panic!("not a task: {other:?}"),
    }
}

#[test]
fn statement_forms() {
    let src = "journey\ntitle  My day\naccTitle: A title \naccDescr: A line\nsection Go\n  Make tea: 5: Me\n";
    let (start, messages) = parsed(src);
    assert!(messages.is_empty(), "{messages:?}");
    let kinds = statements(&start);
    assert_eq!(kinds.len(), 5);
    let StatementKind::Title(title) = kinds[0] else {
        panic!("title")
    };
    assert_eq!(title.text.text, " My day");
    assert_eq!(slice(src, title.text.span), " My day");
    let StatementKind::AccTitle(acc) = kinds[1] else {
        panic!("accTitle")
    };
    assert_eq!(acc.value.text, "A title ");
    let StatementKind::AccDescr(descr) = kinds[2] else {
        panic!("accDescr")
    };
    assert_eq!(descr.value.text, "A line");
    let StatementKind::Section(section) = kinds[3] else {
        panic!("section")
    };
    assert_eq!(section.text.text, "Go");
    let make = task(kinds[4]);
    assert_eq!(make.name.text, "Make tea");
    assert_eq!(make.data.text, ": 5: Me");
    assert_eq!(slice(src, start.header.span), "journey");
    assert_eq!(start.span.start, 0);
    assert_eq!(slice(src, start.document.lines[1].span), "title  My day");
}

#[test]
fn task_fields_keep_spans() {
    let src = "journey\n  Do work :  1 : Me, Cat :extra\n";
    let (start, messages) = parsed(src);
    assert!(messages.is_empty());
    let kinds = statements(&start);
    let work = task(kinds[0]);
    assert_eq!(work.name.text, "Do work ");
    assert_eq!(work.fields.len(), 3);
    let raw = ["  1 ", " Me, Cat ", "extra"];
    let trimmed = ["1", "Me, Cat", "extra"];
    for (i, field) in work.fields.iter().enumerate() {
        assert_eq!(field.raw.text, raw[i]);
        assert_eq!(slice(src, field.raw.span), raw[i]);
        assert_eq!(field.trimmed.text, trimmed[i]);
        assert_eq!(slice(src, field.trimmed.span), trimmed[i]);
    }
}

#[test]
fn empty_trailing_fields_stay_as_fields() {
    let (start, messages) = parsed("journey\nT: 3:\nU: :\n");
    assert!(messages.is_empty());
    let kinds = statements(&start);
    assert_eq!(task(kinds[0]).fields.len(), 2);
    let second = &task(kinds[1]).fields;
    assert_eq!(second.len(), 2);
    assert_eq!(second[0].raw.span.start, second[0].trimmed.span.start);
    assert_eq!(second[0].trimmed.span.start, second[0].trimmed.span.end);
}

#[test]
fn keywords_ignore_case_and_take_any_leading_whitespace_char() {
    let (start, messages) = parsed("JOURNEY\nTITLE x\nSection\ty\nACCTITLE:z\n");
    assert!(messages.is_empty(), "{messages:?}");
    let kinds = statements(&start);
    let StatementKind::Title(title) = kinds[0] else {
        panic!("title")
    };
    assert_eq!(title.text.text, "x");
    let StatementKind::Section(section) = kinds[1] else {
        panic!("section")
    };
    assert_eq!(section.text.text, "y");
    let StatementKind::AccTitle(acc) = kinds[2] else {
        panic!("accTitle")
    };
    assert_eq!(acc.value.text, "z");
}

#[test]
fn title_keyword_outranks_task_name() {
    let (start, messages) = parsed("journey\nTitle page: 3: Me\n");
    assert!(messages.is_empty());
    let StatementKind::Title(title) = statements(&start)[0] else {
        panic!("title")
    };
    assert_eq!(title.text.text, "page: 3: Me");
}

#[test]
fn semicolon_is_invalid_and_recovery_stops_at_line_end() {
    let src = "journey\nA: 3; B: 4\nC: 2\n";
    let removed = preprocess(src).removed;
    let result = parse(src, &removed);
    let messages: Vec<String> = result
        .diagnostics
        .iter()
        .map(|d| format!("{}: {}", d.code, d.message))
        .collect();
    assert_eq!(messages, ["journey/unknown-statement: unknown statement ;"]);
    assert_eq!(slice(src, result.diagnostics[0].span), "; B: 4");
    let kinds = statements(&result.document);
    assert_eq!(kinds.len(), 2);
    assert_eq!(task(kinds[1]).name.text, "C");
}

#[test]
fn task_without_data_is_rejected_once() {
    let src = "journey\nLonely\nB: 4\n";
    let removed = preprocess(src).removed;
    let result = parse(src, &removed);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(
        result.diagnostics[0].message,
        "unexpected end of line, expected one of: taskData"
    );
    assert_eq!(slice(src, result.diagnostics[0].span), "\n");
    assert_eq!(statements(&result.document).len(), 1);
}

#[test]
fn bare_colon_after_name_is_rejected() {
    let src = "journey\nName :\nB: 4\n";
    let removed = preprocess(src).removed;
    let result = parse(src, &removed);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(
        result.diagnostics[0].message,
        "unexpected :, expected one of: taskData"
    );
    assert_eq!(slice(src, result.diagnostics[0].span), ":");
    assert_eq!(statements(&result.document).len(), 1);
}

#[test]
fn standalone_data_and_header_repeat_are_unknown_statements() {
    let (start, messages) = parsed("journey\n: 4: x\njourney\nB: 4\n");
    assert_eq!(
        messages,
        [
            "journey/unknown-statement: unknown statement : 4: x",
            "journey/unknown-statement: unknown statement journey"
        ]
    );
    assert_eq!(statements(&start).len(), 1);
}

#[test]
fn header_word_needs_boundary() {
    let (start, messages) = parsed("journey\njourneys: 3\n");
    assert!(messages.is_empty());
    assert_eq!(task(statements(&start)[0]).name.text, "journeys");
}

#[test]
fn multiline_description_keeps_braces_and_trims_nothing() {
    let src = "journey\naccDescr {\n  first\n  second\n}\nA: 3\n";
    let (start, messages) = parsed(src);
    assert!(messages.is_empty());
    let kinds = statements(&start);
    let StatementKind::AccDescrMultiline(block) = kinds[0] else {
        panic!("block")
    };
    assert_eq!(block.value.text, "first\n  second\n");
    assert_eq!(slice(src, block.open), "{");
    assert_eq!(slice(src, block.close.unwrap()), "}");
    assert_eq!(kinds.len(), 2);
}

#[test]
fn empty_multiline_description_makes_no_statement() {
    let (start, messages) = parsed("journey\naccDescr {\n}\n");
    assert!(messages.is_empty());
    assert!(statements(&start).is_empty());
}

#[test]
fn unterminated_description_spans_to_eof() {
    let src = "journey\naccDescr {\nnever closed";
    let removed = preprocess(src).removed;
    let result = parse(src, &removed);
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].message, "unterminated {");
    assert_eq!(slice(src, result.diagnostics[0].span), "{\nnever closed");
    let StatementKind::AccDescrMultiline(block) = statements(&result.document)[0] else {
        panic!("block")
    };
    assert!(block.close.is_none());
    assert_eq!(block.value.text, "never closed");
}

#[test]
fn quotes_never_unterminate() {
    let (_, messages) = parsed("journey\nSay \"hi: 3\nB: 4\n");
    assert!(messages.is_empty());
}

#[test]
fn accessibility_values_keep_hash_and_semicolon() {
    let (start, messages) = parsed("journey\naccTitle: a # b; c\naccDescr: d # e; f\n");
    assert!(messages.is_empty());
    let kinds = statements(&start);
    let StatementKind::AccTitle(title) = kinds[0] else {
        panic!("accTitle")
    };
    let StatementKind::AccDescr(descr) = kinds[1] else {
        panic!("accDescr")
    };
    assert_eq!(title.value.text, "a # b; c");
    assert_eq!(descr.value.text, "d # e; f");
}

#[test]
fn accessibility_colon_consumes_line_break_whitespace() {
    let (start, messages) = parsed("journey\naccTitle:\n  value\n");
    assert!(messages.is_empty());
    let StatementKind::AccTitle(title) = statements(&start)[0] else {
        panic!("accTitle")
    };
    assert_eq!(title.value.text, "value");
}

#[test]
fn empty_accessibility_value_at_eof() {
    let (start, messages) = parsed("journey\naccTitle:");
    assert!(messages.is_empty());
    let StatementKind::AccTitle(title) = statements(&start)[0] else {
        panic!("accTitle")
    };
    assert_eq!(title.value.text, "");
}

#[test]
fn comments_are_skipped() {
    let src = "journey\n%% whole line\n# hash line\nA: 3 # tail\nB: 4: Me %% inline\n";
    let (start, messages) = parsed(src);
    assert!(messages.is_empty());
    let kinds = statements(&start);
    assert_eq!(kinds.len(), 2);
    assert_eq!(task(kinds[0]).data.text, ": 3 ");
    assert_eq!(task(kinds[1]).data.text, ": 4: Me %% inline");
}

#[test]
fn comment_after_one_character_is_discarded_with_that_character() {
    let (start, messages) = parsed("journey\n  x%%rest\nB: 4\n");
    assert!(messages.is_empty());
    let kinds = statements(&start);
    assert_eq!(kinds.len(), 1);
    assert_eq!(task(kinds[0]).name.text, "B");
}

#[test]
fn crlf_spans_point_at_source_bytes() {
    let src = "journey\r\nA: 3: Me\r\nB: 4\r\n";
    let (start, messages) = parsed(src);
    assert!(messages.is_empty());
    let kinds = statements(&start);
    assert_eq!(slice(src, task(kinds[0]).fields[1].trimmed.span), "Me");
    let lines = &start.document.lines;
    assert_eq!(slice(src, lines[lines.len() - 2].span), "B: 4");
}

#[test]
fn directive_inside_task_keeps_spans_on_source_bytes() {
    let src = "journey\nA: 3: M%%{init: {}}%%e\n";
    let (start, messages) = parsed(src);
    assert!(messages.is_empty(), "{messages:?}");
    let field = &task(statements(&start)[0]).fields[1];
    assert_eq!(field.trimmed.text, "Me");
    assert_eq!(slice(src, field.trimmed.span), "M%%{init: {}}%%e");
}

#[test]
fn empty_document_after_header() {
    let (start, messages) = parsed("journey");
    assert!(messages.is_empty());
    assert!(start.document.lines.is_empty());
    assert_eq!(start.document.span, Span { start: 7, end: 7 });
}

#[test]
fn first_word_must_be_header() {
    let (_, messages) = parsed("pie\nA: 3");
    assert_eq!(
        messages,
        ["journey/unexpected-token: unexpected pie, expected one of: journey"]
    );
}

#[test]
fn entities_are_text_and_do_not_start_comments() {
    let src = "journey\nsection R#38;D #amp; Q\nA #35; b: 3: x#60;y\n";
    let (start, messages) = parsed(src);
    assert!(messages.is_empty(), "{messages:?}");
    let kinds = statements(&start);
    let StatementKind::Section(section) = kinds[0] else {
        panic!("section")
    };
    assert_eq!(section.text.text, "R#38;D #amp; Q");
    let entry = task(kinds[1]);
    assert_eq!(entry.name.text, "A #35; b");
    assert_eq!(entry.fields[1].trimmed.text, "x#60;y");
}

#[test]
fn malformed_entity_still_starts_a_comment() {
    let (start, messages) = parsed("journey\nA: 3 #amp\nB: 4 #;\nC: 5 ##amp; x\n");
    assert!(messages.is_empty());
    let kinds = statements(&start);
    assert_eq!(kinds.len(), 3);
    assert_eq!(task(kinds[0]).data.text, ": 3 ");
    assert_eq!(task(kinds[1]).data.text, ": 4 ");
    assert_eq!(task(kinds[2]).data.text, ": 5 ");
}
