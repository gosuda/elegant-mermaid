use super::ast::{EmFrame, EventModel};
use super::parse;
use crate::diag::Diagnostic;
use crate::syntax::preprocess::preprocess;

fn parsed(source: &str) -> (EventModel, Vec<Diagnostic>) {
    let prep = preprocess(source);
    let result = parse(source, &prep.removed);
    (result.document, result.diagnostics)
}

fn rendered(source: &str, diagnostics: &[Diagnostic]) -> Vec<String> {
    diagnostics
        .iter()
        .map(|d| {
            format!(
                "{} | {} | {}",
                d.code,
                d.message,
                source.get(d.span.start..d.span.end).unwrap_or("?")
            )
        })
        .collect()
}

fn names(document: &EventModel) -> Vec<&str> {
    document
        .frames
        .iter()
        .map(|frame| frame.fields().name.text.as_str())
        .collect()
}

#[test]
fn diagnostics_match_the_grammar_document() {
    let cases: &[(&str, &[&str])] = &[
        (
            "eventmodeling\ntitle My Title\ntf 01 ui A\n",
            &["eventmodeling/unknown-statement | unknown statement title | title My Title"],
        ),
        (
            "eventmodeling\ntf 01 ui A; tf 02 cmd B\n",
            &["eventmodeling/unknown-statement | unknown statement ; | ; "],
        ),
        (
            "eventmodeling\ntf 01 ui\ntf 02 cmd B\n",
            &["eventmodeling/unexpected-token | unexpected tf, expected one of: EM_ID | tf"],
        ),
        (
            "eventmodeling\ntf 01 ui A ->>\ntf 02 cmd B\n",
            &["eventmodeling/unexpected-token | unexpected tf, expected one of: EM_FID | tf"],
        ),
        (
            "eventmodeling\ntf 01 foo A\n",
            &[
                "eventmodeling/unexpected-token | unexpected foo, expected one of: cmd, command, event, evt, pcr, processor, readmodel, rmo, ui | foo",
            ],
        ),
        (
            "eventmodeling\ntf 01 ui A [[N",
            &["eventmodeling/unterminated | unterminated [[ | [[N"],
        ),
        (
            "eventmodeling\ntf 01 ui A [[N tf 02 ui B",
            &["eventmodeling/unexpected-token | unexpected tf, expected one of: ]] | tf"],
        ),
        (
            "eventmodeling\ntf 01 ui A `json",
            &["eventmodeling/unterminated | unterminated ` | `json"],
        ),
        (
            "eventmodeling\ntf 01 ui A `foo` { a }\n",
            &[
                "eventmodeling/unexpected-token | unexpected foo, expected one of: figma, html, jsobj, json, md, salt, text, uri | foo",
            ],
        ),
        (
            "eventmodeling\ntf 01 ui A \"x\ntf 02 ui B\n",
            &["eventmodeling/unterminated | unterminated \" | \"x\ntf 02 ui B\n"],
        ),
        (
            "eventmodeling\n/* open\ntf 01 ui A\n",
            &["eventmodeling/unterminated | unterminated /* | /* open\ntf 01 ui A\n"],
        ),
        (
            "eventmodeling\ndata D { a }\n",
            &[
                "eventmodeling/unexpected-token | unexpected { a }, expected one of: EM_DATA_BLOCK, ` | { a }",
            ],
        ),
        (
            "eventmodeling\ngwt 01 given ui A then evt B tf 02 ui C\n",
            &[],
        ),
        (
            "eventmodeling\ngwt 01 then evt B\n",
            &["eventmodeling/unexpected-token | unexpected then, expected one of: given | then"],
        ),
        (
            "eventmodeling\nfoo bar baz\ntf 01 ui A\n",
            &["eventmodeling/unknown-statement | unknown statement foo | foo bar baz"],
        ),
        (
            "eventmodeling foo\ntf 01 ui A\n",
            &["eventmodeling/unknown-statement | unknown statement foo | foo"],
        ),
        (
            "eventmodeling;\ntf 01 ui A\n",
            &[
                "eventmodeling/unexpected-token | unexpected eventmodeling, expected one of: eventmodeling | eventmodeling",
            ],
        ),
        (
            "eventmodeling\ntf 01 ui A\n  ui B\n",
            &["eventmodeling/unknown-statement | unknown statement ui | ui B"],
        ),
        (
            "eventmodeling\ntf 1000 ui A\n",
            &[
                "eventmodeling/unexpected-token | unexpected 0, expected one of: cmd, command, event, evt, pcr, processor, readmodel, rmo, ui | 0",
            ],
        ),
    ];
    for (source, want) in cases {
        let (_, diagnostics) = parsed(source);
        assert_eq!(rendered(source, &diagnostics), *want, "{source:?}");
    }
}

#[test]
fn end_of_input_inside_a_delimiter_reports_only_unterminated() {
    for source in [
        "eventmodeling\ntf 01 ui A [[",
        "eventmodeling\ntf 01 ui A [[N",
        "eventmodeling\ntf 01 ui A `",
        "eventmodeling\ntf 01 ui A `json",
    ] {
        let (_, diagnostics) = parsed(source);
        assert_eq!(diagnostics.len(), 1, "{source}");
        assert_eq!(
            diagnostics[0].code, "eventmodeling/unterminated",
            "{source}"
        );
        assert_eq!(diagnostics[0].span.end, source.len(), "{source}");
    }
}

#[test]
fn end_of_input_shows_a_zero_width_span() {
    let source = "eventmodeling\ntf 01 ui A ->>";
    let (_, diagnostics) = parsed(source);
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, "eventmodeling/unexpected-token");
    assert_eq!(diagnostics[0].span.start, source.len());
    assert_eq!(diagnostics[0].span.end, source.len());
}

#[test]
fn recovery_keeps_later_statements() {
    let source = "eventmodeling\ntf 01 ui A\nbogus line here\ntf 02 cmd B ->>\ntf 03 evt C\nentity X\ntf 04 ui D; tf 05 ui E\n";
    let (document, diagnostics) = parsed(source);
    assert_eq!(diagnostics.len(), 3, "{diagnostics:?}");
    assert_eq!(names(&document), ["01", "03", "04", "05"]);
    assert_eq!(document.model_entities.len(), 1);
}

#[test]
fn frames_are_free_form() {
    let source = "eventmodeling tf 01 ui A tf 02\ncmd B\n->> 01 { x } rf 03 evt C";
    let (document, diagnostics) = parsed(source);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    assert_eq!(document.frames.len(), 3);
    let second = document.frames[1].fields();
    assert_eq!(second.name.text, "02");
    assert_eq!(second.source_frames[0].text, "01");
    assert_eq!(second.data_inline_value.as_ref().unwrap().text, "{ x }");
    assert!(document.frames[2].is_reset());
}

#[test]
fn frame_spans_and_fields() {
    let source = "eventmodeling\ntf 02 cmd Inv . Add ->> 01 ->> 07 [[Info]] `json` {a}   // note\ntimeframe 03 evt X";
    let (document, diagnostics) = parsed(source);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    let first = document.frames[0].fields();
    let slice = |span: crate::source::Span| source.get(span.start..span.end).unwrap();
    assert_eq!(
        slice(first.span),
        "tf 02 cmd Inv . Add ->> 01 ->> 07 [[Info]] `json` {a}"
    );
    assert_eq!(slice(first.keyword), "tf");
    assert_eq!(first.entity_identifier.text, "Inv.Add");
    assert_eq!(slice(first.entity_identifier.span), "Inv . Add");
    assert_eq!(first.model_entity_type.text, "cmd");
    assert_eq!(first.data_reference.as_ref().unwrap().text, "Info");
    assert_eq!(first.data_type.as_ref().unwrap().text, "json");
    assert_eq!(slice(first.data_inline_value.as_ref().unwrap().span), "{a}");
    assert_eq!(first.source_frames.len(), 2);
    let last = document.frames[1].fields();
    assert_eq!(slice(last.span), "timeframe 03 evt X");
    assert!(last.data_type.is_none() && last.data_reference.is_none());
    assert!(last.data_inline_value.is_none());
}

#[test]
fn statement_lists() {
    let source = "eventmodeling\nentity A.B\ndata D `json` {\n x\n}\nnote 01 {\n y\n}\ngwt 01 given ui A cmd B when evt C then rmo D pcr E\ntf 01 ui A\n";
    let (document, diagnostics) = parsed(source);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    assert_eq!(document.model_entities[0].name.text, "A.B");
    let data = &document.data_entities[0];
    assert_eq!(data.name.text, "D");
    assert_eq!(data.data_type.as_ref().unwrap().text, "json");
    assert_eq!(data.data_block_value.text, "{\n x\n}\n");
    assert_eq!(document.note_entities[0].source_frame.text, "01");
    let gwt = &document.gwt_entities[0];
    assert_eq!(gwt.given_statements.len(), 2);
    assert_eq!(gwt.when_statements.len(), 1);
    assert_eq!(gwt.then_statements.len(), 2);
    assert_eq!(gwt.then_statements[1].model_entity_type.text, "pcr");
    assert_eq!(gwt.then_statements[1].entity_identifier.text, "E");
}

#[test]
fn block_data_boundaries() {
    let accepted = |source: &str| parsed(source).1.is_empty();
    assert!(accepted("eventmodeling\ndata D {\n a\n} \n"));
    assert!(accepted("eventmodeling\ndata D {\n a\n}"));
    assert!(!accepted("eventmodeling\ndata D {\n a\n}x\n"));
    assert!(!accepted("eventmodeling\ndata D {\n a\n }\n"));
    let (document, _) = parsed("eventmodeling\ndata D {\n}\n}\n");
    assert_eq!(document.data_entities[0].data_block_value.text, "{\n}\n}\n");
    let (document, _) = parsed("eventmodeling\ndata D {\r\n a\r\n}\r\ntf 01 ui A");
    assert_eq!(
        document.data_entities[0].data_block_value.text,
        "{\r\n a\r\n}\r\n"
    );
    assert_eq!(document.frames.len(), 1);
}

#[test]
fn inline_data_is_greedy_to_the_last_closer_on_the_line() {
    let (document, diagnostics) =
        parsed("eventmodeling\ntf 01 evt A { a } tf 02 evt B { b }\ntf 03 evt C\n");
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    assert_eq!(document.frames.len(), 2);
    assert_eq!(
        document.frames[0]
            .fields()
            .data_inline_value
            .as_ref()
            .unwrap()
            .text,
        "{ a } tf 02 evt B { b }"
    );
}

#[test]
fn directives_and_frontmatter_are_removed() {
    let source = "---\ntitle: x\n---\n%%{init: {\"theme\": \"dark\"}}%%\neventmodeling\ntf 01 ui A %%{init: {}}%%\ntf 02 cmd B\n";
    let (document, diagnostics) = parsed(source);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    assert_eq!(document.frames.len(), 2);
    assert!(
        source
            .get(document.header.span.start..)
            .unwrap()
            .starts_with("eventmodeling")
    );
}

#[test]
fn keywords_are_reserved_and_identifiers_keep_prefixes() {
    assert!(
        parsed("eventmodeling\ntf 01 ui datax\ntf 02 ui uiX\ntf 03 ui tfx\n")
            .1
            .is_empty()
    );
    for name in ["data", "text", "tf", "ui", "given", "entity"] {
        let source = format!("eventmodeling\ntf 01 ui {name}\n");
        assert!(!parsed(&source).1.is_empty(), "{name}");
    }
}

#[test]
fn time_frame_variants_are_distinguished() {
    let (document, _) = parsed("eventmodeling\ntf 01 ui A\nresetframe 02 ui B\n");
    assert!(matches!(document.frames[0], EmFrame::TimeFrame(_)));
    assert!(matches!(document.frames[1], EmFrame::ResetFrame(_)));
}
