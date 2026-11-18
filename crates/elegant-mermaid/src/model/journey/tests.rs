use crate::diag::Diagnostic;
use crate::syntax::journey::parse;
use crate::syntax::preprocess::preprocess;

use super::{Model, resolve};

fn run(source: &str) -> (Model, Vec<Diagnostic>) {
    let removed = preprocess(source).removed;
    let parsed = parse(source, &removed);
    let (model, mut diagnostics) = resolve(source, &parsed.document);
    diagnostics.extend(parsed.diagnostics);
    (model, diagnostics)
}

fn messages(diagnostics: &[Diagnostic]) -> Vec<String> {
    diagnostics
        .iter()
        .map(|d| format!("{}: {}", d.code, d.message))
        .collect()
}

fn strings(items: &[&str]) -> Vec<String> {
    items.iter().map(|item| (*item).to_owned()).collect()
}

#[test]
fn sections_tasks_and_actors() {
    let source = "journey\ntitle  My day\nsection Go\n  Make tea: 5: Me\n  Do work: 1: Me, Cat\nsection Home\n  Sit: 5\n";
    let (model, diagnostics) = run(source);
    assert!(diagnostics.is_empty());
    assert_eq!(model.title, " My day");
    assert_eq!(model.title_label, "My day");
    assert_eq!(model.sections.len(), 2);
    assert_eq!(model.tasks.len(), 3);
    assert_eq!(model.tasks[0].section, "Go");
    assert_eq!(model.tasks[2].section, "Home");
    assert_eq!(model.tasks[0].score, 5);
    assert_eq!(model.tasks[1].people, strings(&["Me", "Cat"]));
    assert!(model.tasks[2].people.is_empty());
    assert_eq!(model.actors, strings(&["Cat", "Me"]));
    assert_eq!(model.tasks[0].name, "Make tea");
    assert_eq!(model.tasks[2].label, "Sit");
}

#[test]
fn tasks_before_any_section_stay_in_the_empty_section() {
    let (model, diagnostics) = run("journey\nA: 3\nsection S\nB: 4\n");
    assert!(diagnostics.is_empty());
    assert_eq!(model.tasks[0].section, "");
    assert_eq!(model.tasks[1].section, "S");
}

#[test]
fn duplicate_sections_remain_duplicate() {
    let (model, diagnostics) = run("journey\nsection S\nsection S\nA: 3\n");
    assert!(diagnostics.is_empty());
    assert_eq!(model.sections.len(), 2);
}

#[test]
fn section_and_task_names_are_not_trimmed_but_labels_are() {
    let (model, diagnostics) = run("journey\nsection  Wide \n  register slug : 5: x\n");
    assert!(diagnostics.is_empty());
    assert_eq!(model.sections[0].name, " Wide ");
    assert_eq!(model.sections[0].label, "Wide");
    assert_eq!(model.tasks[0].name, "register slug ");
    assert_eq!(model.tasks[0].label, "register slug");
}

#[test]
fn people_keep_order_duplicates_and_empty_names() {
    let (model, diagnostics) = run("journey\nA: 3: Bob, ,bob,Bob :ignored\nB: 3:\nC: 3\n");
    assert!(diagnostics.is_empty());
    assert_eq!(model.tasks[0].people, strings(&["Bob", "", "bob", "Bob"]));
    assert_eq!(model.tasks[1].people, strings(&[""]));
    assert!(model.tasks[2].people.is_empty());
    assert_eq!(model.actors, strings(&["", "Bob", "bob"]));
}

#[test]
fn actors_sort_by_utf16_code_units() {
    let (model, diagnostics) = run("journey\nA: 3: \u{ffee}, \u{1F600}, z\n");
    assert!(diagnostics.is_empty());
    assert_eq!(model.actors, strings(&["z", "\u{1F600}", "\u{ffee}"]));
}

#[test]
fn score_must_be_an_integer_in_range() {
    let big = "9".repeat(23);
    let cases = [
        (
            "abc",
            "journey/unexpected-token: unexpected abc, expected one of: integer".to_owned(),
        ),
        (
            "",
            "journey/unexpected-token: unexpected , expected one of: integer".to_owned(),
        ),
        (
            "3.5",
            "journey/unexpected-token: unexpected 3.5, expected one of: integer".to_owned(),
        ),
        (
            "1e2",
            "journey/unexpected-token: unexpected 1e2, expected one of: integer".to_owned(),
        ),
        (
            "+-3",
            "journey/unexpected-token: unexpected +-3, expected one of: integer".to_owned(),
        ),
        (
            "0",
            "journey/score-out-of-range: score 0 is outside the range 1 to 5".to_owned(),
        ),
        (
            "6",
            "journey/score-out-of-range: score 6 is outside the range 1 to 5".to_owned(),
        ),
        (
            "-1",
            "journey/score-out-of-range: score -1 is outside the range 1 to 5".to_owned(),
        ),
        (
            "007",
            "journey/score-out-of-range: score 007 is outside the range 1 to 5".to_owned(),
        ),
        (
            &big,
            format!("journey/score-out-of-range: score {big} is outside the range 1 to 5"),
        ),
        (
            &format!("-{big}"),
            format!("journey/score-out-of-range: score -{big} is outside the range 1 to 5"),
        ),
    ];
    for (field, want) in cases {
        let (_, diagnostics) = run(&format!("journey\nA: {field}\n"));
        assert_eq!(messages(&diagnostics), [want], "field {field:?}");
    }
}

#[test]
fn score_accepts_signs_and_leading_zeros() {
    let (model, diagnostics) = run("journey\nA: +5\nB: 003\nC:  4 \n");
    assert!(diagnostics.is_empty());
    let scores: Vec<i64> = model.tasks.iter().map(|t| t.score).collect();
    assert_eq!(scores, [5, 3, 4]);
}

#[test]
fn score_diagnostic_spans_cover_the_trimmed_field() {
    let source = "journey\nA:  9 : Me\nB: \n";
    let (_, diagnostics) = run(source);
    assert_eq!(diagnostics.len(), 2);
    let first = diagnostics[0].span;
    assert_eq!(&source[first.start..first.end], "9");
    assert_eq!(diagnostics[1].span.start, diagnostics[1].span.end);
}

#[test]
fn accessibility_and_title_replace_previous_values() {
    let source = "journey\ntitle one\ntitle two\naccTitle:  first \naccTitle: second\naccDescr: d1\naccDescr {\n  line one\n    line two\n}\n";
    let (model, diagnostics) = run(source);
    assert!(diagnostics.is_empty());
    assert_eq!(model.title, "two");
    assert_eq!(model.acc_title, "second");
    assert_eq!(model.acc_descr, "line one\nline two");
}

#[test]
fn labels_decode_entities() {
    let (model, diagnostics) = run("journey\nsection R#38;D #amp; Q\nA #35; b: 3\n");
    assert!(diagnostics.is_empty());
    assert_eq!(model.sections[0].label, "R&D & Q");
    assert_eq!(model.tasks[0].label, "A # b");
}

#[test]
fn honoured_config_keys() {
    let source = "%%{init: {\"journey\": {\"width\": 200, \"height\": 60, \"diagramMarginX\": 10, \"ignored\": 3}}}%%\njourney\nA: 3\n";
    let (model, diagnostics) = run(source);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    assert_eq!(model.config.width, Some(200));
    assert_eq!(model.config.height, Some(60));
    assert_eq!(model.config.margin_x, Some(10));
}

#[test]
fn unparsed_statements_create_no_tasks() {
    let (model, diagnostics) = run("journey\nLonely\n; x\nA: 3\n");
    assert_eq!(diagnostics.len(), 2);
    assert_eq!(model.tasks.len(), 1);
}
