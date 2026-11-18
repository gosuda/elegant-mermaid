use crate::diag::Diagnostic;
use crate::source::Span;
use crate::syntax::preprocess::preprocess;
use crate::syntax::timeline::parse;

use super::{Model, resolve};

fn run(source: &str) -> (Model, Vec<Diagnostic>) {
    let removed = preprocess(source).removed;
    let parsed = parse(source, &removed);
    let (model, mut diagnostics) = resolve(source, &parsed.document);
    diagnostics.extend(parsed.diagnostics);
    (model, diagnostics)
}

fn outline(model: &Model) -> Vec<String> {
    model
        .periods
        .iter()
        .map(|period| {
            let mut line = format!("{}|{}", period.section_name, period.text);
            for event in &period.events {
                line.push('|');
                line.push_str(&event.text);
            }
            line
        })
        .collect()
}

fn strings(items: &[&str]) -> Vec<String> {
    items.iter().map(|item| (*item).to_owned()).collect()
}

#[test]
fn direction_defaults_to_lr() {
    for (source, want) in [
        ("timeline", "LR"),
        ("timeline LR", "LR"),
        ("timeline TD", "TD"),
        ("timeline td", "TD"),
    ] {
        let (model, diagnostics) = run(source);
        assert!(diagnostics.is_empty(), "{source}");
        assert_eq!(model.direction, want, "{source}");
        assert_eq!(model.vertical(), want == "TD", "{source}");
    }
}

#[test]
fn periods_events_and_sections_follow_declaration_order() {
    let (model, diagnostics) =
        run("timeline\nsection A\n2002 : x : y\n  : z\n2003\nsection B\n2004 : w\n");
    assert!(diagnostics.is_empty());
    assert_eq!(
        outline(&model),
        strings(&["A|2002 |x |y|z", "A|2003", "B|2004 |w"])
    );
    assert_eq!(
        model.periods.iter().map(|p| p.section).collect::<Vec<_>>(),
        vec![Some(0), Some(0), Some(1)]
    );
    assert_eq!(model.sections[0].name, "A");
    assert_eq!(model.sections[1].name, "B");
}

#[test]
fn section_names_are_not_trimmed_and_duplicates_stay_distinct() {
    let (model, diagnostics) = run("timeline\nsection  A \n1\nsection  A \n2\n");
    assert!(diagnostics.is_empty());
    assert_eq!(model.sections[0].name, " A ");
    assert_eq!(model.sections[1].name, " A ");
    assert_eq!(model.sections[0].label, "A");
    assert_eq!(model.sections[1].label, "A");
    assert_eq!(model.periods[0].section, Some(0));
    assert_eq!(model.periods[1].section, Some(1));
}

#[test]
fn periods_before_the_first_section_have_no_section() {
    let (model, diagnostics) = run("timeline\n1\nsection S\n2\n");
    assert!(diagnostics.is_empty());
    assert_eq!(model.periods[0].section, None);
    assert_eq!(model.periods[1].section, Some(0));
    assert_eq!(model.periods[0].section_name, "");
}

#[test]
fn event_after_a_section_still_belongs_to_the_preceding_period() {
    let (model, diagnostics) = run("timeline\np : a\nsection S\n: b\n");
    assert!(diagnostics.is_empty());
    assert_eq!(outline(&model), strings(&["|p |a|b"]));
    assert_eq!(model.periods[0].section, None);
}

#[test]
fn event_without_a_period_is_reported() {
    let (model, diagnostics) = run("timeline\nsection S\n: lonely\np\n");
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, "timeline/event-without-period");
    assert_eq!(diagnostics[0].message, "event has no preceding period");
    assert_eq!(diagnostics[0].span, Span { start: 19, end: 27 });
    assert_eq!(outline(&model), strings(&["S|p"]));
}

#[test]
fn title_keeps_its_leading_whitespace_and_the_label_trims() {
    let (model, diagnostics) = run("timeline\ntitle   Social media \ntitle  last wins\n");
    assert!(diagnostics.is_empty());
    assert_eq!(model.title, " last wins");
    assert_eq!(model.title_label, "last wins");
}

#[test]
fn accessibility_text_follows_the_common_database() {
    let (model, diagnostics) = run(
        "timeline\naccTitle:   spaced title  \naccDescr {\n   line one\n \n     line two  \n}\n",
    );
    assert!(diagnostics.is_empty());
    assert_eq!(model.acc_title, "spaced title");
    assert_eq!(model.acc_descr, "line one\nline two");
    let (model, _) = run("timeline\naccDescr: first\naccDescr {second}\naccDescr {  }\n");
    assert_eq!(model.acc_descr, "second");
}

#[test]
fn labels_decode_entities_and_trim_without_changing_the_text() {
    let (model, diagnostics) =
        run("timeline\nsection #35;s#amp;\n  2002 : a #35;#9731; b #foo; #0; #x\n");
    assert!(diagnostics.is_empty());
    assert_eq!(model.sections[0].label, "#s&");
    assert_eq!(model.periods[0].label, "2002");
    assert_eq!(
        model.periods[0].events[0].label,
        "a #\u{2603} b #foo; #0; #x"
    );
    assert_eq!(
        model.periods[0].events[0].text,
        "a #35;#9731; b #foo; #0; #x"
    );
}

#[test]
fn html_serialisation_is_not_reproduced() {
    let (model, diagnostics) = run("timeline\ntitle a & b<br>c\n");
    assert!(diagnostics.is_empty());
    assert_eq!(model.title_label, "a & b<br>c");
    let (model, diagnostics) = run("timeline\ntitle \u{a0}<br>x\n");
    assert!(diagnostics.is_empty());
    assert_eq!(model.title, "\u{a0}<br>x");
    let (model, diagnostics) = run("timeline\ntitle a<b\n");
    assert!(diagnostics.is_empty());
    assert_eq!(model.title, "a<b");
    let (model, diagnostics) = run("timeline\naccDescr {\na\n\u{a0}<br>b\n}\n");
    assert!(diagnostics.is_empty());
    assert_eq!(model.acc_descr, "a\n<br>b");
    let (model, diagnostics) = run("timeline\naccDescr: a\u{a0}<br>b\n");
    assert!(diagnostics.is_empty());
    assert_eq!(model.acc_descr, "a\u{a0}<br>b");
}

#[test]
fn bare_comment_line_never_becomes_payload() {
    let (model, diagnostics) = run("timeline\na:\n%%\nb\n");
    assert!(diagnostics.is_empty());
    assert_eq!(outline(&model), strings(&["|a|b"]));
    let (model, diagnostics) = run("timeline\na:\n\n%%\nb\n");
    assert!(diagnostics.is_empty());
    assert_eq!(outline(&model), strings(&["|a|b"]));
    let (model, diagnostics) = run("timeline\ntitle\n%%\nx\n");
    assert!(diagnostics.is_empty());
    assert_eq!(model.title, "x");
    let (model, diagnostics) = run("timeline\naccDescr {\na\n%%\nb\n}\n");
    assert!(diagnostics.is_empty());
    assert_eq!(model.acc_descr, "a\nb");
    for (source, code) in [
        ("timeline\na :\n%%", "timeline/unknown-statement"),
        ("timeline\naccTitle:\n\t%%", "timeline/unexpected-token"),
        ("timeline\naccDescr:\n%%", "timeline/unexpected-token"),
        ("timeline\naccDescr:\n\n%%\n", "timeline/unexpected-token"),
    ] {
        let (_, diagnostics) = run(source);
        assert_eq!(diagnostics.len(), 1, "{source:?}");
        assert_eq!(diagnostics[0].code, code, "{source:?}");
    }
}
