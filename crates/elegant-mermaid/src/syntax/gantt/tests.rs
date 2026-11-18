use crate::diag::Diagnostic;

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

fn describe(kind: &StatementKind) -> String {
    match kind {
        StatementKind::DateFormat(t) => format!("dateFormat={}", t.value),
        StatementKind::InclusiveEndDates(_) => "inclusive".into(),
        StatementKind::TopAxis(_) => "topAxis".into(),
        StatementKind::AxisFormat(t) => format!("axisFormat={}", t.value),
        StatementKind::TickInterval(t) => format!("tickInterval={}", t.value),
        StatementKind::Excludes(t) => format!("excludes={}", t.value),
        StatementKind::Includes(t) => format!("includes={}", t.value),
        StatementKind::TodayMarker(t) => format!("todayMarker={}", t.value),
        StatementKind::Weekday(n) => format!("weekday={}", n.name),
        StatementKind::Weekend(n) => format!("weekend={}", n.name),
        StatementKind::Title(t) => format!("title={}", t.value),
        StatementKind::Section(t) => format!("section={}", t.value),
        StatementKind::AccTitle(n) => format!("accTitle={}", n.value.value),
        StatementKind::AccDescr(n) => format!("accDescr={}", n.value.value),
        StatementKind::AccDescrBlock(t) => format!("block={}", t.value),
        StatementKind::Task(n) => format!("task={}|{}", n.text.value, n.data.value),
        StatementKind::Click(n) => format!("click={} {:?}", n.click.value, n.order),
    }
}

fn summary(start: &Start) -> Vec<String> {
    start
        .document
        .lines
        .iter()
        .filter_map(|line| line.statement.as_ref())
        .map(|statement| describe(&statement.kind))
        .collect()
}

fn strings(items: &[&str]) -> Vec<String> {
    items.iter().map(|item| (*item).to_owned()).collect()
}

#[test]
fn directives_and_tasks() {
    let (start, diagnostics) = run(
        "gantt\n  title  My plan \n  dateFormat  YYYY-MM-DD\naxisFormat %d/%m\ntickInterval 1week\nexcludes weekends, 2014-01-10\nincludes 2014-01-11\ntodayMarker off\ninclusiveEndDates\ntopAxis\nweekday monday\nweekend friday\nsection Alpha\nDesign :a1, 2014-01-01, 30d\n  Build :after a1, 20d\n",
    );
    assert!(diagnostics.is_empty());
    assert_eq!(
        summary(&start),
        strings(&[
            "title= My plan ",
            "dateFormat= YYYY-MM-DD",
            "axisFormat=%d/%m",
            "tickInterval=1week",
            "excludes=weekends, 2014-01-10",
            "includes=2014-01-11",
            "todayMarker=off",
            "inclusive",
            "topAxis",
            "weekday=monday",
            "weekend=friday",
            "section=Alpha",
            "task=Design |:a1, 2014-01-01, 30d",
            "task=Build |:after a1, 20d",
        ])
    );
}

#[test]
fn keywords_fold_case_and_lack_boundaries() {
    let (start, diagnostics) = run("GANTT\nDATEFORMAT yyyy\nWeekday   Sunday\nTopAxisX\n");
    assert_eq!(
        messages(&diagnostics),
        strings(&["gantt/unexpected-token: unexpected \n, expected one of: taskData"])
    );
    assert_eq!(
        summary(&start),
        strings(&["dateFormat=yyyy", "weekday=sunday", "topAxis"])
    );
}

#[test]
fn task_text_beginning_with_command_word_starts_mode() {
    let (_, diagnostics) = run("gantt\ncall me :a1, 2014-01-01, 3d\n");
    assert_eq!(
        messages(&diagnostics),
        strings(&["gantt/unterminated: unterminated call"])
    );
    let (start, diagnostics) = run("gantt\ntitle plan\ntitle: x :a1, 2014-01-01, 3d\n");
    assert!(diagnostics.is_empty());
    assert_eq!(
        summary(&start),
        strings(&["title=plan", "task=title|: x :a1, 2014-01-01, 3d"])
    );
}

#[test]
fn task_without_data_is_unexpected() {
    let (start, diagnostics) = run("gantt\nlonely\nTask :a1, 2014-01-01, 3d\n");
    assert_eq!(
        messages(&diagnostics),
        strings(&["gantt/unexpected-token: unexpected \n, expected one of: taskData"])
    );
    assert_eq!(
        summary(&start),
        strings(&["task=Task |:a1, 2014-01-01, 3d"])
    );
}

#[test]
fn unknown_statements() {
    let (start, diagnostics) = run("gantt\n2014-01-01 release\n:\nsection S\n");
    assert_eq!(
        messages(&diagnostics),
        strings(&[
            "gantt/unknown-statement: unknown statement 2014-01-01",
            "gantt/unknown-statement: unknown statement :"
        ])
    );
    assert_eq!(summary(&start), strings(&["section=S"]));
    assert_eq!(diagnostics[0].span.start, 6);
    assert_eq!(diagnostics[0].span.end, 24);
}

#[test]
fn click_statements() {
    let (start, diagnostics) = run(
        "gantt\nclick a1 href \"http://x\" call fn(1, 2)\nclick a2 call go()\nclick a3 call fn(x) href \"y\"\n",
    );
    assert!(diagnostics.is_empty());
    assert_eq!(
        summary(&start),
        strings(&[
            "click=a1 [\"href\", \"callbackname\", \"callbackargs\"]",
            "click=a2 [\"callbackname\"]",
            "click=a3 [\"callbackname\", \"callbackargs\", \"href\"]",
        ])
    );
    let Some(statement) = start
        .document
        .lines
        .get(1)
        .and_then(|line| line.statement.as_ref())
    else {
        panic!("missing click statement");
    };
    let StatementKind::Click(first) = &statement.kind else {
        panic!("not a click statement");
    };
    assert_eq!(
        first.href.as_ref().map(|t| t.value.as_str()),
        Some("http://x")
    );
    assert_eq!(
        first.callback.as_ref().map(|t| t.value.as_str()),
        Some("fn")
    );
    assert_eq!(first.args.as_ref().map(|t| t.value.as_str()), Some("1, 2"));
}

#[test]
fn click_without_command_is_rejected() {
    for source in ["gantt\nclick a1\n", "gantt\nclick"] {
        let (_, diagnostics) = run(source);
        assert_eq!(
            messages(&diagnostics),
            strings(&[
                "gantt/unexpected-token: unexpected end of input, expected one of: callbackname, href"
            ]),
            "{source:?}"
        );
    }
}

#[test]
fn unterminated_delimiters() {
    for (source, want) in [
        (
            "gantt\nclick a href \"http://x",
            "gantt/unterminated: unterminated \"",
        ),
        (
            "gantt\nclick a call fn(1, 2",
            "gantt/unterminated: unterminated (",
        ),
        (
            "gantt\naccDescr {\nnever closed",
            "gantt/unterminated: unterminated {",
        ),
        (
            "gantt\nclick a call fn\nsection s",
            "gantt/unterminated: unterminated call",
        ),
    ] {
        let (_, diagnostics) = run(source);
        assert_eq!(messages(&diagnostics), strings(&[want]), "{source:?}");
    }
}

#[test]
fn accessibility() {
    let (start, diagnostics) = run(
        "gantt\naccTitle: A title\naccDescr: one\naccDescr {\n line a\n line b\n}\nsection s\n",
    );
    assert!(diagnostics.is_empty());
    assert_eq!(
        summary(&start),
        strings(&[
            "accTitle=A title",
            "accDescr=one",
            "block=line a\n line b\n",
            "section=s"
        ])
    );
}

#[test]
fn comments_and_spans_after_removal() {
    let (start, diagnostics) = run("gantt\n%% note\n  %x\nsection s\n");
    assert!(diagnostics.is_empty());
    assert_eq!(summary(&start), strings(&["section=s"]));
    let statements: Vec<_> = start
        .document
        .lines
        .iter()
        .filter_map(|line| line.statement.as_ref())
        .collect();
    assert_eq!(statements.first().map(|s| s.span.start), Some(19));
}
