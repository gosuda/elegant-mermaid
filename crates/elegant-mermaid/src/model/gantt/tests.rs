use crate::civil;
use crate::diag::{Diagnostic, Severity};
use crate::syntax::gantt::parse;
use crate::syntax::preprocess::preprocess;

use super::{Model, RowKind, resolve, split_callback_args};

fn resolved(source: &str) -> (Model, Vec<Diagnostic>) {
    let removed = preprocess(source).removed;
    let parsed = parse(source, &removed);
    let (model, mut diagnostics) = resolve(source, &parsed.document);
    let mut all = parsed.diagnostics;
    all.append(&mut diagnostics);
    (model, all)
}

fn codes(diagnostics: &[Diagnostic]) -> Vec<String> {
    diagnostics
        .iter()
        .map(|d| format!("{}: {}", d.code, d.message))
        .collect()
}

fn day(y: i64, m: i64, d: i64) -> i64 {
    civil::join(y, m, d, 0, 0, 0)
}

fn strings(items: &[&str]) -> Vec<String> {
    items.iter().map(|item| (*item).to_owned()).collect()
}

#[test]
fn chained_tasks() {
    let (m, ds) = resolved(
        "gantt\ndateFormat YYYY-MM-DD\nsection A\nOne :a1, 2014-01-01, 30d\nTwo :after a1, 20d\nThree :2014-03-01, 2014-03-05\nFour :a4, 2014-02-01, until a1\n",
    );
    assert!(ds.is_empty(), "{ds:?}");
    assert_eq!(m.tasks.len(), 4);
    assert_eq!(m.tasks[0].start_seconds, day(2014, 1, 1));
    assert_eq!(m.tasks[0].end_seconds, day(2014, 1, 31));
    assert_eq!(m.tasks[1].start_seconds, day(2014, 1, 31));
    assert_eq!(m.tasks[1].end_seconds, day(2014, 2, 20));
    assert_eq!(m.tasks[2].end_seconds, day(2014, 3, 5));
    assert!(m.tasks[2].manual_end);
    assert_eq!(m.tasks[1].id, "task1");
    let kinds: Vec<_> = m.rows.iter().map(|r| (r.kind, r.index)).collect();
    assert_eq!(
        kinds,
        vec![
            (RowKind::Section, 0),
            (RowKind::Task, 0),
            (RowKind::Task, 1),
            (RowKind::Task, 2),
            (RowKind::Task, 3)
        ]
    );
}

#[test]
fn implicit_predecessor_and_inclusive_end() {
    let (m, ds) = resolved(
        "gantt\ndateFormat YYYY-MM-DD\ninclusiveEndDates\nOne :a, 2014-01-01, 2014-01-03\nTwo :4d\n",
    );
    assert!(ds.is_empty(), "{ds:?}");
    assert_eq!(m.tasks[0].end_seconds, day(2014, 1, 4));
    assert_eq!(m.tasks[1].start_seconds, day(2014, 1, 4));
    assert_eq!(m.tasks[1].end_seconds, day(2014, 1, 8));
}

#[test]
fn weekend_exclusion_extends_end() {
    let (m, ds) =
        resolved("gantt\ndateFormat YYYY-MM-DD\nexcludes weekends\nOne :a, 2014-01-03, 3d\n");
    assert!(ds.is_empty(), "{ds:?}");
    assert_eq!(m.tasks[0].end_seconds, day(2014, 1, 8));
    assert!(m.tasks[0].has_render_end);
    assert_eq!(m.tasks[0].render_end, day(2014, 1, 8));
}

#[test]
fn exclusion_limit() {
    let (_, ds) = resolved(
        "gantt\ndateFormat YYYY-MM-DD\nexcludes monday tuesday wednesday thursday friday saturday sunday\nOne :a, 2014-01-03, 3d\n",
    );
    assert_eq!(
        codes(&ds),
        strings(&["gantt/exclusion-limit: cannot find a non-excluded end within 10000 days"])
    );
}

#[test]
fn duration_units() {
    for (text, want) in [
        ("90s", 90),
        ("2m", 120),
        ("1.5h", 5400),
        ("1500ms", 1),
        ("2w", 14 * 86400),
        ("1.5d", 2 * 86400),
        ("0.4d", 0),
        ("1M", 31 * 86400),
        ("1y", 365 * 86400),
    ] {
        let (m, ds) = resolved(&format!(
            "gantt\ndateFormat YYYY-MM-DD\nOne :a, 2014-01-01, {text}\n"
        ));
        assert!(ds.is_empty(), "{text}: {ds:?}");
        assert_eq!(m.tasks[0].end_seconds, day(2014, 1, 1) + want, "{text}");
    }
    let (m, _) = resolved("gantt\ndateFormat YYYY-MM-DD\nOne :a, 2014-01-31, 1M\n");
    assert_eq!(m.tasks[0].end_seconds, day(2014, 2, 28));
    let (m, _) = resolved("gantt\ndateFormat YYYY-MM-DD\nOne :a, 2012-02-29, 1y\n");
    assert_eq!(m.tasks[0].end_seconds, day(2013, 2, 28));
}

#[test]
fn invalid_end_keeps_start() {
    let (m, ds) = resolved("gantt\ndateFormat YYYY-MM-DD\nOne :a, 2014-01-01, soon\n");
    assert_eq!(
        codes(&ds),
        strings(&[
            "gantt/invalid-end: soon is neither a date nor a duration; task has zero duration"
        ])
    );
    assert_eq!(ds[0].severity, Severity::Warning);
    assert_eq!(m.tasks[0].start_seconds, m.tasks[0].end_seconds);
}

#[test]
fn reference_warnings_and_epoch_fallback() {
    let (m, ds) = resolved(
        "gantt\ndateFormat YYYY-MM-DD\nOne :a, after nope other, 2d\nTwo :b, 2014-01-01, until missing\n",
    );
    assert_eq!(
        codes(&ds),
        strings(&[
            "gantt/unknown-task-reference: after references unknown task id nope",
            "gantt/unknown-task-reference: after references unknown task id other",
            "gantt/unknown-task-reference: until references unknown task id missing",
        ])
    );
    assert_eq!(m.tasks[0].start_seconds, 0);
    assert_eq!(m.tasks[0].end_seconds, 2 * 86400);
    assert_eq!(m.tasks[1].end_seconds, 0);
}

#[test]
fn errors() {
    for (source, want) in [
        (
            "gantt\nOne :3d\n",
            "gantt/predecessor-missing: task has no preceding task",
        ),
        (
            "gantt\ndateFormat YYYY-MM-DD\nOne :a, 2014-13-01, 3d\n",
            "gantt/invalid-date: invalid date 2014-13-01",
        ),
        (
            "gantt\nOne :crit\n",
            "gantt/task-data-invalid: task requires one, two, or three data fields after tags",
        ),
        (
            "gantt\nOne :a, 2014-01-01, 3d, 4d\n",
            "gantt/task-data-invalid: task requires one, two, or three data fields after tags",
        ),
        (
            "gantt\nOne :a, after b, 1d\nTwo :b, after a, 1d\n",
            "gantt/unresolved-task: task dates remain unresolved after eleven passes",
        ),
    ] {
        let (_, ds) = resolved(source);
        assert_eq!(
            codes(&ds).first().map(String::as_str),
            Some(want),
            "{source:?}"
        );
    }
}

#[test]
fn tags_and_data_arity() {
    let (m, ds) = resolved(
        "gantt\ndateFormat YYYY-MM-DD\nOne :done, crit, id1, 2014-01-01, 1d\nTwo :milestone, 2014-01-03, 0d\nThree :vert, v1, 2014-01-02, 0d\n",
    );
    assert!(ds.is_empty(), "{ds:?}");
    assert!(m.tasks[0].done && m.tasks[0].crit && !m.tasks[0].active);
    assert_eq!(m.tasks[0].id, "id1");
    assert!(m.tasks[1].milestone);
    assert!(m.tasks[2].vert);
    let orders: Vec<_> = m.tasks.iter().map(|t| t.order).collect();
    assert_eq!(orders, vec![Some(0), Some(1), None]);
}

#[test]
fn timestamp_formats() {
    let (m, ds) = resolved("gantt\ndateFormat X\nOne :a, 1700000000, 1700003600\n");
    assert!(ds.is_empty(), "{ds:?}");
    assert_eq!(m.tasks[0].start_seconds, 1_700_000);
    assert_eq!(m.tasks[0].end_seconds, 1_700_003_600);
    let (m, ds) = resolved("gantt\ndateFormat x\nOne :a, 1700000000123, 1700000003123\n");
    assert!(ds.is_empty(), "{ds:?}");
    assert_eq!(m.tasks[0].start_seconds, 1_700_000_000);
    assert_eq!(m.tasks[0].end_seconds, 1_700_000_003);
}

#[test]
fn fallback_dates_without_date_format() {
    let (m, ds) = resolved("gantt\nOne :a, 2014-01-01, 2d\n");
    assert!(ds.is_empty(), "{ds:?}");
    assert_eq!(m.tasks[0].start_seconds, day(2014, 1, 1));
}

#[test]
fn axis_and_tick_directives() {
    let (_, ds) =
        resolved("gantt\naxisFormat %L\ntickInterval 5millisecond\nodd :a, 2014-01-01, 1d\n");
    assert_eq!(
        codes(&ds)[..2],
        strings(&[
            "gantt/axis-format-unsupported: axis format contains unsupported code %L; using %Y-%m-%d",
            "gantt/tick-interval-unsupported: millisecond tick interval is not supported; using automatic ticks",
        ])[..]
    );
    let (_, ds) = resolved("gantt\ntodayMarker off\n");
    assert_eq!(
        codes(&ds),
        strings(&["gantt/today-marker-ignored: today marker is ignored"])
    );
    assert_eq!(ds[0].severity, Severity::Info);
}

#[test]
fn click_links_and_callbacks() {
    let (m, ds) = resolved(
        "gantt\ndateFormat YYYY-MM-DD\nOne :a1, 2014-01-01, 1d\nclick a1 href \"https://example.com\" call run(\"x, y\", 2)\nclick a1 href \"javascript:alert(1)\"\nclick nope href \"https://other\"\n",
    );
    assert_eq!(
        codes(&ds),
        strings(&[
            "interaction/callback-ignored: callback run is ignored",
            "interaction/unsafe-url: link URL is not allowed",
        ])
    );
    assert_eq!(m.tasks[0].link.as_deref(), Some("https://example.com"));
    let args = m.clicks[0].callback.as_ref().map(|c| c.args.clone());
    assert_eq!(args, Some(strings(&["x, y", "2"])));
}

#[test]
fn config_and_frontmatter() {
    let (m, ds) = resolved(
        "---\ntitle: \"Plan #35;\"\nconfig:\n  gantt:\n    barHeight: 30\n    topAxis: true\n    weekday: monday\n    axisFormat: \"%d\"\n---\ngantt\n",
    );
    assert!(ds.is_empty(), "{ds:?}");
    assert_eq!(m.title_label, "Plan #");
    assert_eq!(m.config_integer("barHeight"), Some(30));
    assert!(m.config_bool("topAxis"));
    assert_eq!(m.config_string("weekday"), Some("monday"));
    assert_eq!(m.effective_weekday(), "monday");
    assert_eq!(m.effective_axis_format(), "%d");
}

#[test]
fn callback_args_split_on_unquoted_commas() {
    assert_eq!(
        split_callback_args("a, \"b, c\", \"\""),
        strings(&["a", "b, c", ""])
    );
}
