use super::{
    ast::{Line, StatementKind},
    lexer::lex,
    parse,
};
use crate::source::Span;

fn kinds(source: &str) -> Vec<&'static str> {
    let parsed = parse(source, &[]);
    parsed
        .document
        .document
        .lines
        .iter()
        .filter_map(|line| line.statement.as_ref().map(|s| kind_name(&s.kind)))
        .collect()
}

fn kind_name(kind: &StatementKind<'_>) -> &'static str {
    match kind {
        StatementKind::Participant(_) => "participant",
        StatementKind::Signal(_) => "signal",
        StatementKind::Autonumber { .. } => "autonumber",
        StatementKind::Activate { .. } => "activate",
        StatementKind::Deactivate { .. } => "deactivate",
        StatementKind::Note(_) => "note",
        StatementKind::Links { .. } => "links",
        StatementKind::Link { .. } => "link",
        StatementKind::Properties { .. } => "properties",
        StatementKind::Details { .. } => "details",
        StatementKind::Title { .. } => "title",
        StatementKind::Accessibility { .. } => "accessibility",
        StatementKind::Box(_) => "box",
        StatementKind::Control(_) => "control",
    }
}

fn codes(source: &str) -> Vec<String> {
    parse(source, &[])
        .diagnostics
        .iter()
        .map(|d| d.code.to_string())
        .collect()
}

#[test]
fn lexes_arrow_tokens_in_table_order() {
    let tokens = lex("A->>B: x\n", &[]);
    let arrows: Vec<&str> = tokens
        .iter()
        .filter(|t| t.kind.starts_with("SOLID_ARROW") || t.kind == "DOTTED_ARROW")
        .map(|t| t.kind)
        .collect();
    assert_eq!(arrows, ["SOLID_ARROW"]);
    let tokens = lex("A/|--B: x\n", &[]);
    assert!(
        tokens
            .iter()
            .any(|t| t.kind == "SOLID_ARROW_TOP_REVERSE_DOTTED")
    );
}

#[test]
fn keywords_fold_case_and_end_at_boundary() {
    assert_eq!(
        kinds("sequenceDiagram\nLOOP every day\nA->>B: x\nEND\n"),
        ["control"]
    );
    assert_eq!(kinds("sequenceDiagram\nNotes->>B: x\n"), ["signal"]);
    assert_eq!(kinds("sequenceDiagram\npar_over X\nEND\n"), ["control"]);
    assert_eq!(
        kinds("sequenceDiagram\ncritical X\noption Y\nend\n"),
        ["control"]
    );
    assert_eq!(kinds("sequenceDiagram\nendpoint->>B: x\n"), ["signal"]);
    assert_eq!(kinds("sequenceDiagram\nLink->>B: x\n"), ["signal"]);
    assert_eq!(
        kinds("sequenceDiagram\nlink A: Dashboard @ https://x.dev\n"),
        ["link"]
    );
    assert_eq!(
        codes("sequenceDiagram\noption X\nend\n"),
        ["sequence/unknown-statement", "sequence/unknown-statement"]
    );
}

#[test]
fn stray_invalid_token_is_a_blank_line() {
    let parsed = parse("sequenceDiagram\n<\nA->>B: x\n", &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
}

#[test]
fn invalid_participant_id_is_rejected() {
    assert_eq!(
        codes("sequenceDiagram\nparticipant a<b\n"),
        ["sequence/unexpected-token"]
    );
}

#[test]
fn box_body_accepts_participants_only() {
    assert_eq!(
        codes("sequenceDiagram\nbox X\nparticipant A\ndestroy B\nend\n"),
        Vec::<String>::new()
    );
    assert_eq!(
        codes("sequenceDiagram\nbox X\ncreate participant A\nend\n"),
        ["sequence/unknown-statement"]
    );
}

#[test]
fn accessibility_forms_capture_values() {
    let source =
        "sequenceDiagram\naccTitle: T\naccDescr: D\naccDescr {\nmulti\n}\naccDescr {}\nA->>B: x\n";
    let parsed = parse(source, &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    assert_eq!(
        kinds(source),
        ["accessibility", "accessibility", "accessibility", "signal"]
    );
}

#[test]
fn unterminated_metadata_and_accessibility_report_their_opener() {
    let source = "sequenceDiagram\nparticipant A@{ \"type\": \"actor\"\n";
    let parsed = parse(source, &[]);
    assert_eq!(parsed.diagnostics.len(), 1);
    assert_eq!(parsed.diagnostics[0].code, "sequence/unterminated");
    assert_eq!(
        &source[parsed.diagnostics[0].span.start..parsed.diagnostics[0].span.end],
        "@{ \"type\": \"actor\"\n"
    );
    let source = "sequenceDiagram\naccDescr {\nnever closed\n";
    let parsed = parse(source, &[]);
    assert_eq!(parsed.diagnostics.len(), 1);
    assert_eq!(parsed.diagnostics[0].code, "sequence/unterminated");
    assert_eq!(
        parsed.diagnostics[0].span.start,
        source.find("accDescr").unwrap_or(0)
    );
}

#[test]
fn left_of_and_actor_split() {
    let tokens = lex("note left of Alice: hi\n", &[]);
    let names: Vec<&str> = tokens.iter().map(|t| t.kind).collect();
    assert!(names.contains(&"left_of"));
    assert!(names.contains(&"note"));
}

#[test]
fn actor_stops_before_arrow_and_parens() {
    let tokens = lex("A->>B: hi\n", &[]);
    let actors: Vec<&str> = tokens
        .iter()
        .filter(|t| t.kind == "ACTOR")
        .map(|t| t.text.as_ref())
        .collect();
    assert_eq!(actors, ["A", "B"]);
    let tokens = lex("A()->>B: hi\n", &[]);
    assert!(tokens.iter().any(|t| t.kind == "()"));
    let actors: Vec<&str> = tokens
        .iter()
        .filter(|t| t.kind == "ACTOR")
        .map(|t| t.text.as_ref())
        .collect();
    assert_eq!(actors, ["A", "B"]);
}

#[test]
fn newline_and_semicolon_both_terminate() {
    assert_eq!(
        kinds("sequenceDiagram\nA->>B: x; C->>D: y\n"),
        ["signal", "signal"]
    );
}

#[test]
fn participant_modes_capture_alias_and_config() {
    let parsed = parse(
        "sequenceDiagram\nparticipant Bob as Bob Marley\nA->>Bob: hi\n",
        &[],
    );
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let parsed = parse(
        "sequenceDiagram\nparticipant Bob@{ \"type\": \"actor\" } as Bobby\nA->>Bob: hi\n",
        &[],
    );
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
}

#[test]
fn unterminated_block_reports_once() {
    assert_eq!(
        codes("sequenceDiagram\nloop every day\nA->>B: x\n"),
        ["sequence/unterminated"]
    );
    assert_eq!(
        codes("sequenceDiagram\nbox Tan\nparticipant X\n"),
        ["sequence/unterminated"]
    );
}

#[test]
fn recovery_preserves_enclosing_block() -> Result<(), &'static str> {
    let source = "sequenceDiagram\nloop L\nA->>: x\nB->>C: y\nend\nD->>E: z\n";
    let parsed = parse(source, &[]);
    let error = parsed
        .diagnostics
        .iter()
        .find(|d| d.code == "sequence/unexpected-token")
        .ok_or("unexpected token diagnostic missing")?;
    assert_eq!(&source[error.span.start..error.span.end], ": x");
    assert_eq!(parsed.diagnostics.len(), 1);
    assert_eq!(kinds(source), ["control", "signal"]);
    Ok(())
}

#[test]
fn unknown_statement_starts_no_production() {
    assert_eq!(
        codes("sequenceDiagram\noff x\n"),
        ["sequence/unknown-statement"]
    );
}

#[test]
fn nesting_limit_stops_recursion() {
    let mut source = String::from("sequenceDiagram\n");
    for _ in 0..65 {
        source.push_str("loop L\n");
    }
    for _ in 0..65 {
        source.push_str("end\n");
    }
    let parsed = parse(&source, &[]);
    assert!(
        parsed
            .diagnostics
            .iter()
            .any(|d| d.code == "limit/nesting-depth")
    );
}

#[test]
fn accessibilities_capture_values() {
    let parsed = parse(
        "sequenceDiagram\naccTitle: My title\naccDescr { multi line } \nA->>B: x\n",
        &[],
    );
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
}

#[test]
fn statement_spans_exclude_terminator() -> Result<(), &'static str> {
    let source = "sequenceDiagram\nA->>B: hi\n";
    let parsed = parse(source, &[]);
    let statement = parsed
        .document
        .document
        .lines
        .iter()
        .find_map(|line| line.statement.as_ref())
        .ok_or("signal statement missing")?;
    assert_eq!(&source[statement.span.end..], "\n");
    Ok(())
}

fn check_spans(source: &str, lines: &[Line<'_>], seen: &mut usize) {
    for line in lines {
        let Some(statement) = line.statement.as_ref() else {
            continue;
        };
        *seen += 1;
        let span = statement.span;
        assert_eq!(span, line.span);
        assert_eq!(
            source.get(span.end..=span.end),
            Some("\n"),
            "statement {:?}",
            &source[span.start..span.end]
        );
        match &statement.kind {
            StatementKind::Autonumber { span: own, .. }
            | StatementKind::Activate { span: own, .. }
            | StatementKind::Deactivate { span: own, .. } => assert_eq!(*own, span),
            StatementKind::Box(block) => {
                check_spans(source, &block.section.lines, seen);
                let last = block.section.lines.last().map(|line| line.span.end);
                assert_eq!(Some(block.section.span.end), last);
            }
            _ => {}
        }
    }
}

#[test]
fn every_statement_span_stops_before_its_terminator() {
    let source = "sequenceDiagram\nbox B\nparticipant P\ndestroy P\nend\nparticipant A\nactor C\ncreate participant D\nautonumber 3\nactivate A\ndeactivate A\nNote over A: x\nlink A: l @ u\nlinks A: {}\nproperties A: {}\ndetails A: {}\nA->>C: hi\n";
    let parsed = parse(source, &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut seen = 0;
    let lines = &parsed.document.document.lines;
    check_spans(source, lines, &mut seen);
    assert_eq!(seen, 15);
    let last = lines.last().map(|line| line.span.end);
    assert_eq!(Some(parsed.document.document.span.end), last);
}

fn quote_warnings(source: &str) -> Vec<crate::diag::Diagnostic> {
    parse(source, &[])
        .diagnostics
        .into_iter()
        .filter(|d| d.code == "sequence/quote-unclosed")
        .collect()
}

#[test]
fn unclosed_quote_warns_on_names_and_aliases() {
    let cases: [(&str, &str, &[&str]); 14] = [
        (
            "participant name",
            "sequenceDiagram\n  participant \"Bob\n  A->>Bob: hi\n",
            &["\"Bob"],
        ),
        ("actor name", "sequenceDiagram\n  actor \"Bob\n", &["\"Bob"]),
        (
            "alias",
            "sequenceDiagram\n  participant Alice as \"Alias\n",
            &["\"Alias"],
        ),
        (
            "name and alias",
            "sequenceDiagram\n  participant \"Bob as \"B\n",
            &["\"Bob", "\"B"],
        ),
        (
            "created participant",
            "sequenceDiagram\n  create participant \"Bob\n",
            &["\"Bob"],
        ),
        (
            "inside a box",
            "sequenceDiagram\n  box Group\n    participant \"Bob\n  end\n",
            &["\"Bob"],
        ),
        (
            "inside a block",
            "sequenceDiagram\n  alt ok\n    participant \"Bob\n  end\n",
            &["\"Bob"],
        ),
        (
            "closed name",
            "sequenceDiagram\n  participant \"Bob\"\n",
            &[],
        ),
        (
            "closed alias",
            "sequenceDiagram\n  participant Alice as \"Alias\"\n",
            &[],
        ),
        (
            "closed quote with a tail",
            "sequenceDiagram\n  participant \"Bob\" x\n",
            &[],
        ),
        ("plain name", "sequenceDiagram\n  participant Bob\n", &[]),
        (
            "quote not at the start",
            "sequenceDiagram\n  participant Bo\"b\n",
            &[],
        ),
        (
            "destroy is not a declaration",
            "sequenceDiagram\n  destroy \"Bob\n",
            &[],
        ),
        (
            "message actor is not a declaration",
            "sequenceDiagram\n  A->>\"Bob: hi\n",
            &[],
        ),
    ];
    for (name, source, hits) in cases {
        let found: Vec<&str> = quote_warnings(source)
            .iter()
            .map(|d| {
                assert_eq!(d.severity, crate::diag::Severity::Warning, "{name}");
                &source[d.span.start..d.span.end]
            })
            .collect();
        assert_eq!(found, hits, "{name}");
    }
}

#[test]
fn unclosed_quote_warning_carries_the_registry_row_and_an_unsafe_fix() {
    let source = "sequenceDiagram\n  participant \"Bob \t\n";
    let found = quote_warnings(source);
    assert_eq!(found.len(), 1);
    let row = crate::r#gen::lintrules::LINT_RULES
        .iter()
        .find(|row| row.code == "sequence/quote-unclosed");
    assert!(row.is_some(), "registry row missing");
    let (summary, help) = row.map_or(("", ""), |row| (row.summary, row.help));
    assert!(!summary.is_empty());
    assert_eq!(found[0].message, summary);
    assert_eq!(found[0].help, help);
    let end = "sequenceDiagram\n  participant \"Bob".len();
    assert_eq!(
        found[0].span,
        Span {
            start: end - "\"Bob".len(),
            end
        }
    );
    assert_eq!(found[0].fixes.len(), 1);
    let fix = &found[0].fixes[0];
    assert_eq!(fix.title, "Insert the closing quote");
    assert_eq!(fix.safety, crate::diag::FixSafety::Unsafe);
    assert_eq!(fix.edits.len(), 1);
    assert_eq!(fix.edits[0].span, Span { start: end, end });
    assert_eq!(fix.edits[0].new_text, "\"");
}

#[test]
fn unclosed_quote_is_not_a_syntax_error() {
    let parsed = parse("sequenceDiagram\n  participant \"Bob\n  A->>Bob: hi\n", &[]);
    assert!(
        parsed
            .diagnostics
            .iter()
            .all(|d| d.severity != crate::diag::Severity::Error),
        "{:?}",
        parsed.diagnostics
    );
}
