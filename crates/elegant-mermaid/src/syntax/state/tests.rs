use super::{ast::StatementKind, lexer::lex, parse};
use crate::diag::Severity;

#[test]
fn state_header_accepts_eof_without_synthetic_lines() {
    let parsed = parse("stateDiagram-v2", &[]);
    assert!(
        parsed.diagnostics.is_empty(),
        "EOF header must parse without diagnostics: {:?}",
        parsed.diagnostics
    );
    assert!(
        parsed.document.document.lines.is_empty(),
        "EOF header must not synthesize body lines: {:?}",
        parsed.document.document.lines
    );
    assert_eq!(parsed.document.header.text, "stateDiagram-v2");
    assert_eq!(parsed.document.span.end, 15);
}

#[test]
fn state_alias_keeps_body_and_colon_identifier_distinction() -> Result<(), &'static str> {
    let source = "stateDiagram\nstate \"First\" as a: detail\nstate \"Second\" as b: detail {\n[*] --> C\n}\n";
    let parsed = parse(source, &[]);
    assert!(
        parsed.diagnostics.is_empty(),
        "aliases with and without bodies must parse: {:?}",
        parsed.diagnostics
    );
    let statements: Vec<_> = parsed
        .document
        .document
        .lines
        .iter()
        .filter_map(|l| l.statement.as_ref())
        .collect();
    assert_eq!(statements.len(), 2);
    let StatementKind::Composite {
        id,
        description,
        body,
        ..
    } = &statements[0].kind
    else {
        return Err("expected alias declaration");
    };
    assert_eq!(id.text.trim(), "a: detail");
    assert_eq!(description.as_ref().map(|t| t.text.as_ref()), Some("First"));
    assert!(
        body.is_none(),
        "alias without braces must not acquire a body: {body:?}"
    );
    let StatementKind::Composite {
        id,
        body,
        delimiters,
        ..
    } = &statements[1].kind
    else {
        return Err("expected composite declaration");
    };
    assert_eq!(id.text.trim(), "b: detail");
    let body = body.as_ref().ok_or("composite retains document")?;
    assert_eq!(
        body.lines.iter().filter(|l| l.statement.is_some()).count(),
        1
    );
    assert!(
        delimiters.is_some(),
        "composite body must retain both brace spans: {delimiters:?}"
    );
    assert_eq!(
        &source[statements[1].span.start..statements[1].span.end],
        "state \"Second\" as b: detail {\n[*] --> C\n}"
    );
    Ok(())
}

#[test]
fn state_rejects_entire_chained_transition_and_recovers_inside_scope() -> Result<(), &'static str> {
    let parsed = parse(
        "stateDiagram\nstate Outer {\nA --> B --> C\nD --> E\n}\nF\n",
        &[],
    );
    assert_eq!(parsed.diagnostics.len(), 1);
    assert_eq!(parsed.diagnostics[0].code, "state/unexpected-token");
    let statements: Vec<_> = parsed
        .document
        .document
        .lines
        .iter()
        .filter_map(|l| l.statement.as_ref())
        .collect();
    assert_eq!(statements.len(), 2);
    let StatementKind::Composite {
        body: Some(body), ..
    } = &statements[0].kind
    else {
        return Err("scope must survive recovery");
    };
    let children: Vec<_> = body
        .lines
        .iter()
        .filter_map(|l| l.statement.as_ref())
        .collect();
    assert_eq!(children.len(), 1);
    let StatementKind::Transition { from, to, .. } = &children[0].kind else {
        return Err("expected surviving transition");
    };
    assert_eq!((from.id.text.as_ref(), to.id.text.as_ref()), ("D", "E"));
    Ok(())
}

#[test]
fn state_quoted_descriptions_and_block_notes_retain_physical_line_ends() -> Result<(), &'static str>
{
    let parsed = parse(
        "stateDiagram\rstate \"one\r\ntwo\rthree\" as A\rnote left of A\rfirst\r\nsecond\rend note\r",
        &[],
    );
    assert!(
        parsed.diagnostics.is_empty(),
        "quoted descriptions and block notes must retain mixed line endings: {:?}",
        parsed.diagnostics
    );
    let statements: Vec<_> = parsed
        .document
        .document
        .lines
        .iter()
        .filter_map(|l| l.statement.as_ref())
        .collect();
    let StatementKind::Composite {
        description: Some(description),
        ..
    } = &statements[0].kind
    else {
        return Err("expected quoted state");
    };
    assert_eq!(description.text, "one\r\ntwo\rthree");
    let StatementKind::Note {
        text,
        position,
        target,
    } = &statements[1].kind
    else {
        return Err("expected attached note");
    };
    assert_eq!(text.text, "first\r\nsecond");
    assert_eq!((position.value, target.text.as_ref()), ("left_of", "A"));
    Ok(())
}

#[test]
fn state_default_classdef_keeps_authority_token_mismatch() {
    let parsed = parse("stateDiagram\nclassDef default fill:red\nA\n", &[]);
    assert_eq!(parsed.diagnostics.len(), 1);
    assert_eq!(parsed.diagnostics[0].code, "state/unexpected-token");
    assert_eq!(
        parsed.diagnostics[0].message,
        "unexpected default , expected one of: CLASSDEF_ID, DEFAULT"
    );
    assert_eq!(
        parsed
            .document
            .document
            .lines
            .iter()
            .filter(|l| l.statement.is_some())
            .count(),
        1
    );
}

#[test]
fn state_styles_keep_order_and_literal_components() -> Result<(), &'static str> {
    let parsed = parse(
        "stateDiagram\nclassDef marked fill:#abc,color:red;\nstyle B,A fill:blue,stroke:red;\nclass B,A marked\nA:::marked --> B: go\n",
        &[],
    );
    assert!(
        parsed.diagnostics.is_empty(),
        "ordered style directives and inline classes must parse: {:?}",
        parsed.diagnostics
    );
    let statements: Vec<_> = parsed
        .document
        .document
        .lines
        .iter()
        .filter_map(|l| l.statement.as_ref())
        .collect();
    let StatementKind::Style(style) = &statements[1].kind else {
        return Err("expected style");
    };
    assert_eq!(style.targets.text.trim(), "B,A");
    assert_eq!(style.styles.text, "fill:blue,stroke:red;");
    let StatementKind::Transition {
        from, description, ..
    } = &statements[3].kind
    else {
        return Err("expected transition");
    };
    assert_eq!(
        from.css_class.as_ref().map(|t| t.text.as_ref()),
        Some("marked")
    );
    assert_eq!(description.as_ref().map(|t| t.text.as_ref()), Some(": go"));
    Ok(())
}

#[test]
fn state_comment_split_and_source_order_are_observable() -> Result<(), &'static str> {
    let tokens = lex(
        "stateDiagram\nA%% comment\nnoise direction LR suffix\n",
        &[],
    );
    let ids: Vec<_> = tokens
        .iter()
        .filter(|t| t.kind == "ID")
        .map(|t| t.text.as_ref())
        .collect();
    assert_eq!(ids, ["A"]);
    let direction = tokens
        .iter()
        .find(|t| t.kind == "direction_lr")
        .ok_or("greedy direction rule precedes ID")?;
    assert_eq!(direction.text, "noise direction LR suffix");
    Ok(())
}

#[test]
fn state_accessibility_block_keeps_closing_delimiter_span() -> Result<(), &'static str> {
    let source = "stateDiagram\naccDescr {first\nsecond}\nA\n";
    let parsed = parse(source, &[]);
    assert!(
        parsed.diagnostics.is_empty(),
        "closed accessibility block must parse: {:?}",
        parsed.diagnostics
    );
    let statement = parsed
        .document
        .document
        .lines
        .iter()
        .find_map(|l| l.statement.as_ref())
        .ok_or("accessibility statement")?;
    let StatementKind::Accessibility {
        title: false,
        value,
    } = &statement.kind
    else {
        return Err("expected description");
    };
    assert_eq!(value.text, "first\nsecond");
    assert_eq!(
        &source[statement.span.start..statement.span.end],
        "accDescr {first\nsecond}"
    );
    Ok(())
}

#[test]
fn state_unclosed_composite_is_not_resolved_as_partial_state() {
    let parsed = parse("stateDiagram\nstate A {\nB\n", &[]);
    assert_eq!(parsed.diagnostics.len(), 1);
    assert_eq!(parsed.diagnostics[0].code, "state/unterminated");
    assert_eq!(parsed.diagnostics[0].span.start, 21);
    assert!(
        parsed
            .document
            .document
            .lines
            .iter()
            .all(|l| l.statement.is_none()),
        "unclosed composite must leave no partial state statements: {:?}",
        parsed.document.document.lines
    );
}

#[test]
fn state_nesting_stops_before_level_sixty_five() {
    let mut source = String::from("stateDiagram\n");
    for i in 0..65 {
        source.push_str(&format!("state n{i} {{\n"));
    }
    let parsed = parse(&source, &[]);
    assert_eq!(
        parsed
            .diagnostics
            .iter()
            .filter(|d| d.code == "limit/nesting-depth")
            .count(),
        1
    );
    assert!(
        parsed
            .diagnostics
            .iter()
            .all(|d| d.code != "state/unterminated"),
        "nesting-limit diagnostic must take precedence over unterminated composites: {:?}",
        parsed.diagnostics
    );
}

#[test]
fn state_directives_and_symbol_alternatives_keep_typed_facts() -> Result<(), &'static str> {
    let source = "stateDiagram\nstate f <<fork>>\nstate j [[join]]\nstate c <<choice>>\nstate Ignored\nnote \"memo\" as Float\nclick f \"https://example.com\" \"tip\"\nclick j href \"mailto:x@y\"\naccTitle: A\naccDescr: B\nscale 2 width\nhide empty description\nstate Outer {\n--\nA\n--\n}\n";
    let parsed = parse(source, &[]);
    assert!(
        parsed.diagnostics.is_empty(),
        "symbol, note, link, accessibility, scale, and concurrent alternatives must parse: {:?}",
        parsed.diagnostics
    );
    let statements: Vec<_> = parsed
        .document
        .document
        .lines
        .iter()
        .filter_map(|l| l.statement.as_ref())
        .collect();
    assert_eq!(statements.len(), 12);
    let stereotypes: Vec<_> = statements
        .iter()
        .filter_map(|s| match &s.kind {
            StatementKind::Stereotype { id, stereotype } => Some((id.text.as_ref(), *stereotype)),
            _ => None,
        })
        .collect();
    assert_eq!(
        stereotypes,
        [
            ("f", super::ast::Stereotype::Fork),
            ("j", super::ast::Stereotype::Join),
            ("c", super::ast::Stereotype::Choice)
        ]
    );
    let StatementKind::FloatingNote { text, id } = &statements[4].kind else {
        return Err("floating note must remain distinct");
    };
    assert_eq!((text.text.as_ref(), id.text.trim()), ("memo", "Float"));
    let StatementKind::Click { url, tooltip, .. } = &statements[5].kind else {
        return Err("expected quoted link");
    };
    assert_eq!(url.text, "https://example.com");
    assert_eq!(tooltip.as_ref().map(|t| t.text.as_ref()), Some("tip"));
    let StatementKind::Click { tooltip, .. } = &statements[6].kind else {
        return Err("expected href link");
    };
    assert!(
        tooltip.is_none(),
        "href alternative must not invent a tooltip: {tooltip:?}"
    );
    let StatementKind::Composite {
        body: Some(body), ..
    } = &statements[11].kind
    else {
        return Err("expected concurrent composite");
    };
    assert_eq!(
        body.lines
            .iter()
            .filter_map(|l| l.statement.as_ref())
            .filter(|s| matches!(s.kind, StatementKind::Concurrent))
            .count(),
        2
    );
    Ok(())
}

#[test]
fn state_unclosed_quote_points_at_quote_and_preserves_unicode_boundaries() {
    let source = "stateDiagram\nstate \"unfinished é";
    let parsed = parse(source, &[]);
    assert_eq!(parsed.diagnostics.len(), 1);
    let diagnostic = &parsed.diagnostics[0];
    assert_eq!(diagnostic.code, "state/unterminated");
    assert_eq!(
        &source[diagnostic.span.start..diagnostic.span.end],
        "\"unfinished é"
    );
    assert!(
        parsed
            .document
            .document
            .lines
            .iter()
            .all(|l| l.statement.is_none()),
        "unclosed quoted declaration must leave no partial state statements: {:?}",
        parsed.document.document.lines
    );
}

#[test]
fn state_colon_description_accepts_multibyte_scalar_after_paired_colon() -> Result<(), &'static str>
{
    let parsed = parse("stateDiagram\nA: first:é\n", &[]);
    assert!(
        parsed.diagnostics.is_empty(),
        "paired colon followed by a multibyte scalar must parse: {:?}",
        parsed.diagnostics
    );
    let statement = parsed
        .document
        .document
        .lines
        .iter()
        .find_map(|l| l.statement.as_ref())
        .ok_or("expected description assignment")?;
    let StatementKind::Id {
        description: Some(description),
        ..
    } = &statement.kind
    else {
        return Err("expected state description");
    };
    assert_eq!(description.text, ": first:é");
    Ok(())
}

#[test]
fn state_composite_opens_brace_on_next_line_keeps_children_and_spans() -> Result<(), &'static str> {
    let source =
        "stateDiagram-v2\n\n  state Parent\n  {\n  Child\n  }\n\n  Parent --> Other : label\n";
    let parsed = parse(source, &[]);
    assert!(
        parsed.diagnostics.is_empty(),
        "composite with its opening brace on the next line must parse: {:?}",
        parsed.diagnostics
    );
    let statements: Vec<_> = parsed
        .document
        .document
        .lines
        .iter()
        .filter_map(|l| l.statement.as_ref())
        .collect();
    assert_eq!(statements.len(), 2);
    let StatementKind::Composite {
        id,
        body: Some(body),
        delimiters: Some((open, close)),
        ..
    } = &statements[0].kind
    else {
        return Err("expected composite with a body");
    };
    assert_eq!(id.text, "Parent");
    assert_eq!(&source[open.start..open.end], "{");
    assert_eq!(&source[close.start..close.end], "}");
    let children: Vec<_> = body
        .lines
        .iter()
        .filter_map(|l| l.statement.as_ref())
        .collect();
    assert_eq!(children.len(), 1);
    let StatementKind::Id { id: child, .. } = &children[0].kind else {
        return Err("expected nested child state");
    };
    assert_eq!(child.id.text, "Child");
    assert_eq!(&source[child.span.start..child.span.end], "Child");
    assert_eq!(
        &source[children[0].span.start..children[0].span.end],
        "Child"
    );
    assert_eq!(
        &source[statements[0].span.start..statements[0].span.end],
        "state Parent\n  {\n  Child\n  }"
    );
    let StatementKind::Transition {
        from,
        to,
        description,
        ..
    } = &statements[1].kind
    else {
        return Err("expected transition after the composite");
    };
    assert_eq!(
        (from.id.text.as_ref(), to.id.text.as_ref()),
        ("Parent", "Other")
    );
    assert_eq!(
        description.as_ref().map(|t| t.text.as_ref()),
        Some(": label")
    );
    Ok(())
}

#[test]
fn state_blank_line_before_brace_keeps_composite_bare_and_rejects_stray_brace()
-> Result<(), &'static str> {
    let parsed = parse("stateDiagram\nstate Parent\n\n{\nChild\n}\n", &[]);
    let codes: Vec<_> = parsed
        .diagnostics
        .iter()
        .map(|d| (d.code, d.severity))
        .collect();
    assert_eq!(
        codes,
        [
            ("state/unknown-statement", Severity::Error),
            ("state/unexpected-token", Severity::Error)
        ]
    );
    let statements: Vec<_> = parsed
        .document
        .document
        .lines
        .iter()
        .filter_map(|l| l.statement.as_ref())
        .collect();
    assert_eq!(statements.len(), 2);
    let StatementKind::Composite { body: None, .. } = &statements[0].kind else {
        return Err("blank line must keep the composite bare");
    };
    let StatementKind::Id { id, .. } = &statements[1].kind else {
        return Err("recovered child must parse as an id statement");
    };
    assert_eq!(id.id.text, "Child");
    Ok(())
}
