use super::{
    ast::*,
    lexer::{MODES, lex},
    parse,
};
use crate::source::Span;

#[test]
fn requirement_header_requires_newline_and_keeps_alias() -> Result<(), &'static str> {
    for newline in ["\n", "\r\n", "\r"] {
        let source = format!("requirement{newline}");
        let parsed = parse(&source, &[]);
        assert!(
            parsed.diagnostics.is_empty(),
            "header alias with {newline:?} must parse without diagnostics: {:?}",
            parsed.diagnostics
        );
        assert_eq!(parsed.document.header.span, Span { start: 0, end: 11 });
        assert_eq!(
            parsed.document.diagram.span,
            Span {
                start: source.len(),
                end: source.len(),
            }
        );
    }
    let parsed = parse("requirementDiagram", &[]);
    let d = parsed
        .diagnostics
        .first()
        .ok_or("missing newline diagnostic")?;
    assert_eq!(d.code, "requirement/unexpected-token");
    assert_eq!(d.message, "unexpected , expected one of: NEWLINE");
    assert_eq!(d.span, Span { start: 18, end: 18 });
    Ok(())
}

#[test]
fn requirement_definition_keeps_fields_and_delimiters() -> Result<(), &'static str> {
    let source = "requirementDiagram\nrequirement req {\nid: 1\ntext: \"é\"\nrisk: high\nverifyMethod: test\n}\n";
    let parsed = parse(source, &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let statement = parsed
        .document
        .diagram
        .statements
        .first()
        .ok_or("definition")?;
    let StatementKind::Requirement(def) = &statement.kind else {
        return Err("requirement");
    };
    assert_eq!(def.name.value, "req");
    assert_eq!(def.name.span, Span { start: 31, end: 35 });
    assert_eq!(def.delimiters.0, Span { start: 35, end: 36 });
    assert_eq!(def.body.fields.len(), 4);
    let field = def.body.fields.get(1).ok_or("text field")?;
    let RequirementFieldValue::Text(text) = &field.value else {
        return Err("text");
    };
    assert_eq!(text.value, "é");
    assert!(
        text.quoted,
        "quoted text must retain its quoted flag: {text:?}"
    );
    assert_eq!(text.span, Span { start: 49, end: 53 });
    assert_eq!(field.colon, Span { start: 47, end: 48 });
    assert_eq!(def.requirement_type.value, "Requirement");
    Ok(())
}

#[test]
fn requirement_type_alternatives_and_empty_bodies_are_preserved() -> Result<(), &'static str> {
    for (keyword, value) in [
        ("requirement", "Requirement"),
        ("functionalRequirement", "Functional Requirement"),
        ("interfaceRequirement", "Interface Requirement"),
        ("performanceRequirement", "Performance Requirement"),
        ("physicalRequirement", "Physical Requirement"),
        ("designConstraint", "Design Constraint"),
    ] {
        let source = format!("requirementDiagram\n{keyword} req {{\n}}\n");
        let parsed = parse(&source, &[]);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let statement = parsed
            .document
            .diagram
            .statements
            .first()
            .ok_or("definition")?;
        let StatementKind::Requirement(def) = &statement.kind else {
            return Err("requirement");
        };
        assert_eq!(def.requirement_type.value, value);
        assert!(
            def.body.fields.is_empty(),
            "empty requirement body must not acquire fields: {:?}",
            def.body.fields
        );
        assert_eq!(def.body.span, def.delimiters.1);
    }
    Ok(())
}

#[test]
fn requirement_element_retains_ordered_repeated_fields() -> Result<(), &'static str> {
    let source = "requirementDiagram\nelement unit:::blue,red {\ntype: simulation\ndocref: \"spec\"\ntype: model\n}\n";
    let parsed = parse(source, &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let statement = parsed
        .document
        .diagram
        .statements
        .first()
        .ok_or("definition")?;
    let StatementKind::Element(def) = &statement.kind else {
        return Err("element");
    };
    assert_eq!(def.name.value, "unit");
    assert_eq!(def.name.span, Span { start: 27, end: 31 });
    let classes = def.classes.as_ref().ok_or("inline classes")?;
    assert_eq!(
        classes
            .names
            .iter()
            .map(|n| n.value.as_ref())
            .collect::<Vec<_>>(),
        ["blue", "red"]
    );
    assert_eq!(def.body.fields.len(), 3);
    let field = def.body.fields.get(1).ok_or("reference field")?;
    let ElementFieldValue::Ref(reference) = &field.value else {
        return Err("reference");
    };
    assert_eq!(reference.value, "spec");
    assert!(
        reference.quoted,
        "quoted docref must retain its quoted flag: {reference:?}"
    );
    assert_eq!(reference.span, Span { start: 70, end: 76 });
    Ok(())
}

#[test]
fn requirement_relationships_keep_direction_and_all_kinds() -> Result<(), &'static str> {
    for relation in [
        "contains",
        "copies",
        "derives",
        "satisfies",
        "verifies",
        "refines",
        "traces",
    ] {
        let source = format!("requirementDiagram\nA - {relation} -> B\nA <- {relation} - A\n");
        let parsed = parse(&source, &[]);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let statements = &parsed.document.diagram.statements;
        let StatementKind::Relationship(forward) = &statements.first().ok_or("forward")?.kind
        else {
            return Err("relationship");
        };
        assert_eq!(
            (forward.left.value.as_ref(), forward.right.value.as_ref()),
            ("A", "B")
        );
        assert_eq!(forward.left.span, Span { start: 19, end: 21 });
        assert_eq!(forward.relationship.value, relation);
        assert!(
            !forward.reversed,
            "right-arrow relationship must retain forward orientation: {forward:?}"
        );
        let StatementKind::Relationship(reverse) = &statements.get(1).ok_or("reverse")?.kind else {
            return Err("relationship");
        };
        assert!(
            reverse.reversed,
            "left-arrow relationship must retain reversed orientation: {reverse:?}"
        );
        assert_eq!(
            (reverse.left.value.as_ref(), reverse.right.value.as_ref()),
            ("A", "A")
        );
    }
    Ok(())
}

#[test]
fn requirement_styles_retain_components_and_class_lists() -> Result<(), &'static str> {
    let source = "requirementDiagram\nclassDef blue,red fill:#abc,color:red;\nstyle A,B stroke-width:2\nclass A,B blue,red\nA:::blue,red\n";
    let parsed = parse(source, &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let statements = &parsed.document.diagram.statements;
    assert_eq!(statements.len(), 4);
    let StatementKind::ClassDef(def) = &statements.first().ok_or("class definition")?.kind else {
        return Err("class definition");
    };
    assert_eq!(
        def.ids
            .names
            .iter()
            .map(|n| n.value.as_ref())
            .collect::<Vec<_>>(),
        ["blue", "red"]
    );
    assert_eq!(def.ids.span, Span { start: 28, end: 36 });
    let first = def.styles.styles.first().ok_or("first style")?;
    assert_eq!(
        first
            .components
            .iter()
            .map(|c| c.text.as_ref())
            .collect::<Vec<_>>(),
        ["fill", ":", "#", "abc"]
    );
    assert_eq!(first.span, Span { start: 37, end: 46 });
    let StatementKind::Style(style) = &statements.get(1).ok_or("style")?.kind else {
        return Err("style");
    };
    assert_eq!(
        style
            .ids
            .names
            .iter()
            .map(|n| n.value.as_ref())
            .collect::<Vec<_>>(),
        ["A", "B"]
    );
    let StatementKind::Class(class) = &statements.get(3).ok_or("shorthand")?.kind else {
        return Err("class");
    };
    assert_eq!(class.classes.names.len(), 2);
    assert_eq!(
        class.separator,
        Some(Span {
            start: 103,
            end: 106
        })
    );
    Ok(())
}

#[test]
fn requirement_accessibility_modes_keep_values_and_whole_block() -> Result<(), &'static str> {
    let source =
        "accTitle: Before\nrequirementDiagram\naccDescr: café\naccDescr {one\r\ntwo}\naccTitle:\n";
    let parsed = parse(source, &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let leading = parsed.document.directives.first().ok_or("leading title")?;
    assert_eq!(leading.value.text, "Before");
    assert_eq!(leading.span, Span { start: 0, end: 16 });
    let statements = &parsed.document.diagram.statements;
    let StatementKind::Directive(block) = &statements.get(1).ok_or("description block")?.kind
    else {
        return Err("description block");
    };
    assert_eq!(block.value.text, "one\r\ntwo");
    assert!(
        block.multiline,
        "braced accessibility description must retain its multiline flag: {block:?}"
    );
    assert_eq!(block.span, Span { start: 52, end: 71 });
    let StatementKind::Directive(empty) = &statements.get(2).ok_or("empty title")?.kind else {
        return Err("empty title");
    };
    assert_eq!(empty.value.text, "");
    Ok(())
}

#[test]
fn requirement_whole_line_directions_precede_words_and_comments() -> Result<(), &'static str> {
    let source = "requirementDiagram\nnoise direction LR suffix direction TB\n# direction BT\n%% direction RL\n";
    let parsed = parse(source, &[]);
    assert!(
        parsed.diagnostics.is_empty(),
        "whole-line direction rules must parse before words and comments: {:?}",
        parsed.diagnostics
    );
    let values = parsed
        .document
        .diagram
        .statements
        .iter()
        .filter_map(|s| {
            if let StatementKind::Direction(d) = &s.kind {
                Some(d.value)
            } else {
                None
            }
        })
        .collect::<Vec<_>>();
    assert_eq!(values, ["TB", "BT", "RL"]);
    let first = parsed
        .document
        .diagram
        .statements
        .first()
        .ok_or("direction")?;
    assert_eq!(first.span, Span { start: 19, end: 57 });
    Ok(())
}

#[test]
fn requirement_mixed_line_endings_and_case_fold_body_only() -> Result<(), &'static str> {
    let source = "requirementDiagram\rReQuIrEmEnT r {\r\nRiSk: LOW\nVERIFYMETHOD: ANALYSIS\r}\r";
    let parsed = parse(source, &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let statement = parsed
        .document
        .diagram
        .statements
        .first()
        .ok_or("definition")?;
    let StatementKind::Requirement(def) = &statement.kind else {
        return Err("requirement");
    };
    let first = def.body.fields.first().ok_or("risk")?;
    let RequirementFieldValue::Risk(risk) = &first.value else {
        return Err("risk");
    };
    assert_eq!(risk.value, "Low");
    assert_eq!(risk.span, Span { start: 42, end: 45 });
    assert_eq!(def.body.fields.len(), 2);
    Ok(())
}

#[test]
fn requirement_invalid_risk_recovers_at_next_field() -> Result<(), &'static str> {
    let source =
        "requirementDiagram\nrequirement r {\nrisk: extreme\ntext: okay\n}\nelement e {\n}\n";
    let parsed = parse(source, &[]);
    assert_eq!(parsed.diagnostics.len(), 1);
    let d = parsed.diagnostics.first().ok_or("risk diagnostic")?;
    assert_eq!(d.code, "requirement/unexpected-token");
    assert_eq!(
        d.message,
        "unexpected extreme, expected one of: HIGH_RISK, LOW_RISK, MED_RISK"
    );
    assert_eq!(d.span, Span { start: 41, end: 48 });
    assert_eq!(parsed.document.diagram.statements.len(), 2);
    let StatementKind::Requirement(def) = &parsed
        .document
        .diagram
        .statements
        .first()
        .ok_or("definition")?
        .kind
    else {
        return Err("requirement");
    };
    assert_eq!(def.body.fields.len(), 1);
    Ok(())
}

#[test]
fn requirement_invalid_verification_keeps_closing_brace() -> Result<(), &'static str> {
    let parsed = parse(
        "requirementDiagram\nrequirement r {\nverifyMethod: nope\n}\n",
        &[],
    );
    let d = parsed
        .diagnostics
        .first()
        .ok_or("verification diagnostic")?;
    assert_eq!(parsed.diagnostics.len(), 1);
    assert_eq!(
        d.message,
        "unexpected nope, expected one of: VERIFY_ANALYSIS, VERIFY_DEMONSTRATION, VERIFY_INSPECTION, VERIFY_TEST"
    );
    assert_eq!(d.span, Span { start: 49, end: 53 });
    assert_eq!(parsed.document.diagram.statements.len(), 1);
    Ok(())
}

#[test]
fn requirement_unknown_statement_recovers_without_phantom_definition() -> Result<(), &'static str> {
    let parsed = parse("requirementDiagram\n@ bad\nelement e {\n}\n", &[]);
    assert_eq!(parsed.diagnostics.len(), 1);
    let d = parsed.diagnostics.first().ok_or("unknown diagnostic")?;
    assert_eq!(d.code, "requirement/unknown-statement");
    assert_eq!(d.message, "unknown statement @");
    assert_eq!(d.span, Span { start: 19, end: 24 });
    assert_eq!(parsed.document.diagram.statements.len(), 1);
    Ok(())
}

#[test]
fn requirement_percent_remains_unreachable_style_terminal() -> Result<(), &'static str> {
    let parsed = parse(
        "requirementDiagram\nstyle A width:50%\nelement e {\n}\n",
        &[],
    );
    let d = parsed.diagnostics.first().ok_or("percent diagnostic")?;
    assert_eq!(d.code, "requirement/unexpected-token");
    assert_eq!(
        d.message,
        "unexpected %, expected one of: ALPHA, BRKT, COLON, LABEL, MINUS, NUM, PCT, SEMICOLON, SPACE, UNIT"
    );
    assert_eq!(d.span, Span { start: 35, end: 36 });
    assert_eq!(parsed.document.diagram.statements.len(), 1);
    Ok(())
}

#[test]
fn requirement_title_is_lexed_but_has_no_production() -> Result<(), &'static str> {
    let parsed = parse("requirementDiagram\ntitle unused\nelement e {\n}\n", &[]);
    let d = parsed.diagnostics.first().ok_or("title diagnostic")?;
    assert_eq!(d.code, "requirement/unexpected-token");
    assert_eq!(d.span, Span { start: 19, end: 31 });
    assert!(
        d.message
            .starts_with("unexpected title unused, expected one of: CLASS, CLASSDEF,"),
        "title token must report the expected statement alternatives: {:?}",
        d.message
    );
    assert_eq!(parsed.document.diagram.statements.len(), 1);
    Ok(())
}

#[test]
fn requirement_eof_reports_each_open_delimiter_once() -> Result<(), &'static str> {
    for (source, start, text) in [
        ("requirementDiagram\nrequirement r {\n", 33, "{"),
        ("requirementDiagram\nelement e {\n", 29, "{"),
        ("requirementDiagram\nelement \"é", 27, "\"é"),
        (
            "requirementDiagram\naccDescr {unfinished",
            28,
            "{unfinished",
        ),
        ("requirementDiagram\nrequirement r {\ntext: \"é", 41, "\"é"),
    ] {
        let parsed = parse(source, &[]);
        assert_eq!(parsed.diagnostics.len(), 1, "{source}");
        let d = parsed
            .diagnostics
            .first()
            .ok_or("unterminated diagnostic")?;
        assert_eq!(d.code, "requirement/unterminated");
        assert_eq!(
            d.span,
            Span {
                start,
                end: source.len()
            }
        );
        assert_eq!(d.message, format!("unterminated {text}"));
        assert!(
            parsed.document.diagram.statements.is_empty(),
            "unterminated construct must not leave partial statements: {:?}",
            parsed.document.diagram.statements
        );
    }
    Ok(())
}

#[test]
fn requirement_quoted_tokens_include_quotes_without_backslash_escaping() -> Result<(), &'static str>
{
    let tokens = lex("requirementDiagram\nelement \"\" {\n}\n\"a\\\"b\n", &[]);
    let quoted = tokens
        .iter()
        .filter(|t| t.kind == "qString")
        .collect::<Vec<_>>();
    assert_eq!(quoted.len(), 2);
    let empty = quoted.first().ok_or("empty quoted token")?;
    assert_eq!(empty.text, "");
    assert_eq!(empty.span, Span { start: 27, end: 29 });
    let escaped = quoted.get(1).ok_or("literal backslash")?;
    assert_eq!(escaped.text, "a\\");
    assert_eq!(escaped.span, Span { start: 34, end: 38 });
    Ok(())
}

#[test]
fn requirement_lexer_keeps_authority_modes_and_rule_precedence() -> Result<(), &'static str> {
    assert_eq!(
        MODES,
        [
            "INITIAL",
            "string",
            "token",
            "unqString",
            "style",
            "acc_title",
            "acc_descr",
            "acc_descr_multiline"
        ]
    );
    let tokens = lex("requirementDiagram\nstyle A x:12%;#fff\n", &[]);
    let kinds = tokens.iter().map(|t| t.kind).collect::<Vec<_>>();
    assert_eq!(
        kinds,
        [
            "RD",
            "NEWLINE",
            "STYLE",
            "ALPHA",
            "ALPHA",
            "COLON",
            "ALPHA",
            "PERCENT",
            "SEMICOLON",
            "BRKT",
            "ALPHA",
            "EOF"
        ]
    );
    let number = tokens.get(6).ok_or("style digits")?;
    assert_eq!(number.text, "12");
    assert_eq!(number.span, Span { start: 29, end: 31 });
    Ok(())
}

#[test]
fn requirement_removed_regions_preserve_source_offsets() -> Result<(), &'static str> {
    let source = "ignored\nrequirementDiagram\nelement e {\n}\n";
    let parsed = parse(source, &[Span { start: 0, end: 8 }]);
    assert!(
        parsed.diagnostics.is_empty(),
        "removed preprocessing region must not produce syntax diagnostics: {:?}",
        parsed.diagnostics
    );
    assert_eq!(parsed.document.header.span, Span { start: 8, end: 26 });
    let statement = parsed
        .document
        .diagram
        .statements
        .first()
        .ok_or("element")?;
    assert_eq!(statement.span, Span { start: 27, end: 40 });
    Ok(())
}

#[test]
fn requirement_invalid_frontmatter_fixtures_remain_rejected() -> Result<(), &'static str> {
    for source in [
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../corpus/requirement/mermaid/requirement~visual-check~with-a-theme-default.mmd"
        )),
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../corpus/requirement/mermaid/requirement~visual-check~with-a-title-default.mmd"
        )),
    ] {
        let parsed = parse(source, &[]);
        let d = parsed
            .diagnostics
            .first()
            .ok_or("invalid frontmatter must fail")?;
        assert_eq!(d.code, "requirement/unexpected-token");
        assert_eq!(d.message, "unexpected -, expected one of: RD");
        assert_eq!(source.get(d.span.start..d.span.end), Some("-"));
    }
    Ok(())
}

#[test]
fn requirement_risk_and_verification_alternatives_keep_typed_values() -> Result<(), &'static str> {
    let source = "requirementDiagram\nrequirement r {\nrisk: low\nrisk: medium\nrisk: high\nverifyMethod: analysis\nverifyMethod: demonstration\nverifyMethod: inspection\nverifyMethod: test\n}\n";
    let parsed = parse(source, &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let statement = parsed
        .document
        .diagram
        .statements
        .first()
        .ok_or("definition")?;
    let StatementKind::Requirement(def) = &statement.kind else {
        return Err("requirement");
    };
    let values = def
        .body
        .fields
        .iter()
        .filter_map(|f| match &f.value {
            RequirementFieldValue::Risk(risk) => Some(risk.value),
            RequirementFieldValue::Verify(verify) => Some(verify.value),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        values,
        [
            "Low",
            "Medium",
            "High",
            "Analysis",
            "Demonstration",
            "Inspection",
            "Test"
        ]
    );
    let field = def.body.fields.get(1).ok_or("medium risk")?;
    assert_eq!(field.span, Span { start: 45, end: 57 });
    Ok(())
}

#[test]
fn requirement_unknown_word_stays_unknown_and_does_not_consume_next_line()
-> Result<(), &'static str> {
    let parsed = parse("requirementDiagram\nnonsense\nelement e {\n}\n", &[]);
    let d = parsed.diagnostics.first().ok_or("unknown diagnostic")?;
    assert_eq!(parsed.diagnostics.len(), 1);
    assert_eq!(d.code, "requirement/unknown-statement");
    assert_eq!(d.message, "unknown statement nonsense");
    assert_eq!(d.span, Span { start: 19, end: 27 });
    assert_eq!(parsed.document.diagram.statements.len(), 1);
    Ok(())
}

#[test]
fn requirement_unknown_unquoted_word_message_drops_trailing_whitespace() -> Result<(), &'static str>
{
    let parsed = parse("requirementDiagram\n  req1 \n  req2   \n", &[]);
    assert_eq!(parsed.diagnostics.len(), 2);
    let first = parsed.diagnostics.first().ok_or("first diagnostic")?;
    assert_eq!(first.message, "unknown statement req1");
    assert_eq!(first.span, Span { start: 21, end: 26 });
    let second = parsed.diagnostics.get(1).ok_or("second diagnostic")?;
    assert_eq!(second.message, "unknown statement req2");
    assert_eq!(second.span, Span { start: 29, end: 36 });
    Ok(())
}

#[test]
fn requirement_style_quote_restores_style_mode_and_reports_eof() -> Result<(), &'static str> {
    let tokens = lex("requirementDiagram\nclass \"A\",B blue\n", &[]);
    let quoted = tokens
        .iter()
        .find(|t| t.kind == "qString")
        .ok_or("quoted target")?;
    assert_eq!(quoted.text, "A");
    assert_eq!(quoted.span, Span { start: 25, end: 28 });
    let tail = tokens
        .iter()
        .filter(|t| t.span.start >= 28)
        .map(|t| t.kind)
        .collect::<Vec<_>>();
    assert_eq!(tail, ["COMMA", "ALPHA", "ALPHA", "EOF"]);
    let parsed = parse("requirementDiagram\nstyle A \"unfinished", &[]);
    let d = parsed
        .diagnostics
        .first()
        .ok_or("unterminated style string")?;
    assert_eq!(d.code, "requirement/unterminated");
    assert_eq!(d.message, "unterminated \"unfinished");
    assert_eq!(d.span, Span { start: 27, end: 38 });
    Ok(())
}

#[test]
fn requirement_invalid_element_field_recovers_and_preserves_docref() -> Result<(), &'static str> {
    let parsed = parse(
        "requirementDiagram\nelement e {\nrisk: low\ndocref: doc\n}\n",
        &[],
    );
    let d = parsed.diagnostics.first().ok_or("invalid element field")?;
    assert_eq!(parsed.diagnostics.len(), 1);
    assert_eq!(d.code, "requirement/unexpected-token");
    assert_eq!(
        d.message,
        "unexpected risk, expected one of: DOCREF, NEWLINE, STRUCT_STOP, TYPE"
    );
    assert_eq!(d.span, Span { start: 31, end: 35 });
    let statement = parsed
        .document
        .diagram
        .statements
        .first()
        .ok_or("element")?;
    let StatementKind::Element(def) = &statement.kind else {
        return Err("element");
    };
    assert_eq!(def.body.fields.len(), 1);
    let field = def.body.fields.first().ok_or("docref")?;
    let ElementFieldValue::Ref(reference) = &field.value else {
        return Err("docref");
    };
    assert_eq!(reference.value, "doc");
    assert_eq!(reference.span, Span { start: 49, end: 52 });
    Ok(())
}

#[test]
fn requirement_lexer_groups_line_events_and_preserves_unquoted_trailing_span()
-> Result<(), &'static str> {
    let tokens = lex("requirementDiagram\n\nA café  - copies -> B\n", &[]);
    let newline = tokens.get(1).ok_or("grouped newline")?;
    assert_eq!(newline.kind, "NEWLINE");
    assert_eq!(newline.span, Span { start: 18, end: 20 });
    let name = tokens.get(2).ok_or("unquoted endpoint")?;
    assert_eq!(name.text, "A café");
    assert_eq!(name.span, Span { start: 20, end: 29 });
    Ok(())
}
