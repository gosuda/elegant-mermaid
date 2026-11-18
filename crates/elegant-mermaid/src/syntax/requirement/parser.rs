use std::borrow::Cow;

use super::{
    ast::*,
    diagnostic,
    lexer::{Token, lex_cleaned},
};
use crate::{
    diag::Diagnostic,
    source::{Span, cleaned::Cleaned},
};

pub struct Parsed<'a> {
    pub document: Start<'a>,
    pub diagnostics: Vec<Diagnostic>,
}

pub fn parse<'a>(source: &'a str, removed: &[Span]) -> Parsed<'a> {
    let cleaned = Cleaned::new(source, removed);
    let mut p = Parser {
        source,
        tokens: lex_cleaned(&cleaned),
        cleaned,
        at: 0,
        diagnostics: Vec::new(),
    };
    p.newlines();
    let mut directives = Vec::new();
    while is_directive(p.kind()) {
        if let Some(directive) = p.directive() {
            directives.push(directive);
        }
        p.newlines();
    }
    let header = p.header();
    let diagram = p.diagram(p.end());
    let start = directives
        .first()
        .map_or(header.span.start, |d| d.span.start);
    Parsed {
        document: Start {
            span: Span {
                start,
                end: source.len(),
            },
            header,
            diagram,
            directives,
        },
        diagnostics: p.diagnostics,
    }
}

struct Parser<'a> {
    source: &'a str,
    cleaned: Cleaned<'a>,
    tokens: Vec<Token<'a>>,
    at: usize,
    diagnostics: Vec<Diagnostic>,
}

impl<'a> Parser<'a> {
    fn kind(&self) -> &'static str {
        self.tokens.get(self.at).map_or("EOF", |t| t.kind)
    }
    fn header(&mut self) -> Token<'a> {
        let Some(header) = self.expect("RD") else {
            return Token {
                kind: "RD",
                text: Cow::Borrowed(""),
                span: self.span(),
            };
        };
        let _ = self.expect("NEWLINE");
        header
    }
    fn span(&self) -> Span {
        self.tokens.get(self.at).map_or(
            Span {
                start: self.source.len(),
                end: self.source.len(),
            },
            |t| t.span,
        )
    }
    fn take(&mut self) -> Option<Token<'a>> {
        let token = self.tokens.get(self.at)?.clone();
        self.at += 1;
        Some(token)
    }
    fn end(&self) -> usize {
        self.tokens
            .get(self.at.saturating_sub(1))
            .map_or(0, |t| t.span.end)
    }
    fn since(&self, start: usize) -> Span {
        Span {
            start,
            end: self.end(),
        }
    }
    fn newlines(&mut self) {
        while self.kind() == "NEWLINE" {
            self.at += 1;
        }
    }
    fn unexpected(&mut self, expected: &str) {
        let span = self.span();
        let text = self.cleaned.slice(span);
        self.diagnostics.push(diagnostic(
            "requirement/unexpected-token",
            format!("unexpected {text}, expected one of: {expected}"),
            span,
        ));
    }
    fn expect(&mut self, kind: &'static str) -> Option<Token<'a>> {
        if self.kind() == kind {
            return self.take();
        }
        self.reject(kind);
        None
    }
    fn reject(&mut self, expected: &str) {
        if self.kind() == "UNTERMINATED" {
            self.unterminated();
        } else {
            self.unexpected(expected);
        }
    }
    fn unterminated(&mut self) {
        if let Some(t) = self.take() {
            self.diagnostics.push(diagnostic(
                "requirement/unterminated",
                format!("unterminated {}", t.text),
                t.span,
            ));
        }
    }
    fn recover(&mut self) {
        if self.line_break(self.end(), self.span().start) {
            return;
        }
        while !matches!(self.kind(), "EOF" | "NEWLINE" | "STRUCT_STOP") {
            let end = self.span().end;
            if self.kind() == "UNTERMINATED" {
                self.unterminated();
            } else {
                self.at += 1;
            }
            if self.line_break(end, self.span().start) {
                break;
            }
        }
    }
    fn line_break(&self, start: usize, end: usize) -> bool {
        self.cleaned
            .slice(Span { start, end })
            .contains(['\r', '\n'])
    }
    fn unknown(&mut self) {
        let Some(t) = self.take() else {
            return;
        };
        let end = if self.line_break(t.span.end, self.span().start) {
            t.span.end
        } else {
            self.recover();
            self.end()
        };
        self.diagnostics.push(diagnostic(
            "requirement/unknown-statement",
            format!("unknown statement {}", t.text),
            Span {
                start: t.span.start,
                end,
            },
        ));
    }
    fn diagram(&mut self, body_start: usize) -> Diagram<'a> {
        let mut statements = Vec::new();
        while self.kind() != "EOF" {
            self.newlines();
            if self.kind() == "EOF" {
                break;
            }
            let before = self.at;
            if let Some(statement) = self.statement() {
                statements.push(statement);
            } else {
                self.recover();
            }
            if self.at == before {
                self.at += 1;
            }
        }
        Diagram {
            span: Span {
                start: statements.first().map_or(body_start, |s| s.span.start),
                end: statements.last().map_or(body_start, |s| s.span.end),
            },
            statements,
        }
    }
    fn statement(&mut self) -> Option<Statement<'a>> {
        let start = self.span().start;
        let kind = match self.kind() {
            k if requirement_type(k).is_some() => StatementKind::Requirement(self.requirement()?),
            "ELEMENT" => StatementKind::Element(self.element()?),
            "unqString" | "qString" => self.named()?,
            "STYLE" | "CLASSDEF" | "CLASS" => self.styled()?,
            k if is_directive(k) => StatementKind::Directive(self.directive()?),
            "direction_tb" | "direction_bt" | "direction_rl" | "direction_lr" => {
                self.direction()?
            }
            "title" => {
                self.unexpected(STATEMENTS);
                self.at += 1;
                return None;
            }
            "UNTERMINATED" => {
                self.unterminated();
                return None;
            }
            _ => {
                self.unknown();
                return None;
            }
        };
        Some(Statement {
            span: self.since(start),
            kind,
        })
    }
    fn value(&mut self) -> Option<Token<'a>> {
        if matches!(self.kind(), "unqString" | "qString") {
            return self.take();
        }
        self.reject("qString, unqString");
        None
    }
    fn id(&mut self) -> Option<Id<'a>> {
        let t = self.value()?;
        Some(Id {
            span: t.span,
            quoted: t.kind == "qString",
            value: t.text,
        })
    }
    fn id_list(&mut self) -> Option<IdList<'a>> {
        let first = self.list_name()?;
        let start = first.span.start;
        let mut names = vec![first];
        while self.kind() == "COMMA" {
            self.at += 1;
            names.push(self.list_name()?);
        }
        Some(IdList {
            span: self.since(start),
            names,
        })
    }
    fn list_name(&mut self) -> Option<Id<'a>> {
        if !matches!(self.kind(), "ALPHA" | "unqString" | "qString") {
            self.reject("ALPHA, qString, unqString");
            return None;
        }
        let t = self.take()?;
        Some(Id {
            span: t.span,
            quoted: t.kind == "qString",
            value: t.text,
        })
    }
    fn inline_classes(&mut self) -> Option<Option<IdList<'a>>> {
        if self.kind() != "STYLE_SEPARATOR" {
            return Some(None);
        }
        self.at += 1;
        Some(Some(self.id_list()?))
    }
    fn open_body(&mut self) -> Option<Token<'a>> {
        let open = self.expect("STRUCT_START")?;
        if self.kind() == "EOF" {
            let _ = self.close_body(open.span);
            return None;
        }
        self.expect("NEWLINE")?;
        Some(open)
    }
    fn close_body(&mut self, opening: Span) -> Option<Token<'a>> {
        if self.kind() != "EOF" {
            return self.expect("STRUCT_STOP");
        }
        if !self
            .diagnostics
            .last()
            .is_some_and(|d| d.code == "requirement/unterminated")
        {
            self.diagnostics.push(diagnostic(
                "requirement/unterminated",
                "unterminated {".into(),
                Span {
                    start: opening.start,
                    end: self.source.len(),
                },
            ));
        }
        None
    }
    fn requirement(&mut self) -> Option<RequirementDef<'a>> {
        let keyword = self.take()?;
        let requirement_type = RequirementType {
            span: keyword.span,
            value: requirement_type(keyword.kind)?,
        };
        let name = self.value()?;
        let classes = self.inline_classes()?;
        let open = self.open_body()?;
        let body = self.requirement_body(open.span)?;
        let closing = self.tokens.get(self.at.saturating_sub(1))?.span;
        Some(RequirementDef {
            span: self.since(keyword.span.start),
            requirement_type,
            name: RequirementName {
                span: name.span,
                quoted: name.kind == "qString",
                value: name.text,
            },
            classes,
            body,
            delimiters: (open.span, closing),
        })
    }
    fn requirement_body(&mut self, opening: Span) -> Option<RequirementBody<'a>> {
        let mut fields = Vec::new();
        while !matches!(self.kind(), "STRUCT_STOP" | "EOF") {
            self.newlines();
            if matches!(self.kind(), "STRUCT_STOP" | "EOF") {
                break;
            }
            let before = self.at;
            if let Some(field) = self.requirement_field() {
                fields.push(field);
            } else {
                self.recover();
            }
            if self.at == before {
                self.at += 1;
            }
        }
        let close = self.close_body(opening)?;
        Some(RequirementBody {
            span: Span {
                start: fields.first().map_or(close.span.start, |f| f.span.start),
                end: close.span.end,
            },
            fields,
        })
    }
    fn requirement_field(&mut self) -> Option<RequirementField<'a>> {
        if !matches!(self.kind(), "ID" | "TEXT" | "RISK" | "VERIFYMTHD") {
            self.reject("ID, NEWLINE, RISK, STRUCT_STOP, TEXT, VERIFYMTHD");
            return None;
        }
        let keyword = self.take()?;
        let colon = self.expect("COLONSEP")?.span;
        let value = match keyword.kind {
            "ID" => RequirementFieldValue::Id(self.id()?),
            "TEXT" => {
                let t = self.value()?;
                RequirementFieldValue::Text(Text {
                    span: t.span,
                    quoted: t.kind == "qString",
                    value: t.text,
                })
            }
            "RISK" => RequirementFieldValue::Risk(self.risk()?),
            _ => RequirementFieldValue::Verify(self.verify()?),
        };
        let span = self.since(keyword.span.start);
        self.expect("NEWLINE")?;
        Some(RequirementField {
            span,
            keyword,
            colon,
            value,
        })
    }
    fn risk(&mut self) -> Option<RiskLevel> {
        let value = match self.kind() {
            "LOW_RISK" => "Low",
            "MED_RISK" => "Medium",
            "HIGH_RISK" => "High",
            _ => {
                self.reject("HIGH_RISK, LOW_RISK, MED_RISK");
                return None;
            }
        };
        Some(RiskLevel {
            span: self.take()?.span,
            value,
        })
    }
    fn verify(&mut self) -> Option<VerifyType> {
        let value = match self.kind() {
            "VERIFY_ANALYSIS" => "Analysis",
            "VERIFY_DEMONSTRATION" => "Demonstration",
            "VERIFY_INSPECTION" => "Inspection",
            "VERIFY_TEST" => "Test",
            _ => {
                self.reject(
                    "VERIFY_ANALYSIS, VERIFY_DEMONSTRATION, VERIFY_INSPECTION, VERIFY_TEST",
                );
                return None;
            }
        };
        Some(VerifyType {
            span: self.take()?.span,
            value,
        })
    }
    fn element(&mut self) -> Option<ElementDef<'a>> {
        let keyword = self.take()?;
        let name = self.value()?;
        let classes = self.inline_classes()?;
        let open = self.open_body()?;
        let body = self.element_body(open.span)?;
        let closing = self.tokens.get(self.at.saturating_sub(1))?.span;
        Some(ElementDef {
            span: self.since(keyword.span.start),
            name: ElementName {
                span: name.span,
                quoted: name.kind == "qString",
                value: name.text,
            },
            classes,
            body,
            delimiters: (open.span, closing),
        })
    }
    fn element_body(&mut self, opening: Span) -> Option<ElementBody<'a>> {
        let mut fields = Vec::new();
        while !matches!(self.kind(), "STRUCT_STOP" | "EOF") {
            self.newlines();
            if matches!(self.kind(), "STRUCT_STOP" | "EOF") {
                break;
            }
            let before = self.at;
            if let Some(field) = self.element_field() {
                fields.push(field);
            } else {
                self.recover();
            }
            if self.at == before {
                self.at += 1;
            }
        }
        let close = self.close_body(opening)?;
        Some(ElementBody {
            span: Span {
                start: fields.first().map_or(close.span.start, |f| f.span.start),
                end: close.span.end,
            },
            fields,
        })
    }
    fn element_field(&mut self) -> Option<ElementField<'a>> {
        if !matches!(self.kind(), "TYPE" | "DOCREF") {
            self.reject("DOCREF, NEWLINE, STRUCT_STOP, TYPE");
            return None;
        }
        let keyword = self.take()?;
        let colon = self.expect("COLONSEP")?.span;
        let t = self.value()?;
        let quoted = t.kind == "qString";
        let value = match keyword.kind {
            "TYPE" => ElementFieldValue::Type(Type {
                span: t.span,
                quoted,
                value: t.text,
            }),
            _ => ElementFieldValue::Ref(Ref {
                span: t.span,
                quoted,
                value: t.text,
            }),
        };
        let span = self.since(keyword.span.start);
        self.expect("NEWLINE")?;
        Some(ElementField {
            span,
            keyword,
            colon,
            value,
        })
    }
    fn named(&mut self) -> Option<StatementKind<'a>> {
        let next = self.tokens.get(self.at + 1).map_or("EOF", |t| t.kind);
        if !matches!(next, "STYLE_SEPARATOR" | "LINE" | "END_ARROW_L") {
            self.unknown();
            return None;
        }
        let left = self.id()?;
        if self.kind() == "STYLE_SEPARATOR" {
            let separator = self.take()?.span;
            let classes = self.id_list()?;
            let span = self.since(left.span.start);
            let targets = IdList {
                span: left.span,
                names: vec![left],
            };
            return Some(StatementKind::Class(ClassStatement {
                span,
                targets,
                classes,
                separator: Some(separator),
            }));
        }
        self.relationship(left).map(StatementKind::Relationship)
    }
    fn relationship(&mut self, left: Id<'a>) -> Option<RelationshipDef<'a>> {
        let first = self.take()?;
        let relationship = self.relation_kind()?;
        let (arrow, line) = if first.kind == "END_ARROW_L" {
            (first, self.expect("LINE")?.span)
        } else {
            (self.expect("END_ARROW_R")?, first.span)
        };
        let right = self.id()?;
        Some(RelationshipDef {
            span: self.since(left.span.start),
            left,
            right,
            relationship,
            reversed: arrow.kind == "END_ARROW_L",
            arrow,
            line,
        })
    }
    fn relation_kind(&mut self) -> Option<Relationship> {
        let value = match self.kind() {
            "CONTAINS" => "contains",
            "COPIES" => "copies",
            "DERIVES" => "derives",
            "SATISFIES" => "satisfies",
            "VERIFIES" => "verifies",
            "REFINES" => "refines",
            "TRACES" => "traces",
            _ => {
                self.reject("CONTAINS, COPIES, DERIVES, REFINES, SATISFIES, TRACES, VERIFIES");
                return None;
            }
        };
        Some(Relationship {
            span: self.take()?.span,
            value,
        })
    }
    fn directive(&mut self) -> Option<Directive<'a>> {
        let first = self.take()?;
        let value = match first.kind {
            "acc_title" => self.expect("acc_title_value")?,
            "acc_descr" => self.expect("acc_descr_value")?,
            _ => first.clone(),
        };
        Some(Directive {
            span: self.since(first.span.start),
            title: first.kind == "acc_title",
            multiline: first.kind == "acc_descr_multiline_value",
            value,
        })
    }
    fn direction(&mut self) -> Option<StatementKind<'a>> {
        let t = self.take()?;
        let value = match t.kind {
            "direction_tb" => "TB",
            "direction_bt" => "BT",
            "direction_rl" => "RL",
            _ => "LR",
        };
        Some(StatementKind::Direction(Direction {
            span: t.span,
            value,
        }))
    }
    fn styled(&mut self) -> Option<StatementKind<'a>> {
        let keyword = self.take()?;
        let ids = self.id_list()?;
        if keyword.kind == "CLASS" {
            let classes = self.id_list()?;
            return Some(StatementKind::Class(ClassStatement {
                span: self.since(keyword.span.start),
                targets: ids,
                classes,
                separator: None,
            }));
        }
        let styles = self.styles()?;
        let span = self.since(keyword.span.start);
        if keyword.kind == "CLASSDEF" {
            Some(StatementKind::ClassDef(ClassDefStatement {
                span,
                ids,
                styles,
            }))
        } else {
            Some(StatementKind::Style(StyleStatement { span, ids, styles }))
        }
    }
    fn styles(&mut self) -> Option<StylesOpt<'a>> {
        let first = self.style()?;
        let start = first.span.start;
        let mut styles = vec![first];
        while self.kind() == "COMMA" && !self.line_break(self.end(), self.span().start) {
            self.at += 1;
            styles.push(self.style()?);
        }
        if !matches!(self.kind(), "EOF" | "NEWLINE")
            && !self.line_break(self.end(), self.span().start)
        {
            self.reject(STYLE_COMPONENTS);
            return None;
        }
        Some(StylesOpt {
            span: self.since(start),
            styles,
        })
    }
    fn style(&mut self) -> Option<Style<'a>> {
        let start = self.span().start;
        let mut components = Vec::new();
        while is_component(self.kind()) && !self.line_break(self.end(), self.span().start) {
            let t = self.take()?;
            components.push(StyleComponent {
                span: t.span,
                kind: t.kind,
                text: t.text,
            });
        }
        if components.is_empty() {
            self.reject(STYLE_COMPONENTS);
            return None;
        }
        Some(Style {
            span: self.since(start),
            components,
        })
    }
}

const STATEMENTS: &str = "CLASS, CLASSDEF, DESIGN_CONSTRAINT, ELEMENT, EOF, FUNCTIONAL_REQUIREMENT, INTERFACE_REQUIREMENT, NEWLINE, PERFORMANCE_REQUIREMENT, PHYSICAL_REQUIREMENT, REQUIREMENT, STYLE, acc_descr, acc_descr_multiline_value, acc_title, direction_bt, direction_lr, direction_rl, direction_tb, qString, unqString";
const STYLE_COMPONENTS: &str = "ALPHA, BRKT, COLON, LABEL, MINUS, NUM, PCT, SEMICOLON, SPACE, UNIT";

fn is_directive(kind: &str) -> bool {
    matches!(
        kind,
        "acc_title" | "acc_descr" | "acc_descr_multiline_value"
    )
}
fn is_component(kind: &str) -> bool {
    matches!(
        kind,
        "ALPHA"
            | "NUM"
            | "COLON"
            | "UNIT"
            | "SPACE"
            | "BRKT"
            | "PCT"
            | "MINUS"
            | "LABEL"
            | "SEMICOLON"
    )
}
fn requirement_type(kind: &str) -> Option<&'static str> {
    match kind {
        "REQUIREMENT" => Some("Requirement"),
        "FUNCTIONAL_REQUIREMENT" => Some("Functional Requirement"),
        "INTERFACE_REQUIREMENT" => Some("Interface Requirement"),
        "PERFORMANCE_REQUIREMENT" => Some("Performance Requirement"),
        "PHYSICAL_REQUIREMENT" => Some("Physical Requirement"),
        "DESIGN_CONSTRAINT" => Some("Design Constraint"),
        _ => None,
    }
}
