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
    let mut parser = Parser {
        source,
        tokens: lex_cleaned(&cleaned),
        cleaned,
        at: 0,
        diagnostics: Vec::new(),
    };
    while parser.kind() == "NEWLINE" {
        parser.at += 1;
    }
    let header = parser.expect("ER_DIAGRAM").unwrap_or(Token {
        kind: "ER_DIAGRAM",
        text: Cow::Borrowed(""),
        span: Span { start: 0, end: 0 },
    });
    let document = parser.document(0, header.span.end);
    Parsed {
        document: Start {
            span: Span {
                start: header.span.start,
                end: source.len(),
            },
            header,
            document,
        },
        diagnostics: parser.diagnostics,
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
    fn token(&self) -> Token<'a> {
        self.tokens.get(self.at).cloned().unwrap_or(Token {
            kind: "EOF",
            text: Cow::Borrowed(""),
            span: Span {
                start: self.source.len(),
                end: self.source.len(),
            },
        })
    }
    fn kind(&self) -> &'static str {
        self.tokens.get(self.at).map_or("EOF", |t| t.kind)
    }
    fn take(&mut self) -> Token<'a> {
        let token = self.token();
        if self.at < self.tokens.len() {
            self.at += 1;
        }
        token
    }
    fn end(&self) -> usize {
        self.tokens
            .get(self.at.saturating_sub(1))
            .map_or(0, |t| t.span.end)
    }
    fn span(&self, start: usize) -> Span {
        Span {
            start,
            end: self.end().max(start),
        }
    }
    fn unexpected(&mut self, expected: &str) {
        let token = self.token();
        self.diagnostics.push(diagnostic(
            "er/unexpected-token",
            format!(
                "unexpected {}, expected one of: {expected}",
                self.raw(token.span)
            ),
            token.span,
        ));
    }
    fn raw(&self, span: Span) -> Cow<'a, str> {
        self.cleaned.slice(span)
    }
    fn expect(&mut self, kind: &'static str) -> Option<Token<'a>> {
        if self.kind() == kind {
            return Some(self.take());
        }
        self.failed(kind);
        None
    }
    fn failed(&mut self, expected: &str) {
        if self.kind() == "UNTERMINATED" {
            let token = self.take();
            self.unterminated(&token.text, token.span.start);
        } else {
            self.unexpected(expected);
        }
    }
    fn unterminated(&mut self, opener: &str, start: usize) {
        if self
            .diagnostics
            .last()
            .is_some_and(|d| matches!(d.code, "er/unterminated" | "limit/nesting-depth"))
        {
            return;
        }
        self.diagnostics.push(diagnostic(
            "er/unterminated",
            format!("unterminated {opener}"),
            Span {
                start,
                end: self.source.len(),
            },
        ));
    }
    fn document(&mut self, depth: usize, start: usize) -> Document<'a> {
        let mut lines = Vec::new();
        while self.kind() != "EOF" && !(depth > 0 && self.kind() == "END") {
            if self.kind() == "NEWLINE" {
                let token = self.take();
                lines.push(Line {
                    span: token.span,
                    statement: None,
                });
                continue;
            }
            let before = self.at;
            if let Some(statement) = self.statement(depth) {
                lines.push(Line {
                    span: statement.span,
                    statement: Some(statement),
                });
            } else {
                self.recover("END");
                if self.kind() == "SEMI" {
                    self.take();
                }
            }
            if self.at == before {
                self.take();
            }
        }
        Document {
            span: Span {
                start: lines.first().map_or(start, |l| l.span.start),
                end: lines.last().map_or(start, |l| l.span.end),
            },
            lines,
        }
    }
    fn recover(&mut self, close: &str) {
        let mut end = self.token().span.start;
        while !matches!(self.kind(), "EOF" | "NEWLINE" | "SEMI") && self.kind() != close {
            let token = self.token();
            let gap = self.source.get(end..token.span.start).unwrap_or("");
            if gap.contains(['\r', '\n']) {
                return;
            }
            if token.kind == "UNTERMINATED" {
                self.failed("statement");
            } else {
                self.take();
            }
            end = self.end();
        }
    }
    fn statement(&mut self, depth: usize) -> Option<Statement<'a>> {
        let start = self.token().span.start;
        let kind = match self.kind() {
            "ENTITY_NAME" | "UNICODE_TEXT" | "NUM" | "DECIMAL_NUM" | "ENTITY_ONE" => {
                self.named()?
            }
            "SUBGRAPH" => self.subgraph(depth)?,
            "CLASSDEF" | "STYLE" | "CLASS" => self.style_statement()?,
            "acc_title" | "acc_descr" | "acc_descr_multiline_value" => self.accessibility()?,
            "direction_tb" | "direction_bt" | "direction_rl" | "direction_lr" => self.direction(),
            "UNTERMINATED" => {
                self.failed("statement");
                return None;
            }
            _ => {
                self.unknown();
                return None;
            }
        };
        let span = match &kind {
            StatementKind::ClassDef(statement) => statement.span,
            StatementKind::Style(statement) => statement.span,
            _ => self.span(start),
        };
        Some(Statement { span, kind })
    }
    fn unknown(&mut self) {
        let token = self.take();
        self.recover("END");
        self.diagnostics.push(diagnostic(
            "er/unknown-statement",
            format!("unknown statement {}", self.raw(token.span)),
            self.span(token.span.start),
        ));
    }
    fn entity_name(&mut self) -> Option<EntityName<'a>> {
        if !entity_kind(self.kind()) {
            self.failed("DECIMAL_NUM, ENTITY_NAME, ENTITY_ONE, NUM, UNICODE_TEXT");
            return None;
        }
        let token = self.take();
        Some(EntityName {
            span: token.span,
            name: token.text.clone(),
            token,
        })
    }
    fn inline_classes(&mut self) -> Option<Option<IdList<'a>>> {
        if self.kind() != "STYLE_SEPARATOR" {
            return Some(None);
        }
        self.take();
        Some(Some(self.id_list()?))
    }
    fn named(&mut self) -> Option<StatementKind<'a>> {
        let name = self.entity_name()?;
        let alias = self.alias()?;
        let classes = self.inline_classes()?;
        if cardinality_kind(self.kind()).is_some() {
            if alias.is_some() {
                self.unexpected("BLOCK_START, NEWLINE");
                return None;
            }
            return self.relationship(name, classes);
        }
        let (attributes, delimiters) = if self.kind() == "BLOCK_START" {
            let (attributes, delimiters) = self.attributes()?;
            (Some(attributes), Some(delimiters))
        } else {
            (None, None)
        };
        Some(StatementKind::Entity {
            name,
            alias,
            classes,
            attributes,
            delimiters,
        })
    }
    fn alias(&mut self) -> Option<Option<EntityName<'a>>> {
        if self.kind() != "SQS" {
            return Some(None);
        }
        self.take();
        let alias = self.entity_name()?;
        self.expect("SQE")?;
        Some(Some(alias))
    }
    fn relationship(
        &mut self,
        from: EntityName<'a>,
        from_classes: Option<IdList<'a>>,
    ) -> Option<StatementKind<'a>> {
        let relation = self.rel_spec()?;
        let to = self.entity_name()?;
        let to_classes = self.inline_classes()?;
        self.expect("COLON")?;
        let role = self.role()?;
        Some(StatementKind::Relationship {
            from,
            from_classes,
            relation: Box::new(relation),
            to,
            to_classes,
            role,
        })
    }
    fn rel_spec(&mut self) -> Option<RelSpec<'a>> {
        let left = self.cardinality()?;
        let start = left.span.start;
        if !matches!(self.kind(), "IDENTIFYING" | "NON_IDENTIFYING") {
            self.failed("IDENTIFYING, NON_IDENTIFYING");
            return None;
        }
        let token = self.take();
        let relation_type = RelType {
            span: token.span,
            identifying: token.kind == "IDENTIFYING",
            token,
        };
        let right = self.cardinality()?;
        Some(RelSpec {
            span: self.span(start),
            left,
            relation_type,
            right,
        })
    }
    fn cardinality(&mut self) -> Option<Cardinality<'a>> {
        let Some(kind) = cardinality_kind(self.kind()) else {
            self.failed("MD_PARENT, ONE_OR_MORE, ONLY_ONE, ZERO_OR_MORE, ZERO_OR_ONE");
            return None;
        };
        let token = self.take();
        Some(Cardinality {
            span: token.span,
            kind,
            token,
        })
    }
    fn role(&mut self) -> Option<Role<'a>> {
        if !matches!(self.kind(), "WORD" | "ENTITY_NAME" | "UNICODE_TEXT") {
            self.failed("ENTITY_NAME, UNICODE_TEXT, WORD");
            return None;
        }
        let token = self.take();
        Some(Role {
            span: token.span,
            label: token.text.clone(),
            token,
        })
    }
    fn attributes(&mut self) -> Option<(Attributes<'a>, (Span, Span))> {
        let open = self.take();
        let start = self.token().span.start;
        let mut attributes = Vec::new();
        while !matches!(self.kind(), "BLOCK_STOP" | "EOF") {
            let before = self.at;
            if let Some(attribute) = self.attribute() {
                attributes.push(attribute);
            } else {
                self.recover("BLOCK_STOP");
            }
            if before == self.at && self.kind() != "BLOCK_STOP" {
                self.take();
            }
        }
        if self.kind() == "EOF" {
            self.unterminated("{", open.span.start);
            return None;
        }
        let span = Span {
            start: attributes.first().map_or(start, |a| a.span.start),
            end: attributes.last().map_or(start, |a| a.span.end),
        };
        let close = self.take();
        Some((Attributes { span, attributes }, (open.span, close.span)))
    }
    fn attribute(&mut self) -> Option<Attribute<'a>> {
        let word = self.expect("ATTRIBUTE_WORD")?;
        let start = word.span.start;
        let question = if self.kind() == "?" {
            Some(self.take())
        } else {
            None
        };
        let attribute_type = AttributeType {
            span: self.span(start),
            word,
            question,
        };
        let word = self.expect("ATTRIBUTE_WORD")?;
        let name = AttributeName {
            span: word.span,
            word,
        };
        let keys = if self.kind() == "ATTRIBUTE_KEY" {
            Some(self.attribute_keys()?)
        } else {
            None
        };
        let comment = if self.kind() == "COMMENT" {
            let token = self.take();
            Some(AttributeComment {
                span: token.span,
                text: token.text,
            })
        } else {
            None
        };
        Some(Attribute {
            span: self.span(start),
            attribute_type,
            name,
            keys,
            comment,
        })
    }
    fn attribute_keys(&mut self) -> Option<AttributeKeyTypeList<'a>> {
        let start = self.token().span.start;
        let mut keys = vec![self.attribute_key()?];
        while self.kind() == "," {
            self.take();
            keys.push(self.attribute_key()?);
        }
        Some(AttributeKeyTypeList {
            span: self.span(start),
            keys,
        })
    }
    fn attribute_key(&mut self) -> Option<AttributeKeyType<'a>> {
        let token = self.expect("ATTRIBUTE_KEY")?;
        let value = if token.text.eq_ignore_ascii_case("PK") {
            "PK"
        } else if token.text.eq_ignore_ascii_case("FK") {
            "FK"
        } else {
            "UK"
        };
        Some(AttributeKeyType {
            span: token.span,
            token,
            value,
        })
    }
    fn id_list(&mut self) -> Option<IdList<'a>> {
        let start = self.token().span.start;
        let mut names = vec![self.id()?];
        while self.kind() == "COMMA" {
            self.take();
            names.push(self.id()?);
        }
        Some(IdList {
            span: self.span(start),
            names,
        })
    }
    fn id(&mut self) -> Option<Token<'a>> {
        if matches!(self.kind(), "STYLE_TEXT" | "UNICODE_TEXT") {
            return Some(self.take());
        }
        self.failed("STYLE_TEXT, UNICODE_TEXT");
        None
    }
    fn styles(&mut self) -> Option<StylesOpt<'a>> {
        let start = self.token().span.start;
        let mut styles = vec![self.style()?];
        while self.kind() == "COMMA" {
            self.take();
            styles.push(self.style()?);
        }
        Some(StylesOpt {
            span: self.span(start),
            styles,
        })
    }
    fn style(&mut self) -> Option<Style<'a>> {
        let start = self.token().span.start;
        let mut components = Vec::new();
        while matches!(self.kind(), "STYLE_TEXT" | "NUM" | "COLON" | "BRKT") {
            let token = self.take();
            components.push(StyleComponent {
                span: token.span,
                token,
            });
        }
        if components.is_empty() {
            self.failed("BRKT, COLON, NUM, STYLE_TEXT");
            return None;
        }
        Some(Style {
            span: self.span(start),
            components,
        })
    }
    fn style_statement(&mut self) -> Option<StatementKind<'a>> {
        let token = self.take();
        let targets = self.id_list()?;
        if token.kind == "CLASS" {
            let classes = self.id_list()?;
            return Some(StatementKind::Class(ClassStatement {
                span: self.span(token.span.start),
                targets,
                classes,
            }));
        }
        let styles = self.styles()?;
        let span = self.span(token.span.start);
        self.separator()?;
        if token.kind == "CLASSDEF" {
            Some(StatementKind::ClassDef(ClassDefStatement {
                span,
                ids: targets,
                styles,
            }))
        } else {
            Some(StatementKind::Style(StyleStatement {
                span,
                targets,
                styles,
            }))
        }
    }
    fn separator(&mut self) -> Option<Separator<'a>> {
        if !matches!(self.kind(), "SEMI" | "NEWLINE" | "EOF") {
            self.failed("EOF, NEWLINE, SEMI");
            return None;
        }
        let token = self.take();
        Some(Separator {
            span: token.span,
            token,
        })
    }
    fn accessibility(&mut self) -> Option<StatementKind<'a>> {
        let token = self.take();
        if token.kind == "acc_descr_multiline_value" {
            return Some(StatementKind::Accessibility {
                title: false,
                value: token,
            });
        }
        let title = token.kind == "acc_title";
        let value = self.expect(if title {
            "acc_title_value"
        } else {
            "acc_descr_value"
        })?;
        Some(StatementKind::Accessibility { title, value })
    }
    fn direction(&mut self) -> StatementKind<'a> {
        let token = self.take();
        let value = match token.kind {
            "direction_tb" => "TB",
            "direction_bt" => "BT",
            "direction_rl" => "RL",
            _ => "LR",
        };
        StatementKind::Direction(Direction {
            span: token.span,
            value,
        })
    }
    fn subgraph(&mut self, depth: usize) -> Option<StatementKind<'a>> {
        let open = self.take();
        if depth >= 64 {
            self.diagnostics.push(diagnostic(
                "limit/nesting-depth",
                "nesting depth exceeds 64".into(),
                open.span,
            ));
            self.at = self.tokens.len();
            return None;
        }
        let id = self.entity_name()?;
        let title = self.subgraph_title()?;
        let header = SubgraphHeader {
            span: self.span(open.span.start),
            id,
            title,
        };
        self.separator()?;
        let document = self.document(depth + 1, self.end());
        if self.kind() == "EOF" {
            self.unterminated("subgraph", open.span.start);
            return None;
        }
        let close = self.expect("END")?;
        Some(StatementKind::Subgraph {
            header,
            document,
            close,
        })
    }
    fn subgraph_title(&mut self) -> Option<Option<SubgraphTitle<'a>>> {
        if self.kind() != "SQS" {
            return Some(None);
        }
        self.take();
        let first = self.entity_name()?;
        let start = first.span.start;
        let mut parts = vec![first];
        while entity_kind(self.kind()) {
            parts.push(self.entity_name()?);
        }
        let span = self.span(start);
        self.expect("SQE")?;
        Some(Some(SubgraphTitle { span, parts }))
    }
}

fn entity_kind(kind: &str) -> bool {
    matches!(
        kind,
        "ENTITY_NAME" | "UNICODE_TEXT" | "NUM" | "DECIMAL_NUM" | "ENTITY_ONE"
    )
}
fn cardinality_kind(kind: &str) -> Option<CardinalityKind> {
    match kind {
        "ZERO_OR_ONE" => Some(CardinalityKind::ZeroOrOne),
        "ZERO_OR_MORE" => Some(CardinalityKind::ZeroOrMore),
        "ONE_OR_MORE" => Some(CardinalityKind::OneOrMore),
        "ONLY_ONE" => Some(CardinalityKind::OnlyOne),
        "MD_PARENT" => Some(CardinalityKind::MdParent),
        _ => None,
    }
}
