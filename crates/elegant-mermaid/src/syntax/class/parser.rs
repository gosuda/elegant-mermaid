use super::{
    ast::*,
    diagnostic,
    lexer::{Token, lex},
};
use crate::{diag::Diagnostic, source::Span};

pub struct Parsed<'a> {
    pub document: Start<'a>,
    pub diagnostics: Vec<Diagnostic>,
}

pub fn parse<'a>(source: &'a str, removed: &[Span]) -> Parsed<'a> {
    let mut parser = Parser {
        source,
        tokens: lex(source, removed),
        at: 0,
        diagnostics: Vec::new(),
    };
    while parser.kind() == "NEWLINE" {
        parser.at += 1;
    }
    if parser.kind() == "CLASS_DIAGRAM" {
        parser.at += 1;
    }
    let statements = parser.statements(0);
    if parser.kind() == "STRUCT_STOP" {
        parser.unexpected("EOF");
    }
    Parsed {
        document: Start {
            span: Span {
                start: 0,
                end: source.len(),
            },
            statements,
        },
        diagnostics: parser.diagnostics,
    }
}

struct Parser<'a> {
    source: &'a str,
    tokens: Vec<Token<'a>>,
    at: usize,
    diagnostics: Vec<Diagnostic>,
}

impl<'a> Parser<'a> {
    fn kind(&self) -> &'static str {
        self.tokens.get(self.at).map_or("EOF", |t| t.kind)
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
    fn expect(&mut self, kind: &'static str) -> Option<Token<'a>> {
        if self.kind() == kind {
            return self.take();
        }
        if self.kind() == "UNTERMINATED" {
            self.unterminated();
            return None;
        }
        self.unexpected(kind);
        None
    }
    fn unexpected(&mut self, expected: &str) {
        let span = self.tokens.get(self.at).map_or(
            Span {
                start: self.source.len(),
                end: self.source.len(),
            },
            |t| t.span,
        );
        let text = &self.source[span.start..span.end];
        self.diagnostics.push(diagnostic(
            "class/unexpected-token",
            format!("unexpected {text}, expected one of: {expected}"),
            span,
        ));
    }
    fn recover(&mut self) {
        while !matches!(self.kind(), "EOF" | "NEWLINE" | "STRUCT_STOP") {
            self.at += 1;
        }
    }
    fn statements(&mut self, depth: usize) -> Vec<Statement<'a>> {
        let mut statements = Vec::new();
        while !matches!(self.kind(), "EOF" | "STRUCT_STOP") {
            if self.kind() == "NEWLINE" {
                self.at += 1;
                continue;
            }
            if depth > 0 && !matches!(self.kind(), "CLASS" | "NAMESPACE" | "NOTE") {
                self.unexpected("CLASS, NAMESPACE, NOTE");
                self.recover();
                continue;
            }
            let at = self.at;
            if let Some(statement) = self.statement(depth) {
                statements.push(statement);
            }
            if self.at == at {
                self.at += 1;
            }
            if !matches!(self.kind(), "EOF" | "NEWLINE" | "STRUCT_STOP") {
                self.unexpected("NEWLINE");
                self.recover();
            }
        }
        statements
    }
    fn statement(&mut self, depth: usize) -> Option<Statement<'a>> {
        match self.kind() {
            "CLASS" => self.class(depth).map(Statement::Class),
            "NAMESPACE" => self.namespace(depth).map(Statement::Namespace),
            "ANNOTATION_START" => self.annotation(),
            "NOTE" => self.note(),
            "DIRECTION" => self.direction(),
            "STYLE" | "CLASSDEF" | "CSSCLASS" | "CLICK" => self.metadata(),
            "ALPHA" | "BQUOTE_STR" | "MINUS" => self.named(),
            "UNTERMINATED" => {
                self.unterminated();
                None
            }
            _ => {
                self.unknown();
                None
            }
        }
    }
    fn unknown(&mut self) {
        let Some(token) = self.take() else {
            return;
        };
        self.recover();
        self.diagnostics.push(diagnostic(
            "class/unknown-statement",
            format!("unknown statement {}", token.text),
            Span {
                start: token.span.start,
                end: self.end(),
            },
        ));
    }
    fn unterminated(&mut self) {
        if let Some(token) = self.take() {
            self.diagnostics.push(diagnostic(
                "class/unterminated",
                format!("unterminated {}", token.text),
                Span {
                    start: token.span.start,
                    end: self.source.len(),
                },
            ));
        }
    }
    fn name(&mut self) -> Option<ClassName<'a>> {
        if self.kind() == "UNTERMINATED" {
            self.unterminated();
            return None;
        }
        let first = self.tokens.get(self.at)?.span.start;
        let mut tokens = Vec::new();
        let mut value = String::new();
        let mut generic = String::new();
        while matches!(
            self.kind(),
            "ALPHA" | "BQUOTE_STR" | "MINUS" | "DOT" | "GENERICTYPE"
        ) {
            let token = self.take()?;
            if token.kind == "GENERICTYPE" {
                generic = token.text.into();
            } else {
                value.push_str(token.text);
            }
            tokens.push(token);
        }
        if self.kind() == "UNTERMINATED" {
            self.unterminated();
            return None;
        }
        if value.is_empty() {
            self.unexpected("ALPHA, BQUOTE_STR");
            return None;
        }
        Some(ClassName {
            span: Span {
                start: first,
                end: self.end(),
            },
            tokens,
            value,
            generic,
        })
    }
    fn label(&mut self) -> Option<&'a str> {
        if self.kind() != "SQS" {
            return None;
        }
        self.at += 1;
        let value = self.expect("STR")?.text;
        self.expect("SQE")?;
        Some(value)
    }
    fn class(&mut self, depth: usize) -> Option<ClassStatement<'a>> {
        let start = self.take()?.span.start;
        let name = self.name()?;
        let label = self.label();
        let annotation = if self.kind() == "ANNOTATION_START" {
            Some(self.annotation_value()?)
        } else {
            None
        };
        let css_class = self.css_shorthand();
        let has_body = self.kind() == "STRUCT_START";
        let members = if has_body {
            self.members(depth)?
        } else {
            Vec::new()
        };
        if css_class.is_some() && has_body && members.is_empty() {
            self.unexpected("MEMBER");
            return None;
        }
        Some(ClassStatement {
            span: Span {
                start,
                end: self.end(),
            },
            name,
            label,
            css_class,
            annotation,
            members,
            has_body,
        })
    }
    fn css_shorthand(&mut self) -> Option<&'a str> {
        if self.kind() != "COLON" {
            return None;
        }
        let start = self.at;
        for _ in 0..3 {
            if self.kind() != "COLON" {
                self.at = start;
                return None;
            }
            self.at += 1;
        }
        self.take().map(|t| t.text)
    }
    fn open(&mut self, depth: usize) -> Option<Token<'a>> {
        let token = self.expect("STRUCT_START")?;
        if depth >= 64 {
            self.diagnostics.push(diagnostic(
                "limit/nesting-depth",
                "nesting depth exceeds 64".into(),
                token.span,
            ));
            self.at = self.tokens.len();
            return None;
        }
        Some(token)
    }
    fn close(&mut self, opening: &Token<'a>) -> bool {
        if self.kind() == "STRUCT_STOP" {
            self.at += 1;
            return true;
        }
        if self
            .diagnostics
            .last()
            .is_some_and(|diagnostic| diagnostic.code == "limit/nesting-depth")
        {
            return false;
        }
        self.diagnostics.push(diagnostic(
            "class/unterminated",
            format!("unterminated {}", opening.text),
            Span {
                start: opening.span.start,
                end: self.source.len(),
            },
        ));
        false
    }
    fn members(&mut self, depth: usize) -> Option<Vec<MemberStatement<'a>>> {
        let opening = self.open(depth)?;
        let mut members = Vec::new();
        while !matches!(self.kind(), "EOF" | "STRUCT_STOP") {
            if self.kind() == "STRUCT_START" {
                let token = self.take()?;
                self.diagnostics.push(diagnostic(
                    "class/nested-member-block",
                    "class member cannot contain a block".into(),
                    token.span,
                ));
                self.recover();
                continue;
            }
            if self.kind() == "NEWLINE" {
                self.at += 1;
                continue;
            }
            let start = self.tokens[self.at].span.start;
            while !matches!(
                self.kind(),
                "EOF" | "NEWLINE" | "STRUCT_START" | "STRUCT_STOP"
            ) {
                self.at += 1;
            }
            let span = Span {
                start,
                end: self.end(),
            };
            members.push(MemberStatement {
                span,
                text: &self.source[span.start..span.end],
            });
        }
        if !self.close(&opening) {
            return None;
        }
        Some(members)
    }
    fn namespace(&mut self, depth: usize) -> Option<NamespaceStatement<'a>> {
        let start = self.take()?.span.start;
        let name = self.name()?;
        let label = self.label();
        let opening = self.open(depth)?;
        let children = self.statements(depth + 1);
        if children.is_empty() {
            self.unexpected("CLASS, NAMESPACE, NOTE");
        }
        self.close(&opening);
        Some(NamespaceStatement {
            span: Span {
                start,
                end: self.end(),
            },
            name,
            label,
            children,
        })
    }
    fn annotation_value(&mut self) -> Option<String> {
        self.expect("ANNOTATION_START")?;
        let value = self.take()?.text.to_owned();
        self.expect("ANNOTATION_END")?;
        Some(value)
    }
    fn annotation(&mut self) -> Option<Statement<'a>> {
        let annotation = self.annotation_value()?;
        let name = self.name()?;
        Some(Statement::Annotation { name, annotation })
    }
    fn named(&mut self) -> Option<Statement<'a>> {
        let name = self.name()?;
        if name.value == "accDescr" && self.kind() == "STRUCT_START" {
            let opening = self.take()?;
            let start = opening.span.end;
            while !matches!(self.kind(), "EOF" | "STRUCT_STOP") {
                self.at += 1;
            }
            let end = self
                .tokens
                .get(self.at)
                .map_or(self.source.len(), |token| token.span.start);
            if !self.close(&opening) {
                return None;
            }
            return Some(Statement::Accessibility {
                title: false,
                text: &self.source[start..end],
            });
        }
        if matches!(name.value.as_str(), "accTitle" | "accDescr") && self.kind() == "COLON" {
            self.at += 1;
            let text = self.rest();
            return Some(Statement::Accessibility {
                title: name.value == "accTitle",
                text,
            });
        }
        if self.kind() == "COLON" {
            self.at += 1;
            let start = self
                .tokens
                .get(self.at)
                .map_or(self.end(), |t| t.span.start);
            let text = self.member_text()?;
            return Some(Statement::Member {
                name,
                member: Some(MemberStatement {
                    span: Span {
                        start,
                        end: self.end(),
                    },
                    text,
                }),
            });
        }
        if matches!(self.kind(), "NEWLINE" | "EOF" | "STRUCT_STOP") {
            return Some(Statement::Member { name, member: None });
        }
        self.relation(name).map(Statement::Relation)
    }
    fn member_text(&mut self) -> Option<&'a str> {
        let start = self
            .tokens
            .get(self.at)
            .map_or(self.end(), |token| token.span.start);
        while !matches!(self.kind(), "EOF" | "NEWLINE" | "STRUCT_STOP") {
            if matches!(self.kind(), "COLON" | "INVALID") {
                self.unexpected("NEWLINE");
                self.recover();
                return None;
            }
            self.at += 1;
        }
        Some(&self.source[start..self.end().max(start)])
    }
    fn marker(&mut self) -> Option<&'static str> {
        let marker = match self.kind() {
            "EXTENSION" => "extension",
            "AGGREGATION" => "aggregation",
            "COMPOSITION" => "composition",
            "DEPENDENCY" => "dependency",
            "LOLLIPOP" => "lollipop",
            _ => return None,
        };
        self.at += 1;
        Some(marker)
    }
    fn relation(&mut self, from: ClassName<'a>) -> Option<RelationStatement<'a>> {
        let multiplicity_start = if self.kind() == "STR" {
            Some(self.take()?.text)
        } else {
            None
        };
        let marker_start = self.marker();
        let dashed = self.kind() == "DOTTED_LINE";
        if !matches!(self.kind(), "LINE" | "DOTTED_LINE") {
            self.unexpected("DOTTED_LINE, LINE");
            self.recover();
            return None;
        }
        self.at += 1;
        let marker_end = self.marker();
        let multiplicity_end = if self.kind() == "STR" {
            Some(self.take()?.text)
        } else {
            None
        };
        let to = self.name()?;
        let label = if self.kind() == "COLON" {
            self.at += 1;
            Some(self.rest())
        } else {
            None
        };
        Some(RelationStatement {
            span: Span {
                start: from.span.start,
                end: self.end(),
            },
            from,
            to,
            multiplicity_start,
            multiplicity_end,
            marker_start,
            marker_end,
            dashed,
            label,
        })
    }
    fn rest(&mut self) -> &'a str {
        let start = self
            .tokens
            .get(self.at)
            .map_or(self.end(), |t| t.span.start);
        while !matches!(self.kind(), "EOF" | "NEWLINE" | "STRUCT_STOP") {
            self.at += 1;
        }
        &self.source[start..self.end().max(start)]
    }
    fn direction(&mut self) -> Option<Statement<'a>> {
        self.at += 1;
        let token = self.take()?;
        if !matches!(token.text, "TB" | "BT" | "LR" | "RL") {
            self.unexpected("BT, LR, RL, TB");
            return None;
        }
        self.rest();
        Some(Statement::Direction(token.text))
    }
    fn note(&mut self) -> Option<Statement<'a>> {
        let start = self.take()?.span.start;
        let target = if self.tokens.get(self.at).is_some_and(|t| t.text == "for") {
            self.at += 1;
            Some(self.name()?)
        } else {
            None
        };
        let text = self.expect("STR")?.text;
        Some(Statement::Note {
            span: Span {
                start,
                end: self.end(),
            },
            target,
            text,
        })
    }
    fn metadata(&mut self) -> Option<Statement<'a>> {
        let kind = self.take()?.kind;
        let target = self.take()?;
        match kind {
            "CSSCLASS" => Some(Statement::CssClass {
                target: target.text,
                name: self.take()?.text,
            }),
            "STYLE" => Some(Statement::Style {
                target: target.text.into(),
                text: self.rest(),
            }),
            "CLASSDEF" => Some(Statement::ClassDef {
                target: target.text.into(),
                text: self.rest(),
            }),
            _ => {
                let mut values = Vec::new();
                while !matches!(self.kind(), "NEWLINE" | "EOF") {
                    values.push(self.take()?.text);
                }
                Some(Statement::Click {
                    target: target.text.into(),
                    values,
                })
            }
        }
    }
}
