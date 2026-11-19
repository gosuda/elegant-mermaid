use super::{
    ast::*,
    diagnostic,
    lexer::{Token, lex, lex_cleaned},
};
use crate::{
    diag::Diagnostic,
    source::{Span, cleaned::Cleaned},
};
use std::borrow::Cow;

pub struct Parsed<'a> {
    pub document: Start<'a>,
    pub diagnostics: Vec<Diagnostic>,
}
pub fn parse<'a>(source: &'a str, removed: &[Span]) -> Parsed<'a> {
    let cleaned = Cleaned::new(source, removed);
    let mut p = Parser {
        source,
        removed,
        tokens: lex_cleaned(&cleaned),
        cleaned,
        at: 0,
        diagnostics: Vec::new(),
    };
    while matches!(p.kind(), "SPACE" | "NEWLINE" | "COMMENT") {
        p.at += 1;
    }
    let header = p.require("GRAPH").unwrap_or(Token {
        kind: "GRAPH",
        text: Cow::Borrowed(""),
        span: Span { start: 0, end: 0 },
    });
    let config = p.graph_config(&header);
    let document = p.document(0);
    Parsed {
        document: Start {
            span: Span {
                start: header.span.start,
                end: source.len(),
            },
            header,
            config,
            document,
        },
        diagnostics: p.diagnostics,
    }
}
pub(super) struct Parser<'a, 'r> {
    pub(super) source: &'a str,
    pub(super) cleaned: Cleaned<'a>,
    removed: &'r [Span],
    pub(super) tokens: Vec<Token<'a>>,
    pub(super) at: usize,
    diagnostics: Vec<Diagnostic>,
}
impl<'a> Parser<'a, '_> {
    pub(super) fn kind(&self) -> &'static str {
        self.tokens.get(self.at).map_or("EOF", |t| t.kind)
    }
    pub(super) fn take(&mut self) -> Option<Token<'a>> {
        let t = self.tokens.get(self.at)?.clone();
        self.at += 1;
        Some(t)
    }
    pub(super) fn position(&self) -> usize {
        self.tokens
            .get(self.at)
            .map_or(self.source.len(), |t| t.span.start)
    }
    fn end(&self) -> usize {
        self.tokens
            .get(self.at.saturating_sub(1))
            .map_or(0, |t| t.span.end)
    }
    pub(super) fn span(&self, start: usize) -> Span {
        Span {
            start,
            end: self.end(),
        }
    }
    pub(super) fn spaces(&mut self) -> usize {
        let start = self.at;
        while self.kind() == "SPACE" {
            self.at += 1;
        }
        self.at - start
    }
    pub(super) fn require(&mut self, kind: &'static str) -> Option<Token<'a>> {
        if self.kind() == kind {
            return self.take();
        }
        self.unexpected(kind);
        None
    }
    pub(super) fn unexpected(&mut self, accepted: &str) {
        if self.kind() == "UNTERMINATED" {
            if let Some(t) = self.take() {
                self.unterminated(t.span);
            }
            return;
        }
        let span = self.tokens.get(self.at).map_or(
            Span {
                start: self.source.len(),
                end: self.source.len(),
            },
            |t| t.span,
        );
        let text = self.cleaned.slice(span);
        self.diagnostics.push(diagnostic(
            "agentflow/unexpected-token",
            format!("unexpected {text}, expected one of: {accepted}"),
            span,
        ));
    }
    pub(super) fn unterminated(&mut self, opening: Span) {
        let token = self.cleaned.slice(opening);
        self.diagnostics.push(diagnostic(
            "agentflow/unterminated",
            format!("unterminated {token}"),
            Span {
                start: opening.start,
                end: self.source.len(),
            },
        ));
    }
    fn graph_config(&mut self, header: &Token<'a>) -> GraphConfig<'a> {
        let authored = if self.kind() == "DIR" {
            self.take()
        } else {
            None
        };
        let direction = Direction {
            span: authored.as_ref().map_or(header.span, |t| t.span),
            value: authored
                .as_ref()
                .map_or("TB", |t| normalized(t.text.trim())),
        };
        let separator = if self.kind() == "NODIR" {
            self.take().map(|t| FirstStmtSeparator {
                span: t.span,
                tokens: vec![t],
            })
        } else {
            self.first_separator()
        };
        GraphConfig {
            span: self.span(header.span.start),
            direction,
            authored,
            separator,
        }
    }
    fn first_separator(&mut self) -> Option<FirstStmtSeparator<'a>> {
        let start = self.position();
        let mut tokens = Vec::new();
        while self.kind() == "SPACE" {
            tokens.push(self.take()?);
        }
        if !matches!(self.kind(), "NEWLINE" | "SEMI" | "COMMENT") {
            self.unexpected("COMMENT, NEWLINE, SEMI");
            return None;
        }
        tokens.push(self.take()?);
        Some(FirstStmtSeparator {
            span: self.span(start),
            tokens,
        })
    }
    fn document(&mut self, depth: usize) -> Document<'a> {
        let start = self.position();
        let mut lines = Vec::new();
        while self.kind() != "EOF" {
            if self.kind() == "end" && depth > 0 {
                break;
            }
            if matches!(self.kind(), "SPACE" | "NEWLINE" | "SEMI" | "COMMENT") {
                if let Some(t) = self.take() {
                    lines.push(Line {
                        span: t.span,
                        statement: None,
                    });
                }
                continue;
            }
            self.document_statement(depth, &mut lines);
        }
        Document {
            span: Span {
                start,
                end: lines.last().map_or(start, |l| l.span.end),
            },
            lines,
        }
    }
    fn document_statement(&mut self, depth: usize, lines: &mut Vec<Line<'a>>) {
        let before = self.at;
        let start = self.position();
        let statement = self.statement(depth);
        if statement.is_none() {
            self.recover();
            self.resynchronize_line(start);
        } else if let Some(s) = statement {
            lines.push(Line {
                span: s.span,
                statement: Some(s),
            });
        }
        if self.at == before {
            self.at += 1;
        }
    }
    fn recover(&mut self) {
        while !matches!(self.kind(), "EOF" | "NEWLINE" | "SEMI" | "COMMENT" | "end") {
            self.at += 1;
        }
    }
    fn resynchronize_line(&mut self, start: usize) {
        if self.kind() != "EOF" {
            return;
        }
        let Some(d) = self.diagnostics.last_mut() else {
            return;
        };
        if !matches!(
            d.code,
            "agentflow/unexpected-token" | "agentflow/unknown-statement"
        ) {
            return;
        }
        let Some(tail) = self.source.get(start..) else {
            return;
        };
        let Some(offset) = tail.find(['\r', '\n']) else {
            return;
        };
        let end = start + offset;
        if d.span.start >= end || tail.starts_with('"') {
            return;
        }
        d.span.end = d.span.end.min(end);
        let mut removed = self.removed.to_vec();
        removed.push(Span { start: 0, end });
        self.tokens = lex(self.source, &removed);
        self.at = 0;
    }
    fn statement(&mut self, depth: usize) -> Option<Statement<'a>> {
        let start = self.position();
        let kind = match self.kind() {
            "flow" | "global" | "connector" => self.container(depth)?,
            "STYLE" | "CLASSDEF" | "CLASS" => self.style_statement()?,
            "LINKSTYLE" => StatementKind::LinkStyle(self.link_style()?),
            "CLICK" => StatementKind::Click(self.click()?),
            "direction_tb" | "direction_bt" | "direction_rl" | "direction_lr" | "direction_td" => {
                let t = self.take()?;
                return Some(Statement {
                    span: t.span,
                    kind: StatementKind::Direction(Direction {
                        span: t.span,
                        value: direction_kind(t.kind),
                    }),
                });
            }
            "acc_title" | "acc_descr" | "acc_descr_multiline_value" => return self.accessibility(),
            k if id_kind(k) => StatementKind::Vertex(self.vertex_statement()?),
            _ => return self.unknown(),
        };
        if matches!(
            kind,
            StatementKind::Flow { .. } | StatementKind::Global { .. }
        ) {
            return Some(Statement {
                span: self.span(start),
                kind,
            });
        }
        self.spaces();
        if !boundary(self.kind()) {
            self.unexpected("COMMENT, EOF, NEWLINE, SEMI");
            return None;
        }
        Some(Statement {
            span: self.span(start),
            kind,
        })
    }
    fn unknown(&mut self) -> Option<Statement<'a>> {
        if self.kind() == "UNTERMINATED" {
            self.unexpected("");
            return None;
        }
        let t = self.take()?;
        self.recover();
        self.diagnostics.push(diagnostic(
            "agentflow/unknown-statement",
            format!("unknown statement {}", t.text),
            Span {
                start: t.span.start,
                end: self.end(),
            },
        ));
        None
    }
    fn accessibility(&mut self) -> Option<Statement<'a>> {
        let t = self.take()?;
        let title = t.kind == "acc_title";
        let value = match t.kind {
            "acc_title" => self.require("acc_title_value")?,
            "acc_descr" => self.require("acc_descr_value")?,
            _ => t.clone(),
        };
        Some(Statement {
            span: self.span(t.span.start),
            kind: StatementKind::Accessibility { title, value },
        })
    }
    fn container(&mut self, depth: usize) -> Option<StatementKind<'a>> {
        let open = self.take()?;
        if open.kind == "global" {
            return self.global(open, depth);
        }
        let name = self.container_name();
        if open.kind == "connector" && name.is_none() {
            self.unexpected("MD_STR, NODE_STRING, STR");
            return None;
        }
        let title = if self.kind() == "SQS" {
            Some(self.bracket_text()?.0)
        } else {
            None
        };
        let metadata = self.metadata()?;
        self.spaces();
        if !boundary(self.kind()) {
            self.unexpected("COMMENT, EOF, NEWLINE, SEMI");
            return None;
        }
        if open.kind == "connector" {
            return Some(StatementKind::Connector {
                name: name?,
                title,
                metadata,
            });
        }
        let (body, close) = self.block(&open, depth)?;
        Some(StatementKind::Flow {
            name,
            title,
            metadata,
            opening: open.span,
            body,
            close,
        })
    }
    fn container_name(&mut self) -> Option<TextNoTags<'a>> {
        if self.spaces() == 0 {
            return None;
        }
        let start = self.position();
        let mut pieces = Vec::new();
        while no_tags_kind(self.kind()) {
            pieces.push(self.take()?);
        }
        while pieces.last().is_some_and(|t| t.kind == "SPACE") {
            pieces.pop();
        }
        let first = pieces.first()?;
        let kind = text_kind(first.kind);
        let end = pieces.last().map_or(start, |t| t.span.end);
        Some(TextNoTags {
            span: Span { start, end },
            pieces,
            kind,
        })
    }
    fn global(&mut self, open: Token<'a>, depth: usize) -> Option<StatementKind<'a>> {
        self.spaces();
        if !boundary(self.kind()) {
            self.unexpected("COMMENT, EOF, NEWLINE, SEMI");
            return None;
        }
        let (body, close) = self.block(&open, depth)?;
        Some(StatementKind::Global {
            opening: open.span,
            body,
            close,
        })
    }
    fn block(&mut self, open: &Token<'a>, depth: usize) -> Option<(Document<'a>, Span)> {
        if depth >= 64 {
            self.diagnostics.push(diagnostic(
                "limit/nesting-depth",
                "nesting depth exceeds 64".into(),
                open.span,
            ));
            self.at = self.tokens.len();
            return None;
        }
        if self.kind() != "EOF" {
            self.at += 1;
        }
        let body = self.document(depth + 1);
        if self.kind() != "end" {
            if !self
                .diagnostics
                .last()
                .is_some_and(|d| matches!(d.code, "limit/nesting-depth" | "agentflow/unterminated"))
            {
                self.unterminated(open.span);
            }
            return None;
        }
        Some((body, self.take()?.span))
    }
}
pub(super) fn boundary(kind: &str) -> bool {
    matches!(kind, "NEWLINE" | "SEMI" | "COMMENT" | "EOF")
}
pub(super) fn id_kind(kind: &str) -> bool {
    matches!(
        kind,
        "NUM"
            | "NODE_STRING"
            | "DOWN"
            | "MINUS"
            | "DEFAULT"
            | "COMMA"
            | "COLON"
            | "AMP"
            | "BRKT"
            | "MULT"
            | "UNICODE_TEXT"
    )
}
pub(super) fn alpha_kind(kind: &str) -> bool {
    id_kind(kind) && kind != "DEFAULT" || kind == "DIR"
}
fn no_tags_kind(kind: &str) -> bool {
    matches!(
        kind,
        "NUM"
            | "NODE_STRING"
            | "SPACE"
            | "MINUS"
            | "AMP"
            | "UNICODE_TEXT"
            | "COLON"
            | "MULT"
            | "BRKT"
            | "STYLE"
            | "LINKSTYLE"
            | "CLASSDEF"
            | "CLASS"
            | "CLICK"
            | "GRAPH"
            | "DIR"
            | "flow"
            | "connector"
            | "global"
            | "end"
            | "DOWN"
            | "UP"
            | "START_LINK"
            | "STR"
            | "MD_STR"
    )
}
pub(super) fn text_kind(kind: &str) -> TextKind {
    match kind {
        "STR" => TextKind::String,
        "MD_STR" => TextKind::Markdown,
        _ => TextKind::Plain,
    }
}
fn normalized(value: &str) -> &'static str {
    match value {
        "LR" | ">" => "LR",
        "RL" | "<" => "RL",
        "BT" | "^" => "BT",
        _ => "TB",
    }
}
fn direction_kind(kind: &str) -> &'static str {
    match kind {
        "direction_bt" => "BT",
        "direction_rl" => "RL",
        "direction_lr" => "LR",
        _ => "TB",
    }
}
