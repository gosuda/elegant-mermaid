use std::borrow::Cow;

use super::{
    ast::*,
    diagnostic,
    lexer::{Token, is_label, lex_cleaned},
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
        openings: Vec::new(),
    };
    let (header, line_end) = p.document_header();
    let mut lines = Vec::new();
    while p.kind() != "EOF" {
        if let Some(line) = p.line() {
            lines.push(line);
        }
    }
    p.diagnostics.sort_by(|a, b| {
        a.span
            .start
            .cmp(&b.span.start)
            .then_with(|| a.code.cmp(b.code))
    });
    Parsed {
        document: Start {
            span: Span {
                start: header.span.start,
                end: source.len(),
            },
            header,
            line_end,
            tokens: p.tokens,
            lines,
        },
        diagnostics: p.diagnostics,
    }
}
pub(super) struct Parser<'a> {
    pub(super) source: &'a str,
    pub(super) cleaned: Cleaned<'a>,
    pub(super) tokens: Vec<Token<'a>>,
    pub(super) at: usize,
    pub(super) diagnostics: Vec<Diagnostic>,
    pub(super) openings: Vec<Token<'a>>,
}
impl<'a> Parser<'a> {
    fn document_header(&mut self) -> (Token<'a>, LineEnd<'a>) {
        while matches!(self.kind(), "NEWLINE" | "COMMENT") {
            self.at += 1;
        }
        let header = self.expect("USECASE").unwrap_or(Token {
            kind: "USECASE",
            text: Cow::Borrowed(""),
            span: Span { start: 0, end: 0 },
        });
        let line_end = self.line_end().unwrap_or(LineEnd {
            span: self.here(),
            token: None,
        });
        (header, line_end)
    }
    pub(super) fn kind(&self) -> &'static str {
        self.peek(0).map_or("EOF", |t| t.kind)
    }
    pub(super) fn peek(&self, n: usize) -> Option<&Token<'a>> {
        self.tokens.get(self.at + n)
    }
    pub(super) fn take(&mut self) -> Option<Token<'a>> {
        let token = self.tokens.get(self.at)?.clone();
        self.at += 1;
        Some(token)
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
    pub(super) fn here(&self) -> Span {
        self.peek(0).map_or(
            Span {
                start: self.source.len(),
                end: self.source.len(),
            },
            |t| t.span,
        )
    }
    pub(super) fn expect(&mut self, kind: &'static str) -> Option<Token<'a>> {
        if self.kind() == kind {
            return self.take();
        }
        self.unexpected(&[kind]);
        None
    }
    pub(super) fn one_of(&mut self, kinds: &[&str]) -> Option<Token<'a>> {
        if kinds.contains(&self.kind()) {
            return self.take();
        }
        self.unexpected(kinds);
        None
    }
    pub(super) fn unexpected(&mut self, kinds: &[&str]) {
        if self.unclosed_at_eof() {
            self.unfinished();
            return;
        }
        if self.kind() == "EOF" && !self.openings.is_empty() {
            self.unfinished();
            return;
        }
        let mut expected = kinds.to_vec();
        expected.sort_unstable();
        expected.dedup();
        let span = self.here();
        let text = self.cleaned.slice(span);
        self.diagnostics.push(diagnostic(
            "usecase/unexpected-token",
            format!(
                "unexpected {text}, expected one of: {}",
                expected.join(", ")
            ),
            span,
        ));
    }
    fn unfinished(&mut self) {
        let Some(opening) = self.unfinished_opening() else {
            return;
        };
        if self
            .diagnostics
            .last()
            .is_some_and(|d| d.code == "usecase/unterminated")
        {
            return;
        }
        let text = match opening.kind {
            "LPAREN" => "(",
            "LBRACKET" => "[",
            "METADATA_START" => "@{",
            "STEREOTYPE_START" => "<<",
            "SYSTEM_BOUNDARY" => "systemBoundary",
            _ => opening.text.as_ref(),
        };
        let span = Span {
            start: opening.span.start,
            end: self.source.len(),
        };
        self.diagnostics.push(diagnostic(
            "usecase/unterminated",
            format!("unterminated {text}"),
            span,
        ));
        self.at = self.tokens.len();
    }
    fn unfinished_opening(&self) -> Option<Token<'a>> {
        let token = self
            .peek(0)
            .filter(|t| t.kind.starts_with("UNCLOSED_"))
            .cloned();
        match token {
            Some(t) if t.kind != "UNCLOSED_STEREOTYPE_TEXT" => Some(t),
            _ => self
                .openings
                .last()
                .cloned()
                .or_else(|| self.peek(0).cloned()),
        }
    }
    fn unclosed_at_eof(&self) -> bool {
        let Some(token) = self.peek(0) else {
            return false;
        };
        if token.kind == "UNCLOSED_STEREOTYPE_TEXT" && token.text.contains(">>") {
            return false;
        }
        token.kind.starts_with("UNCLOSED_")
            && self.cleaned.index(token.span.end) == self.cleaned.text().len()
    }
    pub(super) fn line_end(&mut self) -> Option<LineEnd<'a>> {
        let span = self.here();
        if self.kind() == "EOF" {
            return Some(LineEnd { span, token: None });
        }
        Some(LineEnd {
            span,
            token: Some(self.expect("NEWLINE")?),
        })
    }
    fn line(&mut self) -> Option<Line<'a>> {
        if let Some(kind) = self.spacing() {
            let span = match &kind {
                LineKind::Blank(b) => b.span,
                LineKind::Comment(c) => c.span,
                LineKind::Statement(s) => s.span,
            };
            return Some(Line { span, kind });
        }
        let before = self.at;
        let errors = self.diagnostics.len();
        let open = self.openings.len();
        let value = self.statement_line();
        if value.is_none() {
            self.recover();
            self.coalesce_unfinished(errors);
        }
        self.openings.truncate(open);
        if self.at == before {
            self.at += 1;
        }
        value
    }
    fn statement_line(&mut self) -> Option<Line<'a>> {
        let start = self.here().start;
        let kind = self.statement()?;
        let span = self.span(start);
        let line_end = self.line_end()?;
        let statement = Statement {
            span,
            kind,
            line_end,
        };
        Some(Line {
            span,
            kind: LineKind::Statement(Box::new(statement)),
        })
    }
    fn coalesce_unfinished(&mut self, errors: usize) {
        if let Some(last) = self.diagnostics.last()
            && last.code == "usecase/unterminated"
            && self.diagnostics.len() > errors + 1
        {
            let last = self.diagnostics.pop();
            self.diagnostics.truncate(errors);
            if let Some(last) = last {
                self.diagnostics.push(last);
            }
        }
    }
    pub(super) fn recover(&mut self) {
        let mut depth = self
            .openings
            .iter()
            .filter(|t| t.kind == "METADATA_START")
            .count();
        while !matches!(self.kind(), "EOF" | "END") {
            if self.kind() == "NEWLINE" && depth == 0 {
                break;
            }
            if self.unclosed_at_eof() {
                self.unfinished();
                return;
            }
            self.recover_delimiter(&mut depth);
            self.at += 1;
        }
        if self.kind() == "EOF" && !self.openings.is_empty() {
            self.unfinished();
        }
    }
    fn recover_delimiter(&mut self, depth: &mut usize) {
        match self.kind() {
            "METADATA_START" | "LBRACE" => *depth += 1,
            "RBRACE" => {
                *depth = (*depth).saturating_sub(1);
                if *depth == 0 {
                    self.close_recovered("METADATA_START");
                }
            }
            "RPAREN" => self.close_recovered("LPAREN"),
            "RBRACKET" => self.close_recovered("LBRACKET"),
            "UNCLOSED_STEREOTYPE_TEXT" => self.close_recovered("STEREOTYPE_START"),
            _ => {}
        }
    }
    fn close_recovered(&mut self, kind: &str) {
        if self.openings.last().is_some_and(|t| t.kind == kind) {
            self.openings.pop();
        }
    }
    pub(super) fn spacing(&mut self) -> Option<LineKind<'a>> {
        match self.kind() {
            "NEWLINE" => {
                let token = self.take()?;
                Some(LineKind::Blank(BlankLine {
                    span: token.span,
                    token,
                }))
            }
            "COMMENT" => {
                let token = self.take()?;
                let span = token.span;
                let line_end = self.line_end()?;
                Some(LineKind::Comment(CommentLine {
                    span,
                    token,
                    line_end,
                }))
            }
            _ => None,
        }
    }
    pub(super) fn base_name(&mut self, delimiters: &[&str]) -> Option<ActorName<'a>> {
        let id = self.one_of(&["IDENTIFIER", "PLAIN_STRING", "MARKDOWN_STRING"])?;
        let mut label = None;
        let mut pair = None;
        if id.kind == "IDENTIFIER" && delimiters.contains(&self.kind()) {
            let open = self.take()?;
            self.openings.push(open.clone());
            label = Some(self.label()?);
            let close = self.expect(if open.kind == "LPAREN" {
                "RPAREN"
            } else {
                "RBRACKET"
            })?;
            self.openings.pop();
            pair = Some((open, close));
        }
        Some(ActorName {
            span: self.span(id.span.start),
            id_content_span: content_span(&id),
            id,
            label,
            delimiters: pair,
        })
    }
    pub(super) fn label(&mut self) -> Option<NodeLabel<'a>> {
        let Some(first) = self.peek(0).cloned() else {
            self.unexpected(&["LABEL_TEXT", "MARKDOWN_STRING", "PLAIN_STRING"]);
            return None;
        };
        let mut tokens = Vec::new();
        if matches!(first.kind, "PLAIN_STRING" | "MARKDOWN_STRING") {
            tokens.push(self.take()?);
        } else {
            while is_label(self.kind()) {
                tokens.push(self.take()?);
            }
        }
        if tokens.is_empty() {
            self.unexpected(&["LABEL_TEXT", "MARKDOWN_STRING", "PLAIN_STRING"]);
            return None;
        }
        Some(node_label(
            &self.cleaned,
            &first,
            tokens,
            self.span(first.span.start),
        ))
    }
    pub(super) fn actor_item(&mut self) -> Option<ActorItem<'a>> {
        let name = self.base_name(&["LPAREN"])?;
        let metadata = if self.kind() == "METADATA_START" {
            Some(self.metadata()?)
        } else {
            None
        };
        let stereotype = self.optional_stereotype()?;
        let classes = self.optional_classes()?;
        Some(ActorItem {
            span: self.span(name.span.start),
            name,
            metadata,
            stereotype,
            classes,
        })
    }
    pub(super) fn entity(&mut self) -> Option<EntityName<'a>> {
        let name = self.base_name(&["LPAREN", "LBRACKET"])?;
        let metadata = if self.kind() == "METADATA_START" {
            let metadata = self.metadata()?;
            Some(UseCaseMetadata {
                span: metadata.span,
                metadata,
            })
        } else {
            None
        };
        let stereotype = self.optional_stereotype()?;
        let classes = self.optional_classes()?;
        Some(EntityName {
            span: self.span(name.span.start),
            id_content_span: name.id_content_span,
            id: name.id,
            label: name.label,
            delimiters: name.delimiters,
            metadata,
            stereotype,
            classes,
        })
    }
    fn optional_stereotype(&mut self) -> Option<Option<Stereotype<'a>>> {
        if self.kind() != "STEREOTYPE_START" {
            return Some(None);
        }
        let open = self.take()?;
        self.openings.push(open.clone());
        let content = self.expect("STEREOTYPE_TEXT")?;
        let raw = content.text.as_ref();
        let start = self.cleaned.index(content.span.start) + raw.len() - raw.trim_start().len();
        let content_span = self.cleaned.span(start, start + raw.trim().len());
        let close = self.expect("STEREOTYPE_END")?;
        self.openings.pop();
        Some(Some(Stereotype {
            span: self.span(open.span.start),
            open,
            content,
            content_span,
            close,
        }))
    }
    pub(super) fn optional_classes(&mut self) -> Option<Option<ClassSuffix<'a>>> {
        if self.kind() != "CLASS_SEPARATOR" {
            return Some(None);
        }
        let separator = self.take()?;
        let classes = self.identifiers()?;
        Some(Some(ClassSuffix {
            span: self.span(separator.span.start),
            separator,
            classes,
        }))
    }
    pub(super) fn identifiers(&mut self) -> Option<Vec<Token<'a>>> {
        let mut ids = vec![self.expect("IDENTIFIER")?];
        while self.kind() == "COMMA" {
            self.at += 1;
            ids.push(self.expect("IDENTIFIER")?);
        }
        Some(ids)
    }
    pub(super) fn metadata(&mut self) -> Option<Metadata<'a>> {
        let open = self.expect("METADATA_START")?;
        self.openings.push(open.clone());
        while self.kind() == "NEWLINE" {
            self.at += 1;
        }
        let mut properties = Vec::new();
        let mut separators = Vec::new();
        while !matches!(self.kind(), "RBRACE" | "EOF") {
            properties.push(self.metadata_property()?);
            if self.kind() == "RBRACE" {
                break;
            }
            separators.push(self.metadata_separator()?);
        }
        let close = self.expect("RBRACE")?;
        self.openings.pop();
        Some(Metadata {
            span: self.span(open.span.start),
            open,
            properties,
            separators,
            close,
        })
    }
    fn metadata_property(&mut self) -> Option<MetadataProperty<'a>> {
        let key = self.one_of(&["IDENTIFIER", "PLAIN_STRING"])?;
        self.expect("COLON")?;
        let value = self.one_of(&["IDENTIFIER", "PLAIN_STRING", "TRUE", "FALSE"])?;
        Some(MetadataProperty {
            span: self.span(key.span.start),
            key_content_span: content_span(&key),
            value_content_span: content_span(&value),
            key,
            value,
        })
    }
    fn metadata_separator(&mut self) -> Option<MetadataSeparator<'a>> {
        let start = self.here().start;
        let mut tokens = Vec::new();
        if self.kind() == "COMMA" {
            tokens.push(self.take()?);
        }
        while self.kind() == "NEWLINE" {
            tokens.push(self.take()?);
        }
        if tokens.first().is_some_and(|t| t.kind == "NEWLINE") && self.kind() == "COMMA" {
            tokens.push(self.take()?);
        }
        while self.kind() == "NEWLINE" {
            tokens.push(self.take()?);
        }
        if tokens.is_empty() {
            self.unexpected(&["COMMA", "NEWLINE", "RBRACE"]);
            return None;
        }
        Some(MetadataSeparator {
            span: self.span(start),
            tokens,
        })
    }
}
pub(super) fn content_span(token: &Token<'_>) -> Span {
    let n = match token.kind {
        "PLAIN_STRING" => 1,
        "MARKDOWN_STRING" => 2,
        _ => 0,
    };
    Span {
        start: token.span.start + n,
        end: token.span.end.saturating_sub(n),
    }
}

fn node_label<'a>(
    cleaned: &Cleaned<'a>,
    first: &Token<'a>,
    tokens: Vec<Token<'a>>,
    span: Span,
) -> NodeLabel<'a> {
    let content = if tokens.len() == 1 {
        content_span(first)
    } else {
        span
    };
    let kind = match first.kind {
        "MARKDOWN_STRING" => LabelKind::Markdown,
        "PLAIN_STRING" => LabelKind::Quoted,
        _ => LabelKind::Plain,
    };
    NodeLabel {
        span,
        text: cleaned.slice(content),
        content_span: content,
        kind,
        tokens,
    }
}
