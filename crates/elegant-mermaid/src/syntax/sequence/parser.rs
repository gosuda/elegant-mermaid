//! Recursive-descent parser for the sequence grammar (`spec/grammar/sequence.md`).

use std::borrow::Cow;

use crate::diag::Diagnostic;
use crate::source::{Span, cleaned::Cleaned};

use super::ast::*;
use super::lexer::{Token, lex_cleaned};
use super::{C_NESTING, C_UNEXPECTED, C_UNKNOWN, C_UNTERMINATED, diagnostic};

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
    let header = parser.expect("SD").unwrap_or(Token {
        kind: "SD",
        text: Cow::Borrowed(""),
        span: Span { start: 0, end: 0 },
    });
    let document = parser.document(0, &[]);
    if parser.kind() == "UNTERMINATED" {
        let token = parser.take();
        parser.unterminated(&token.text, token.span.start);
    }
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Linked {
    Links,
    Link,
    Properties,
    Details,
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
    fn raw(&self, span: Span) -> Cow<'a, str> {
        self.cleaned.slice(span)
    }
    fn tail(&self, token: &Token<'a>, from: usize) -> Cow<'a, str> {
        let base = self.cleaned.index(token.span.start);
        self.cleaned
            .cow(base + from, base + token.text.len().max(from))
    }
    fn content_end(&self) -> usize {
        self.tokens
            .get(..self.at)
            .unwrap_or_default()
            .iter()
            .rev()
            .find(|token| token.kind != "NEWLINE")
            .map_or(0, |token| token.span.end)
    }
    fn unexpected(&mut self, expected: &[&str]) {
        let token = self.token();
        let mut names: Vec<&str> = expected.to_vec();
        names.sort_unstable();
        let list = names.join(", ");
        let message = format!(
            "unexpected {}, expected one of: {list}",
            self.raw(token.span)
        );
        self.diagnostics
            .push(diagnostic(C_UNEXPECTED, message, token.span));
    }
    fn unterminated(&mut self, opener: &str, start: usize) {
        if self
            .diagnostics
            .last()
            .is_some_and(|d| d.code == C_UNTERMINATED || d.code == C_NESTING)
        {
            return;
        }
        let message = format!("unterminated {opener}");
        self.diagnostics.push(diagnostic(
            C_UNTERMINATED,
            message,
            Span {
                start,
                end: self.source.len(),
            },
        ));
    }
    fn unknown_statement(&mut self) {
        let first = self.token();
        let end = self.line_end().max(first.span.start);
        let span = Span {
            start: first.span.start,
            end,
        };
        let message = format!("unknown statement {}", first.text);
        self.diagnostics.push(diagnostic(C_UNKNOWN, message, span));
        self.skip_line();
    }
    /// Source offset where the physical line of the current token ends, before its
    /// terminator.
    fn line_end(&self) -> usize {
        self.tokens
            .get(self.at..)
            .unwrap_or_default()
            .iter()
            .find(|token| matches!(token.kind, "NEWLINE" | "EOF" | "UNTERMINATED"))
            .map_or(self.source.len(), |token| token.span.start)
    }
    /// Skips to the end of the physical line and consumes its newline.
    fn skip_line(&mut self) {
        loop {
            match self.kind() {
                "EOF" | "UNTERMINATED" => return,
                "NEWLINE" => {
                    self.take();
                    return;
                }
                _ => {
                    self.take();
                }
            }
        }
    }
    fn expect(&mut self, kind: &'static str) -> Option<Token<'a>> {
        if self.kind() == kind {
            return Some(self.take());
        }
        self.unexpected(&[kind]);
        None
    }
    fn finish_line(&mut self, expected: &[&str]) {
        match self.kind() {
            "NEWLINE" => {
                self.take();
            }
            "EOF" | "UNTERMINATED" => {}
            _ => {
                self.unexpected(expected);
                self.skip_line();
            }
        }
    }
    fn document(&mut self, depth: usize, stops: &[&'static str]) -> Document<'a> {
        if depth > 64 {
            let token = self.token();
            self.diagnostics.push(diagnostic(
                C_NESTING,
                String::from("nesting depth exceeds 64"),
                token.span,
            ));
            self.skip_depth(stops);
            let at = token.span.start;
            return Document {
                span: Span { start: at, end: at },
                lines: Vec::new(),
            };
        }
        let start = self.token().span.start;
        let mut lines = Vec::new();
        loop {
            let kind = self.kind();
            if kind == "EOF" || kind == "UNTERMINATED" || stops.contains(&kind) {
                break;
            }
            if kind == "NEWLINE" || kind == "INVALID" {
                let token = self.take();
                lines.push(Line {
                    span: token.span,
                    statement: None,
                });
                continue;
            }
            let before = self.at;
            if let Some(statement) = self.statement(depth) {
                let span = statement.span;
                lines.push(Line {
                    span,
                    statement: Some(statement),
                });
            } else if self.at == before {
                self.unknown_statement();
            }
        }
        let end = lines.iter().fold(start, |end, line| end.max(line.span.end));
        Document {
            span: Span { start, end },
            lines,
        }
    }
    fn skip_depth(&mut self, stops: &[&'static str]) {
        loop {
            let kind = self.kind();
            if kind == "EOF" || kind == "UNTERMINATED" || stops.contains(&kind) {
                return;
            }
            self.take();
        }
    }
    fn statement(&mut self, depth: usize) -> Option<Statement<'a>> {
        let start = self.token().span.start;
        let kind = self.kind();
        let built = self.statement_kind(kind, depth, start)?;
        Some(Statement {
            span: Span {
                start,
                end: self.content_end().max(start),
            },
            kind: built,
        })
    }
    fn statement_kind(
        &mut self,
        kind: &'static str,
        depth: usize,
        start: usize,
    ) -> Option<StatementKind<'a>> {
        match kind {
            "participant" => self
                .participant_plain(None, None)
                .map(StatementKind::Participant),
            "actor_kw" => self
                .participant_plain(None, Some("actor"))
                .map(StatementKind::Participant),
            "destroy" => self.destroy_plain(None).map(StatementKind::Participant),
            "create" => {
                let keyword = self.take().span;
                self.created(keyword).map(StatementKind::Participant)
            }
            "box" => self.box_block(start).map(StatementKind::Box),
            "loop" | "rect" | "opt" | "break" | "alt" | "par" | "par_over" | "critical" => {
                self.control_block(start, depth).map(StatementKind::Control)
            }
            "autonumber" => Some(self.autonumber()),
            "activate" => self.activate_statement(start),
            "deactivate" => self.deactivate_statement(start),
            "note" => self.note_statement().map(StatementKind::Note),
            "links" | "link" | "properties" | "details" => self.linked_statement(kind),
            "title" => Some(self.diagram_title()),
            "legacy_title" => Some(self.legacy_title()),
            "acc_title" => self.accessibility_title(),
            "acc_descr" => self.accessibility_description(),
            "acc_multiline_value" => self.accessibility_block(start),
            "ACTOR" => self.signal().map(StatementKind::Signal),
            _ => None,
        }
    }
    fn created(&mut self, create: Span) -> Option<ParticipantStatement<'a>> {
        match self.kind() {
            "participant" => self.participant_plain(Some(create), None),
            "actor_kw" => self.participant_plain(Some(create), Some("actor")),
            "destroy" => self.destroy_plain(Some(create)),
            _ => {
                self.unexpected(&["actor_kw", "destroy", "participant"]);
                None
            }
        }
    }
    fn check_quotes(&mut self, actor: &Actor<'a>, alias: Option<&Alias<'a>>) {
        let spans = std::iter::once(actor.span).chain(alias.map(|alias| alias.text.span));
        for span in spans {
            if let Some(warning) = super::quotes::unclosed(self.source, span) {
                self.diagnostics.push(warning);
            }
        }
    }
    fn participant_plain(
        &mut self,
        create: Option<Span>,
        draw: Option<&'static str>,
    ) -> Option<ParticipantStatement<'a>> {
        let keyword = self.take().span;
        let actor = self.plain_actor()?;
        let config = self.config_part().ok()?;
        let alias = self.alias_part();
        self.finish_line(&["NEWLINE"]);
        self.check_quotes(&actor, alias.as_ref());
        Some(ParticipantStatement {
            create,
            keyword,
            draw,
            destroy: false,
            actor,
            alias,
            config,
        })
    }
    fn destroy_plain(&mut self, create: Option<Span>) -> Option<ParticipantStatement<'a>> {
        let keyword = self.take().span;
        let actor = self.plain_actor()?;
        self.finish_line(&["NEWLINE"]);
        Some(ParticipantStatement {
            create,
            keyword,
            draw: None,
            destroy: true,
            actor,
            alias: None,
            config: None,
        })
    }
    fn alias_part(&mut self) -> Option<Alias<'a>> {
        if self.kind() != "AS" {
            return None;
        }
        let token = self.take();
        let text = self.take();
        Some(Alias {
            token,
            text: Text2 {
                span: text.span,
                text: text.text,
            },
        })
    }
    /// `Ok(None)`: no metadata object. `Err`: the object is malformed and its
    /// diagnostic, or the pending unterminated token, is already recorded.
    fn config_part(&mut self) -> Result<Option<ConfigObject<'a>>, ()> {
        if self.kind() != "CONFIG_START" {
            return Ok(None);
        }
        let start = self.take();
        if self.kind() != "CONFIG_CONTENT" {
            self.reject_config("CONFIG_CONTENT");
            return Err(());
        }
        let content = self.take();
        if self.kind() != "CONFIG_END" {
            self.reject_config("CONFIG_END");
            return Err(());
        }
        let close = self.take();
        Ok(Some(ConfigObject {
            span: Span {
                start: start.span.start,
                end: close.span.end,
            },
            content: content.text,
            content_span: content.span,
        }))
    }
    fn reject_config(&mut self, expected: &'static str) {
        if self.kind() == "UNTERMINATED" {
            return;
        }
        self.unexpected(&[expected]);
        self.skip_line();
    }
    fn plain_actor(&mut self) -> Option<Actor<'a>> {
        if self.kind() != "ACTOR" {
            self.unexpected(&["ACTOR"]);
            self.skip_line();
            return None;
        }
        let token = self.take();
        Some(Actor {
            span: token.span,
            text: token.text,
        })
    }
    fn signal(&mut self) -> Option<Signal<'a>> {
        let source = self.plain_actor()?;
        let central_start = self.take_parens();
        if !is_arrow(self.kind()) {
            self.unexpected(&["ARROW", "TXT"]);
            self.skip_line();
            return None;
        }
        let arrow = self.take();
        let suffix = self.suffix_token();
        let central_end = suffix.is_none() && self.take_parens();
        let target = self.plain_actor()?;
        if self.kind() != "TXT" {
            self.unexpected(&["TXT"]);
            self.skip_line();
            return None;
        }
        let text = self.take();
        Some(Signal {
            span: Span {
                start: source.span.start,
                end: text.span.end,
            },
            source,
            central_start,
            arrow,
            suffix,
            central_end,
            target,
            text: Text2 {
                span: text.span,
                text: text.text,
            },
        })
    }
    fn take_parens(&mut self) -> bool {
        if self.kind() != "()" {
            return false;
        }
        self.take();
        true
    }
    fn suffix_token(&mut self) -> Option<Token<'a>> {
        let kind = self.kind();
        if kind != "+" && kind != "-" {
            return None;
        }
        Some(self.take())
    }
    fn autonumber(&mut self) -> StatementKind<'a> {
        let start = self.take().span.start;
        let mut start_value = None;
        let mut step = None;
        let mut off = false;
        let mut off_span = Span { start: 0, end: 0 };
        match self.kind() {
            "NUM" => {
                start_value = Some(self.take());
                if self.kind() == "NUM" {
                    step = Some(self.take());
                }
            }
            "off" => {
                let token = self.take();
                off = true;
                off_span = token.span;
            }
            _ => {}
        }
        self.finish_line(&["NUM", "NEWLINE", "off"]);
        StatementKind::Autonumber {
            span: Span {
                start,
                end: self.content_end(),
            },
            start: start_value,
            step,
            off,
            off_span,
        }
    }
    fn activate_statement(&mut self, start: usize) -> Option<StatementKind<'a>> {
        let keyword = self.take().span;
        let actor = self.plain_actor()?;
        self.finish_line(&["NEWLINE"]);
        Some(StatementKind::Activate {
            span: Span {
                start,
                end: self.content_end(),
            },
            keyword,
            actor,
        })
    }
    fn deactivate_statement(&mut self, start: usize) -> Option<StatementKind<'a>> {
        let keyword = self.take().span;
        let actor = self.plain_actor()?;
        self.finish_line(&["NEWLINE"]);
        Some(StatementKind::Deactivate {
            span: Span {
                start,
                end: self.content_end(),
            },
            keyword,
            actor,
        })
    }
    fn note_statement(&mut self) -> Option<NoteStatement<'a>> {
        let keyword = self.take().span;
        let placement_kind = self.kind();
        if !matches!(placement_kind, "over" | "left_of" | "right_of") {
            self.unexpected(&["left_of", "over", "right_of"]);
            self.skip_line();
            return None;
        }
        let placement = self.take();
        let (over, actors) = if placement_kind == "over" {
            self.note_over()?
        } else {
            (false, vec![self.plain_actor()?])
        };
        if self.kind() != "TXT" {
            self.unexpected(&["TXT"]);
            self.skip_line();
            return None;
        }
        let text = self.take();
        self.finish_line(&["NEWLINE"]);
        Some(NoteStatement {
            span: Span {
                start: keyword.start,
                end: text.span.end,
            },
            placement: placement.span,
            over,
            actors,
            text: Text2 {
                span: text.span,
                text: text.text,
            },
        })
    }
    fn note_over(&mut self) -> Option<(bool, Vec<Actor<'a>>)> {
        let first = self.plain_actor()?;
        let mut actors = vec![first];
        if self.kind() == "," {
            self.take();
            actors.push(self.plain_actor()?);
        }
        Some((true, actors))
    }
    fn linked_statement(&mut self, kind: &'static str) -> Option<StatementKind<'a>> {
        let target = match kind {
            "links" => Linked::Links,
            "link" => Linked::Link,
            "properties" => Linked::Properties,
            _ => Linked::Details,
        };
        let keyword = self.take().span;
        let actor = self.plain_actor()?;
        if self.kind() != "TXT" {
            self.unexpected(&["TXT"]);
            self.skip_line();
            return None;
        }
        let text = self.take();
        self.finish_line(&["NEWLINE"]);
        let span = Span {
            start: keyword.start,
            end: text.span.end,
        };
        Some(match target {
            Linked::Links => StatementKind::Links {
                span,
                keyword,
                actor,
                text: Text2 {
                    span: text.span,
                    text: text.text,
                },
            },
            Linked::Link => StatementKind::Link {
                span,
                keyword,
                actor,
                text: Text2 {
                    span: text.span,
                    text: text.text,
                },
            },
            Linked::Properties => StatementKind::Properties {
                span,
                keyword,
                actor,
                text: Text2 {
                    span: text.span,
                    text: text.text,
                },
            },
            Linked::Details => StatementKind::Details {
                span,
                keyword,
                actor,
                text: Text2 {
                    span: text.span,
                    text: text.text,
                },
            },
        })
    }
    fn diagram_title(&mut self) -> StatementKind<'a> {
        let token = self.take();
        StatementKind::Title {
            span: token.span,
            legacy: false,
            value: self.tail(&token, 6),
        }
    }

    fn legacy_title(&mut self) -> StatementKind<'a> {
        let token = self.take();
        StatementKind::Title {
            span: token.span,
            legacy: true,
            value: self.tail(&token, 7),
        }
    }
    fn accessibility_title(&mut self) -> Option<StatementKind<'a>> {
        self.accessibility_value(true)
    }

    fn accessibility_description(&mut self) -> Option<StatementKind<'a>> {
        self.accessibility_value(false)
    }

    fn accessibility_value(&mut self, title: bool) -> Option<StatementKind<'a>> {
        let keyword = self.take().span;
        if self.kind() != "acc_value" {
            self.unexpected(&["acc_value"]);
            self.skip_line();
            return None;
        }
        let value = self.take();
        Some(StatementKind::Accessibility {
            span: Span {
                start: keyword.start,
                end: value.span.end,
            },
            title,
            value: value.span,
        })
    }
    fn accessibility_block(&mut self, start: usize) -> Option<StatementKind<'a>> {
        let value = self.take();
        Some(StatementKind::Accessibility {
            span: Span {
                start,
                end: value.span.end,
            },
            title: false,
            value: value.span,
        })
    }
    fn box_block(&mut self, start: usize) -> Option<BoxBlock<'a>> {
        let keyword = self.take().span;
        let text = self.take();
        if text.kind != "restOfLine" {
            self.unexpected(&["restOfLine"]);
            return None;
        }
        let section = self.box_section();
        let close = self.take();
        if close.kind != "end" {
            self.unterminated("box", keyword.start);
            self.skip_depth(&[]);
            return None;
        }
        Some(BoxBlock {
            span: Span {
                start,
                end: close.span.end,
            },
            keyword,
            text: Text2 {
                span: text.span,
                text: text.text,
            },
            section,
            close,
        })
    }
    fn box_section(&mut self) -> BoxSection<'a> {
        let start = self.token().span.start;
        let mut lines = Vec::new();
        loop {
            let kind = self.kind();
            if matches!(kind, "EOF" | "UNTERMINATED" | "end") {
                break;
            }
            if kind == "NEWLINE" {
                let token = self.take();
                lines.push(Line {
                    span: token.span,
                    statement: None,
                });
                continue;
            }
            if kind == "INVALID" {
                let token = self.take();
                let message = format!(
                    "unexpected {}, expected one of: NEWLINE, actor_kw, participant",
                    token.text
                );
                self.diagnostics
                    .push(diagnostic(C_UNEXPECTED, message, token.span));
                continue;
            }
            let before = self.at;
            let opened = self.token().span.start;
            let drawn = match kind {
                "participant" => self.participant_plain(None, None),
                "actor_kw" => self.participant_plain(None, Some("actor")),
                "destroy" => self.destroy_plain(None),
                _ => None,
            };
            let Some(participant) = drawn else {
                if self.at == before {
                    self.unknown_statement();
                }
                continue;
            };
            let end = self.content_end().max(opened);
            let span = Span { start: opened, end };
            lines.push(Line {
                span,
                statement: Some(Statement {
                    span,
                    kind: StatementKind::Participant(participant),
                }),
            });
        }
        let end = lines.iter().fold(start, |end, line| end.max(line.span.end));
        BoxSection {
            span: Span { start, end },
            lines,
        }
    }
    fn control_block(&mut self, start: usize, depth: usize) -> Option<ControlBlock<'a>> {
        let keyword = self.take();
        let kind = control_kind(keyword.kind);
        let text = self.take();
        if text.kind != "restOfLine" {
            self.unexpected(&["restOfLine"]);
            return None;
        }
        let separator = separator_for(kind);
        let stops: [&'static str; 2] = [separator.unwrap_or("end"), "end"];
        let stops = &stops[..1 + usize::from(separator.is_some())];
        let mut sections = vec![Section {
            separator: None,
            title: Text2 {
                span: text.span,
                text: text.text.clone(),
            },
            document: self.document(depth + 1, stops),
        }];
        while Some(self.kind()) == separator {
            let token = self.take();
            let head = self.take();
            if head.kind != "restOfLine" {
                self.unexpected(&["restOfLine"]);
                return None;
            }
            sections.push(Section {
                separator: Some(token),
                title: Text2 {
                    span: head.span,
                    text: head.text,
                },
                document: self.document(depth + 1, stops),
            });
        }
        let close = self.take();
        if close.kind != "end" {
            self.unterminated(keyword.kind, keyword.span.start);
            self.skip_depth(stops);
            return None;
        }
        Some(ControlBlock {
            span: Span {
                start,
                end: close.span.end,
            },
            keyword: keyword.span,
            kind,
            text: Text2 {
                span: text.span,
                text: text.text,
            },
            sections,
            close,
        })
    }
}

fn is_arrow(kind: &str) -> bool {
    matches!(
        kind,
        "SOLID_ARROW"
            | "BIDIRECTIONAL_SOLID_ARROW"
            | "DOTTED_ARROW"
            | "BIDIRECTIONAL_DOTTED_ARROW"
            | "SOLID_OPEN_ARROW"
            | "DOTTED_OPEN_ARROW"
            | "SOLID_CROSS"
            | "DOTTED_CROSS"
            | "SOLID_POINT"
            | "DOTTED_POINT"
            | "SOLID_ARROW_TOP"
            | "SOLID_ARROW_BOTTOM"
            | "STICK_ARROW_TOP"
            | "STICK_ARROW_BOTTOM"
            | "SOLID_ARROW_TOP_DOTTED"
            | "SOLID_ARROW_BOTTOM_DOTTED"
            | "STICK_ARROW_TOP_DOTTED"
            | "STICK_ARROW_BOTTOM_DOTTED"
            | "SOLID_ARROW_TOP_REVERSE"
            | "SOLID_ARROW_BOTTOM_REVERSE"
            | "STICK_ARROW_TOP_REVERSE"
            | "STICK_ARROW_BOTTOM_REVERSE"
            | "SOLID_ARROW_TOP_REVERSE_DOTTED"
            | "SOLID_ARROW_BOTTOM_REVERSE_DOTTED"
            | "STICK_ARROW_TOP_REVERSE_DOTTED"
            | "STICK_ARROW_BOTTOM_REVERSE_DOTTED"
    )
}

fn control_kind(kind: &str) -> &'static str {
    match kind {
        "loop" => "loop",
        "rect" => "rect",
        "opt" => "opt",
        "alt" => "alt",
        "par" => "par",
        "par_over" => "par_over",
        "critical" => "critical",
        _ => "break",
    }
}

fn separator_for(kind: &str) -> Option<&'static str> {
    match kind {
        "alt" => Some("else"),
        "par" | "par_over" => Some("and"),
        "critical" => Some("option"),
        _ => None,
    }
}
