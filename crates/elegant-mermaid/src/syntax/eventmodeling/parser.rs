//! Recursive-descent parser for the eventmodeling grammar
//! (`spec/grammar/eventmodeling.md`).
//!
//! Statements are free-form: they are not tied to lines. A failed statement skips to the
//! next statement keyword or to the end of its line, whichever comes first.

use crate::diag::Diagnostic;
use crate::source::Span;

use super::ast::{
    EmDataEntity, EmFrame, EmGwt, EmGwtStatement, EmModelEntity, EmNoteEntity, EventModel,
    FrameFields, Value,
};
use super::lexer::{HEADER, K_BLOCK, K_EOF, K_FID, K_ID, K_INLINE, K_UNCLOSED, Token, lex};
use super::{C_UNEXPECTED, C_UNKNOWN, C_UNTERMINATED, diagnostic};

const ENTITY_TYPES: &[&str] = &[
    "cmd",
    "command",
    "evt",
    "event",
    "pcr",
    "processor",
    "readmodel",
    "rmo",
    "ui",
];
const DATA_TYPES: &[&str] = &[
    "figma", "html", "jsobj", "json", "md", "salt", "text", "uri",
];
const OPENERS: &[&str] = &[
    "tf",
    "timeframe",
    "rf",
    "resetframe",
    "entity",
    "data",
    "note",
    "gwt",
];
const TICK: &str = "`";

pub struct Parsed {
    pub document: EventModel,
    pub diagnostics: Vec<Diagnostic>,
}

pub fn parse(source: &str, removed: &[Span]) -> Parsed {
    let (tokens, breaks) = lex(source, removed);
    let mut parser = Parser {
        source,
        tokens,
        breaks,
        at: 0,
        diagnostics: Vec::new(),
    };
    let header = parser.header();
    let mut document = EventModel {
        span: Span {
            start: header.span.start,
            end: source.len(),
        },
        header,
        model_entities: Vec::new(),
        frames: Vec::new(),
        data_entities: Vec::new(),
        note_entities: Vec::new(),
        gwt_entities: Vec::new(),
    };
    parser.statements(&mut document);
    Parsed {
        document,
        diagnostics: parser.diagnostics,
    }
}

struct Parser<'a> {
    source: &'a str,
    tokens: Vec<Token>,
    breaks: Vec<usize>,
    at: usize,
    diagnostics: Vec<Diagnostic>,
}

fn value_of(token: &Token) -> Value {
    Value {
        text: token.text.clone(),
        span: token.span,
    }
}

impl Parser<'_> {
    fn token(&self) -> Token {
        self.tokens.get(self.at).cloned().unwrap_or(Token {
            kind: K_EOF,
            text: String::new(),
            span: Span {
                start: self.source.len(),
                end: self.source.len(),
            },
        })
    }

    fn kind(&self) -> &'static str {
        self.tokens.get(self.at).map_or(K_EOF, |t| t.kind)
    }

    fn take(&mut self) -> Token {
        let token = self.token();
        if self.at < self.tokens.len() {
            self.at += 1;
        }
        token
    }

    fn last_end(&self) -> usize {
        self.at
            .checked_sub(1)
            .and_then(|i| self.tokens.get(i))
            .map_or(0, |token| token.span.end)
    }

    fn raw(&self, span: Span) -> &str {
        self.source.get(span.start..span.end).unwrap_or("")
    }

    fn issue(&mut self, code: &'static str, message: String, span: Span) {
        self.diagnostics.push(diagnostic(code, message, span));
    }

    fn unexpected(&mut self, expected: &[&str]) {
        let token = self.token();
        if token.kind == K_UNCLOSED {
            return;
        }
        let mut names = expected.to_vec();
        names.sort_unstable();
        let message = format!(
            "unexpected {}, expected one of: {}",
            self.raw(token.span),
            names.join(", ")
        );
        self.issue(C_UNEXPECTED, message, token.span);
    }

    fn unclosed(&mut self, opener: &Token) {
        let message = format!("unterminated {}", opener.text);
        let span = Span {
            start: opener.span.start,
            end: self.source.len(),
        };
        self.issue(C_UNTERMINATED, message, span);
    }

    fn inside_failure(&mut self, opener: &Token, expected: &[&str]) {
        if self.kind() == K_EOF {
            self.unclosed(opener);
        } else {
            self.unexpected(expected);
        }
    }

    fn line_end(&self, from: usize) -> usize {
        let i = self.breaks.partition_point(|&at| at < from);
        self.breaks.get(i).copied().unwrap_or(self.source.len())
    }

    fn recover(&mut self) {
        let limit = self.line_end(self.token().span.start);
        self.recover_to(limit);
    }

    fn recover_to(&mut self, limit: usize) -> usize {
        loop {
            let token = self.token();
            if token.kind == K_EOF || token.kind == K_UNCLOSED || OPENERS.contains(&token.kind) {
                return limit.min(token.span.start);
            }
            if token.span.start >= limit {
                return limit;
            }
            self.take();
        }
    }

    fn header(&mut self) -> Token {
        if self.kind() == HEADER {
            return self.take();
        }
        self.unexpected(&[HEADER]);
        self.recover();
        Token {
            kind: "",
            text: String::new(),
            span: Span { start: 0, end: 0 },
        }
    }

    fn statements(&mut self, document: &mut EventModel) {
        loop {
            match self.kind() {
                K_EOF => return,
                K_UNCLOSED => {
                    let token = self.token();
                    self.unclosed(&token);
                    return;
                }
                "tf" | "timeframe" => {
                    if let Some(fields) = self.frame() {
                        document.frames.push(EmFrame::TimeFrame(fields));
                    }
                }
                "rf" | "resetframe" => {
                    if let Some(fields) = self.frame() {
                        document.frames.push(EmFrame::ResetFrame(fields));
                    }
                }
                "entity" => self.entity(document),
                "data" => self.data(document),
                "note" => self.note(document),
                "gwt" => self.gwt(document),
                _ => self.unknown(),
            }
        }
    }

    fn unknown(&mut self) {
        let first = self.take();
        let limit = self.line_end(first.span.start);
        let boundary = self.recover_to(limit);
        let end = boundary.max(self.last_end());
        let message = format!("unknown statement {}", self.raw(first.span));
        self.issue(
            C_UNKNOWN,
            message,
            Span {
                start: first.span.start,
                end,
            },
        );
    }

    fn value_of(&mut self, kind: &'static str) -> Option<Value> {
        if self.kind() != kind {
            self.unexpected(&[kind]);
            return None;
        }
        Some(value_of(&self.take()))
    }

    fn one_of(&mut self, kinds: &[&str]) -> Option<Value> {
        if !kinds.contains(&self.kind()) {
            self.unexpected(kinds);
            return None;
        }
        Some(value_of(&self.take()))
    }

    fn qualified_name(&mut self) -> Option<Value> {
        let mut name = self.value_of(K_ID)?;
        while self.kind() == "." {
            self.take();
            let part = self.value_of(K_ID)?;
            name = Value {
                text: format!("{}.{}", name.text, part.text),
                span: Span {
                    start: name.span.start,
                    end: part.span.end,
                },
            };
        }
        Some(name)
    }

    fn frame(&mut self) -> Option<FrameFields> {
        let keyword = self.take();
        let fields = self.frame_fields(&keyword);
        if fields.is_none() {
            self.recover();
        }
        fields
    }

    fn frame_fields(&mut self, keyword: &Token) -> Option<FrameFields> {
        let name = self.value_of(K_FID)?;
        let model_entity_type = self.one_of(ENTITY_TYPES)?;
        let entity_identifier = self.qualified_name()?;
        let mut fields = FrameFields {
            span: keyword.span,
            keyword: keyword.span,
            name,
            model_entity_type,
            entity_identifier,
            source_frames: Vec::new(),
            data_reference: None,
            data_type: None,
            data_inline_value: None,
        };
        self.frame_tail(&mut fields)?;
        fields.span = Span {
            start: keyword.span.start,
            end: self.last_end(),
        };
        Some(fields)
    }

    fn frame_tail(&mut self, fields: &mut FrameFields) -> Option<()> {
        while self.kind() == "->>" {
            self.take();
            fields.source_frames.push(self.value_of(K_FID)?);
        }
        if self.kind() == "[[" {
            fields.data_reference = Some(self.reference()?);
        }
        if self.kind() != TICK && self.kind() != K_INLINE {
            return Some(());
        }
        let (data_type, payload) = self.payload(K_INLINE)?;
        fields.data_type = data_type;
        fields.data_inline_value = Some(payload);
        Some(())
    }

    fn reference(&mut self) -> Option<Value> {
        let opener = self.take();
        if self.kind() != K_ID {
            self.inside_failure(&opener, &[K_ID]);
            return None;
        }
        let token = self.take();
        if self.kind() != "]]" {
            self.inside_failure(&opener, &["]]"]);
            return None;
        }
        self.take();
        Some(value_of(&token))
    }

    fn payload(&mut self, kind: &'static str) -> Option<(Option<Value>, Value)> {
        let mut data_type = None;
        if self.kind() == TICK {
            let opener = self.take();
            if !DATA_TYPES.contains(&self.kind()) {
                self.inside_failure(&opener, DATA_TYPES);
                return None;
            }
            data_type = Some(value_of(&self.take()));
            if self.kind() != TICK {
                self.inside_failure(&opener, &[TICK]);
                return None;
            }
            self.take();
        } else if self.kind() != kind {
            self.unexpected(&[TICK, kind]);
            return None;
        }
        let value = self.value_of(kind)?;
        Some((data_type, value))
    }

    fn entity(&mut self, document: &mut EventModel) {
        let keyword = self.take();
        let Some(name) = self.qualified_name() else {
            self.recover();
            return;
        };
        document.model_entities.push(EmModelEntity {
            span: Span {
                start: keyword.span.start,
                end: self.last_end(),
            },
            keyword: keyword.span,
            name,
        });
    }

    fn data(&mut self, document: &mut EventModel) {
        let keyword = self.take();
        let Some(name) = self.value_of(K_ID) else {
            self.recover();
            return;
        };
        let Some((data_type, block)) = self.payload(K_BLOCK) else {
            self.recover();
            return;
        };
        document.data_entities.push(EmDataEntity {
            span: Span {
                start: keyword.span.start,
                end: self.last_end(),
            },
            keyword: keyword.span,
            name,
            data_type,
            data_block_value: block,
        });
    }

    fn note(&mut self, document: &mut EventModel) {
        let keyword = self.take();
        let Some(frame) = self.value_of(K_FID) else {
            self.recover();
            return;
        };
        let Some((data_type, block)) = self.payload(K_BLOCK) else {
            self.recover();
            return;
        };
        document.note_entities.push(EmNoteEntity {
            span: Span {
                start: keyword.span.start,
                end: self.last_end(),
            },
            keyword: keyword.span,
            source_frame: frame,
            data_type,
            data_block_value: block,
        });
    }

    fn gwt(&mut self, document: &mut EventModel) {
        let keyword = self.take();
        let Some(mut node) = self.gwt_head(&keyword) else {
            self.recover();
            return;
        };
        if self.gwt_body(&mut node).is_none() {
            self.recover();
            return;
        }
        node.span = Span {
            start: keyword.span.start,
            end: self.last_end(),
        };
        document.gwt_entities.push(node);
    }

    fn gwt_head(&mut self, keyword: &Token) -> Option<EmGwt> {
        let source_frame = self.value_of(K_FID)?;
        if self.kind() != "given" {
            self.unexpected(&["given"]);
            return None;
        }
        self.take();
        Some(EmGwt {
            span: keyword.span,
            keyword: keyword.span,
            source_frame,
            given_statements: Vec::new(),
            when_statements: Vec::new(),
            then_statements: Vec::new(),
        })
    }

    fn gwt_body(&mut self, node: &mut EmGwt) -> Option<()> {
        node.given_statements = self.gwt_statements()?;
        if self.kind() == "when" {
            self.take();
            node.when_statements = self.gwt_statements()?;
        }
        if self.kind() != "then" {
            let mut next = ENTITY_TYPES.to_vec();
            next.push("then");
            if node.when_statements.is_empty() {
                next.push("when");
            }
            self.unexpected(&next);
            return None;
        }
        self.take();
        node.then_statements = self.gwt_statements()?;
        Some(())
    }

    fn gwt_statements(&mut self) -> Option<Vec<EmGwtStatement>> {
        let mut statements = Vec::new();
        while statements.is_empty() || ENTITY_TYPES.contains(&self.kind()) {
            let kind = self.one_of(ENTITY_TYPES)?;
            let identifier = self.value_of(K_ID)?;
            statements.push(EmGwtStatement {
                span: Span {
                    start: kind.span.start,
                    end: identifier.span.end,
                },
                model_entity_type: kind,
                entity_identifier: identifier,
            });
        }
        Some(statements)
    }
}
