//! Recursive-descent parser for the journey grammar (`spec/grammar/journey.md`).

use crate::diag::Diagnostic;
use crate::source::Span;

use super::ast::{
    AccDescr, AccDescrMultiline, AccTitle, Document, Line, Section, Start, Statement,
    StatementKind, Task, Title,
};
use super::lexer::{
    ACC_DESCR, ACC_TITLE, CLOSE, EOF, JOURNEY, MULTILINE, NEWLINE, OPEN, SECTION, TASK_DATA,
    TASK_NAME, TITLE, Token, UNTERMINATED, lex,
};
use super::{C_UNEXPECTED, C_UNKNOWN, C_UNTERMINATED, diagnostic};

pub struct Parsed {
    pub document: Start,
    pub diagnostics: Vec<Diagnostic>,
}

enum Outcome {
    Unknown,
    Rejected,
    Parsed(StatementKind, usize),
}

pub fn parse(source: &str, removed: &[Span]) -> Parsed {
    let mut parser = Parser {
        source,
        tokens: lex(source, removed),
        at: 0,
        diagnostics: Vec::new(),
    };
    parser.skip_newlines();
    let header = parser.header();
    let end = header.span.end;
    let mut document = Document {
        span: Span { start: end, end },
        lines: Vec::new(),
    };
    parser.document(&mut document);
    let span = Span {
        start: header.span.start,
        end: end.max(document.span.end),
    };
    Parsed {
        document: Start {
            span,
            header,
            document,
        },
        diagnostics: parser.diagnostics,
    }
}

struct Parser<'a> {
    source: &'a str,
    tokens: Vec<Token>,
    at: usize,
    diagnostics: Vec<Diagnostic>,
}

fn describe(token: &Token) -> &str {
    match token.kind {
        EOF => "end of input",
        NEWLINE => "end of line",
        _ => &token.text,
    }
}

impl Parser<'_> {
    fn kind(&self) -> &'static str {
        self.tokens.get(self.at).map_or(EOF, |token| token.kind)
    }

    fn start(&self) -> usize {
        self.tokens
            .get(self.at)
            .map_or(self.source.len(), |token| token.span.start)
    }

    fn current(&self) -> Token {
        self.tokens.get(self.at).cloned().unwrap_or_else(|| Token {
            kind: EOF,
            text: String::new(),
            span: Span {
                start: self.source.len(),
                end: self.source.len(),
            },
            value: super::ast::Value {
                text: String::new(),
                span: Span {
                    start: self.source.len(),
                    end: self.source.len(),
                },
            },
            fields: Vec::new(),
            end: self.source.len(),
        })
    }

    fn take(&mut self) -> Token {
        let token = self.current();
        if self.at < self.tokens.len() {
            self.at += 1;
        }
        token
    }

    fn skip_newlines(&mut self) {
        while self.kind() == NEWLINE {
            self.at += 1;
        }
    }

    fn issue(&mut self, code: &'static str, message: String, span: Span) {
        self.diagnostics.push(diagnostic(code, message, span));
    }

    fn unexpected(&mut self, expected: &str) {
        let token = self.current();
        let message = format!(
            "unexpected {}, expected one of: {expected}",
            describe(&token)
        );
        self.issue(C_UNEXPECTED, message, token.span);
        self.recover(token.end);
    }

    fn recover(&mut self, line_end: usize) {
        while self.kind() != EOF && self.kind() != NEWLINE && self.start() < line_end {
            self.take();
        }
    }

    fn header(&mut self) -> Token {
        if self.kind() == JOURNEY {
            return self.take();
        }
        self.unexpected(JOURNEY);
        let at = self.start();
        let mut token = self.current();
        token.kind = "";
        token.text = String::new();
        token.span = Span { start: at, end: at };
        token
    }

    fn document(&mut self, document: &mut Document) {
        while self.kind() != EOF {
            if let Some(line) = self.line() {
                document.lines.push(line);
            }
        }
        if let (Some(first), Some(last)) = (document.lines.first(), document.lines.last()) {
            document.span = Span {
                start: first.span.start,
                end: last.span.end,
            };
        }
    }

    fn line(&mut self) -> Option<Line> {
        let first = self.current();
        if first.kind == NEWLINE {
            self.take();
            return Some(Line {
                span: first.span,
                statement: None,
            });
        }
        match self.statement(&first) {
            Outcome::Unknown => {
                let span = Span {
                    start: first.span.start,
                    end: first.end.max(first.span.end),
                };
                self.issue(C_UNKNOWN, format!("unknown statement {}", first.text), span);
                self.take();
                self.recover(first.end);
                None
            }
            Outcome::Rejected => None,
            Outcome::Parsed(kind, last) => {
                let span = Span {
                    start: first.span.start,
                    end: last,
                };
                Some(Line {
                    span,
                    statement: Some(Statement { span, kind }),
                })
            }
        }
    }

    fn statement(&mut self, first: &Token) -> Outcome {
        match first.kind {
            TITLE => {
                self.take();
                let text = first.value.clone();
                Outcome::Parsed(StatementKind::Title(Title { text }), first.span.end)
            }
            SECTION => {
                self.take();
                let text = first.value.clone();
                Outcome::Parsed(StatementKind::Section(Section { text }), first.span.end)
            }
            ACC_TITLE => {
                self.take();
                let value = self.take();
                let node = AccTitle {
                    keyword: first.span,
                    value: value.value,
                };
                Outcome::Parsed(StatementKind::AccTitle(node), value.span.end)
            }
            ACC_DESCR => {
                self.take();
                let value = self.take();
                let node = AccDescr {
                    keyword: first.span,
                    value: value.value,
                };
                Outcome::Parsed(StatementKind::AccDescr(node), value.span.end)
            }
            OPEN => self.multiline(),
            TASK_NAME => self.task(),
            _ => Outcome::Unknown,
        }
    }

    fn multiline(&mut self) -> Outcome {
        let open = self.take();
        let mut end = open.span.end;
        let mut value = None;
        if self.kind() == MULTILINE {
            let token = self.take();
            end = token.span.end;
            value = Some(token.value);
        }
        let mut close = None;
        match self.kind() {
            CLOSE => {
                let token = self.take();
                end = token.span.end;
                close = Some(token.span);
            }
            UNTERMINATED => {
                let token = self.take();
                end = token.span.end;
                self.issue(
                    C_UNTERMINATED,
                    format!("unterminated {}", token.text),
                    token.span,
                );
            }
            _ => {}
        }
        match value {
            Some(value) => Outcome::Parsed(
                StatementKind::AccDescrMultiline(AccDescrMultiline {
                    open: open.span,
                    close,
                    value,
                }),
                end,
            ),
            None => Outcome::Rejected,
        }
    }

    fn task(&mut self) -> Outcome {
        let name = self.take();
        if self.kind() != TASK_DATA {
            self.unexpected(TASK_DATA);
            return Outcome::Rejected;
        }
        let data = self.take();
        let end = data.span.end;
        Outcome::Parsed(
            StatementKind::Task(Task {
                name: name.value,
                data: data.value,
                fields: data.fields,
            }),
            end,
        )
    }
}
