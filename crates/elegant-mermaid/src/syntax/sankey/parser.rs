use super::ast::{Csv, Escaped, Field, NonEscaped, OptEof, Record, Start};
use super::lexer::{self, Token};
use super::{C_UNEXPECTED, C_UNKNOWN, C_UNTERMINATED, diagnostic};
use crate::diag::Diagnostic;
use crate::source::Span;

pub fn parse(source: &str, removed: &[Span]) -> (Start, Vec<Diagnostic>) {
    let mut tokens = lexer::lex(source, removed);
    if tokens
        .last()
        .is_some_and(|token| token.kind == "UNTERMINATED")
    {
        tokens.push(Token {
            kind: "EOF",
            text: String::new(),
            span: Span {
                start: source.len(),
                end: source.len(),
            },
        });
    }
    let mut parser = Parser {
        source,
        tokens,
        at: 0,
        diagnostics: Vec::new(),
    };
    let start = parser.start();
    (start, parser.diagnostics)
}

struct Parser<'a> {
    source: &'a str,
    tokens: Vec<Token>,
    at: usize,
    diagnostics: Vec<Diagnostic>,
}

impl Parser<'_> {
    fn token(&self) -> &Token {
        &self.tokens[self.at.min(self.tokens.len() - 1)]
    }
    fn kind(&self) -> &'static str {
        self.token().kind
    }
    fn take(&mut self) -> Token {
        let token = self.token().clone();
        if self.at + 1 < self.tokens.len() {
            self.at += 1;
        }
        token
    }
    fn boundary(&self) -> bool {
        matches!(self.kind(), "NEWLINE" | "EOF" | "UNTERMINATED")
    }
    fn recover(&mut self) {
        while !self.boundary() {
            self.take();
        }
    }
    fn unterminated(&mut self) {
        let token = self.take();
        self.diagnostics.push(diagnostic(
            C_UNTERMINATED,
            format!("unterminated {}", token.text),
            token.span,
        ));
    }
    fn unexpected(&mut self, expected: &[&str]) {
        if self.kind() == "UNTERMINATED" {
            self.unterminated();
            return;
        }
        let token = self.token();
        let span = token.span;
        let text = &self.source[span.start..span.end];
        let mut names = expected.to_vec();
        names.sort_unstable();
        self.diagnostics.push(diagnostic(
            C_UNEXPECTED,
            format!("unexpected {text}, expected one of: {}", names.join(", ")),
            span,
        ));
        self.recover();
    }
    fn unknown(&mut self) {
        let first = self.take();
        let mut end = first.span.end;
        while !self.boundary() {
            end = self.take().span.end;
        }
        self.diagnostics.push(diagnostic(
            C_UNKNOWN,
            format!("unknown statement {}", first.text),
            Span {
                start: first.span.start,
                end,
            },
        ));
    }
    fn header(&mut self) -> (Option<Token>, bool) {
        if self.kind() != "SANKEY" {
            self.unexpected(&["SANKEY"]);
            return (None, false);
        }
        let header = self.take();
        if self.kind() == "NEWLINE" {
            self.take();
            return (Some(header), true);
        }
        self.unexpected(&["NEWLINE"]);
        if self.kind() == "NEWLINE" {
            self.take();
        }
        (Some(header), false)
    }
    fn start(&mut self) -> Start {
        let first = self.token().span.start;
        let (header, ok) = self.header();
        let csv = if ok || self.kind() != "EOF" {
            self.csv()
        } else {
            Csv {
                span: Span { start: 0, end: 0 },
                records: Vec::new(),
            }
        };
        if self.kind() == "UNTERMINATED" {
            self.unterminated();
        }
        let eof = self.token();
        Start {
            span: Span {
                start: first,
                end: self.source.len(),
            },
            header,
            csv,
            opt_eof: OptEof {
                span: eof.span,
                present: eof.kind == "EOF",
            },
        }
    }
    fn csv(&mut self) -> Csv {
        let start = self.token().span.start;
        let mut records = Vec::new();
        loop {
            if let Some(record) = self.record(records.len()) {
                records.push(record);
            }
            if self.kind() != "NEWLINE" {
                break;
            }
            self.take();
        }
        let end = records.last().map_or(start, |record| record.span.end);
        Csv {
            span: Span { start, end },
            records,
        }
    }
    fn record(&mut self, index: usize) -> Option<Record> {
        if self.kind() == "INVALID" {
            self.unknown();
            return None;
        }
        let source = self.field()?;
        if !self.comma() {
            return None;
        }
        let target = self.field()?;
        if !self.comma() {
            return None;
        }
        let value = self.field()?;
        if !matches!(self.kind(), "NEWLINE" | "EOF") {
            self.unexpected(&["EOF", "NEWLINE"]);
            return None;
        }
        Some(Record {
            span: Span {
                start: source.span.start,
                end: value.span.end,
            },
            source,
            target,
            value,
            index,
        })
    }
    fn comma(&mut self) -> bool {
        if self.kind() == "COMMA" {
            self.take();
            true
        } else {
            self.unexpected(&["COMMA"]);
            false
        }
    }
    fn field(&mut self) -> Option<Field> {
        match self.kind() {
            "COMMA" | "NEWLINE" | "EOF" => {
                let at = self.token().span.start;
                let span = Span { start: at, end: at };
                Some(Field {
                    span,
                    escaped: None,
                    non_escaped: Some(NonEscaped {
                        span,
                        text: String::new(),
                    }),
                })
            }
            "NON_ESCAPED_TEXT" => {
                let token = self.take();
                Some(Field {
                    span: token.span,
                    escaped: None,
                    non_escaped: Some(NonEscaped {
                        span: token.span,
                        text: token.text,
                    }),
                })
            }
            "DQUOTE" => self.escaped(),
            _ => {
                self.unexpected(&["DQUOTE", "NON_ESCAPED_TEXT"]);
                None
            }
        }
    }
    fn escaped(&mut self) -> Option<Field> {
        let open = self.take();
        let content = if self.kind() == "ESCAPED_TEXT" {
            self.take().text
        } else {
            String::new()
        };
        if self.kind() != "DQUOTE" {
            self.unexpected(&["DQUOTE"]);
            return None;
        }
        let close = self.take();
        let span = Span {
            start: open.span.start,
            end: close.span.end,
        };
        Some(Field {
            span,
            escaped: Some(Escaped {
                span,
                text: content,
            }),
            non_escaped: None,
        })
    }
}
