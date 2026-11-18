//! Recursive-descent parser for the pie grammar (`spec/grammar/pie.md`).

use crate::diag::Diagnostic;
use crate::source::Span;

use super::ast::{
    Eol, Metadata, Pie, PieSection, Statement, StatementKind, TitleAndAccessibilities,
};
use super::lexer::{Token, lex};
use super::{C_UNEXPECTED, C_UNKNOWN, C_UNTERMINATED, diagnostic};

pub struct Parsed {
    pub document: Pie,
    pub diagnostics: Vec<Diagnostic>,
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
    let show_data = parser.kind() == "showData";
    if show_data {
        parser.take();
    }
    let body = parser.statements();
    let content_end = parser.content_end();
    let diagnostics = super::lint_diagnostics::merge(source, parser.diagnostics, removed, &body);
    Parsed {
        document: Pie {
            span: Span {
                start: header.span.start,
                end: content_end,
            },
            header,
            show_data,
            body,
        },
        diagnostics,
    }
}

struct Parser<'a> {
    source: &'a str,
    tokens: Vec<Token>,
    at: usize,
    diagnostics: Vec<Diagnostic>,
}

fn metadata_field(kind: &str) -> Option<&'static str> {
    match kind {
        "ACC_DESCR" => Some("accDescr"),
        "ACC_TITLE" => Some("accTitle"),
        "TITLE" => Some("title"),
        _ => None,
    }
}

impl Parser<'_> {
    fn token(&self) -> Token {
        self.tokens.get(self.at).cloned().unwrap_or(Token {
            kind: "EOF",
            text: String::new(),
            span: Span {
                start: self.source.len(),
                end: self.source.len(),
            },
        })
    }

    fn kind(&self) -> &'static str {
        self.tokens.get(self.at).map_or("EOF", |t| t.kind)
    }

    fn take(&mut self) -> Token {
        let token = self.token();
        if self.at < self.tokens.len() {
            self.at += 1;
        }
        token
    }

    fn skip_newlines(&mut self) {
        while self.kind() == "NEWLINE" {
            self.at += 1;
        }
    }

    fn raw(&self, span: Span) -> &str {
        self.source.get(span.start..span.end).unwrap_or("")
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

    fn issue(&mut self, code: &'static str, message: String, span: Span) {
        self.diagnostics.push(diagnostic(code, message, span));
    }

    fn unexpected(&mut self, expected: &[&str]) {
        let token = self.token();
        if token.kind == "UNTERMINATED" {
            return;
        }
        let mut names: Vec<&str> = expected.to_vec();
        names.sort_unstable();
        let message = format!(
            "unexpected {}, expected one of: {}",
            self.raw(token.span),
            names.join(", ")
        );
        self.issue(C_UNEXPECTED, message, token.span);
    }

    fn line_end(&self) -> usize {
        self.tokens
            .get(self.at..)
            .unwrap_or_default()
            .iter()
            .find(|token| matches!(token.kind, "NEWLINE" | "EOF" | "UNTERMINATED"))
            .map_or(self.source.len(), |token| token.span.start)
    }

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

    fn header(&mut self) -> Token {
        if self.kind() == "pie" {
            return self.take();
        }
        self.unexpected(&["pie"]);
        Token {
            kind: "pie",
            text: String::new(),
            span: Span { start: 0, end: 0 },
        }
    }

    fn statements(&mut self) -> Vec<Statement> {
        let mut body = Vec::new();
        loop {
            match self.kind() {
                "EOF" => return body,
                "UNTERMINATED" => {
                    let token = self.token();
                    let message = format!("unterminated {}", token.text);
                    self.issue(C_UNTERMINATED, message, token.span);
                    return body;
                }
                "NEWLINE" => {
                    self.take();
                }
                _ => self.statement_or_unknown(&mut body),
            }
        }
    }

    fn statement_or_unknown(&mut self, body: &mut Vec<Statement>) {
        let first = self.token();
        let statement = match first.kind {
            "ACC_DESCR" | "ACC_TITLE" | "TITLE" => self.metadata(),
            "STRING" => self.section(),
            _ => {
                let message = format!("unknown statement {}", self.raw(first.span));
                let end = self.line_end().max(first.span.end);
                self.issue(
                    C_UNKNOWN,
                    message,
                    Span {
                        start: first.span.start,
                        end,
                    },
                );
                self.skip_line();
                return;
            }
        };
        body.extend(statement);
    }

    fn reject(&mut self) -> Option<Statement> {
        self.skip_line();
        None
    }

    fn eol(&mut self) -> Option<Eol> {
        let start = self.token().span.start;
        match self.kind() {
            "NEWLINE" => {
                let mut end = start;
                while self.kind() == "NEWLINE" {
                    end = self.take().span.end;
                }
                Some(Eol {
                    span: Span { start, end },
                })
            }
            "EOF" => Some(Eol {
                span: Span { start, end: start },
            }),
            _ => None,
        }
    }

    fn section(&mut self) -> Option<Statement> {
        let label = self.take();
        if self.kind() != ":" {
            self.unexpected(&[":"]);
            return self.reject();
        }
        self.take();
        if self.kind() != "NUMBER_PIE" {
            self.unexpected(&["NUMBER_PIE"]);
            return self.reject();
        }
        let number = self.take();
        let end = number.span.end;
        let Some(eol) = self.eol() else {
            self.unexpected(&["EOF", "NEWLINE"]);
            return self.reject();
        };
        Some(Statement {
            span: Span {
                start: label.span.start,
                end,
            },
            kind: StatementKind::PieSection(PieSection { label, number, eol }),
        })
    }

    fn metadata(&mut self) -> Option<Statement> {
        let mut items = Vec::new();
        let (mut start, mut end) = (0, 0);
        while let Some(field) = metadata_field(self.kind()) {
            let token = self.take();
            let Some(eol) = self.eol() else {
                self.unexpected(&["EOF", "NEWLINE"]);
                self.skip_line();
                break;
            };
            if items.is_empty() {
                start = token.span.start;
            }
            end = token.span.end;
            items.push(Metadata {
                field,
                value: token.text,
                span: token.span,
                eol,
            });
        }
        if items.is_empty() {
            return None;
        }
        Some(Statement {
            span: Span { start, end },
            kind: StatementKind::TitleAndAccessibilities(TitleAndAccessibilities { items }),
        })
    }
}
