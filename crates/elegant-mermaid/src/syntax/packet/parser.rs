//! Recursive-descent parser for the packet grammar (`spec/grammar/packet.md`).

use crate::diag::Diagnostic;
use crate::source::Span;

use super::ast::{Label, Metadata, Operand, PacketBlock, Start, Statement, StatementKind};
use super::lexer::{Token, lex};
use super::{C_UNEXPECTED, C_UNKNOWN, C_UNTERMINATED, diagnostic};

pub struct Parsed {
    pub document: Start,
    pub diagnostics: Vec<Diagnostic>,
}

const MAX_INT: i64 = 2_147_483_647;

pub fn parse(source: &str, removed: &[Span]) -> Parsed {
    let mut parser = Parser {
        source,
        tokens: lex(source, removed),
        at: 0,
        statement_end: 0,
        diagnostics: Vec::new(),
    };
    parser.skip_newlines();
    let header = parser.header();
    let statements = parser.statements();
    Parsed {
        document: Start {
            span: Span {
                start: header.span.start,
                end: source.len(),
            },
            header,
            statements,
        },
        diagnostics: parser.diagnostics,
    }
}

fn metadata_field(kind: &str) -> &'static str {
    match kind {
        "ACC_DESCR" => "accDescr",
        "ACC_TITLE" => "accTitle",
        _ => "title",
    }
}

fn parse_int(text: &str) -> i64 {
    text.parse::<i64>()
        .map_or(MAX_INT, |value| value.min(MAX_INT))
}

struct Parser<'a> {
    source: &'a str,
    tokens: Vec<Token>,
    at: usize,
    statement_end: usize,
    diagnostics: Vec<Diagnostic>,
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
        if matches!(self.kind(), "packet" | "packet-beta") {
            return self.take();
        }
        self.unexpected(&["packet", "packet-beta"]);
        Token {
            kind: "packet",
            text: String::new(),
            span: Span { start: 0, end: 0 },
        }
    }

    fn statements(&mut self) -> Vec<Statement> {
        let mut statements = Vec::new();
        loop {
            match self.kind() {
                "EOF" => return statements,
                "UNTERMINATED" => {
                    let token = self.token();
                    let message = format!("unterminated {}", token.text);
                    self.issue(C_UNTERMINATED, message, token.span);
                    return statements;
                }
                "NEWLINE" => {
                    self.take();
                }
                _ => self.statement_or_unknown(&mut statements),
            }
        }
    }

    fn statement_or_unknown(&mut self, statements: &mut Vec<Statement>) {
        let first = self.token();
        let parsed = match first.kind {
            "INT" | "+" => self.block(),
            "ACC_DESCR" | "ACC_TITLE" | "TITLE" => self.metadata(),
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
        if let Some(kind) = parsed {
            statements.push(Statement {
                span: Span {
                    start: first.span.start,
                    end: self.statement_end,
                },
                kind,
            });
        }
    }

    fn finish(&mut self, kind: StatementKind) -> Option<StatementKind> {
        let end = self.content_end();
        match self.kind() {
            "NEWLINE" => {
                self.take();
            }
            "EOF" => {}
            _ => {
                self.unexpected(&["EOF", "NEWLINE"]);
                return self.reject();
            }
        }
        self.statement_end = end;
        Some(kind)
    }

    fn reject(&mut self) -> Option<StatementKind> {
        self.skip_line();
        None
    }

    fn operand(&mut self) -> Option<Operand> {
        if self.kind() != "INT" {
            self.unexpected(&["INT"]);
            return None;
        }
        let token = self.take();
        Some(Operand {
            value: parse_int(&token.text),
            span: token.span,
        })
    }

    fn block(&mut self) -> Option<StatementKind> {
        let mut node = PacketBlock {
            start: None,
            end: None,
            bits: None,
            label: Label {
                text: String::new(),
                span: Span { start: 0, end: 0 },
            },
        };
        let colon = if self.kind() == "+" {
            self.take();
            node.bits = self.operand();
            (node.bits.is_some()).then_some(&[":"][..])
        } else {
            self.range_operands(&mut node)
        };
        match colon {
            Some(expected) => self.label(node, expected),
            None => self.reject(),
        }
    }

    fn range_operands(&mut self, node: &mut PacketBlock) -> Option<&'static [&'static str]> {
        node.start = Some(self.operand()?);
        if self.kind() != "-" {
            return Some(&["-", ":"]);
        }
        self.take();
        node.end = Some(self.operand()?);
        Some(&[":"])
    }

    fn label(&mut self, mut node: PacketBlock, colon: &[&str]) -> Option<StatementKind> {
        if self.kind() != ":" {
            self.unexpected(colon);
            return self.reject();
        }
        self.take();
        if self.kind() != "STRING" {
            self.unexpected(&["STRING"]);
            return self.reject();
        }
        let label = self.take();
        node.label = Label {
            text: label.text,
            span: label.span,
        };
        self.finish(StatementKind::PacketBlock(node))
    }

    fn metadata(&mut self) -> Option<StatementKind> {
        let token = self.take();
        self.finish(StatementKind::Metadata(Metadata {
            field: metadata_field(token.kind),
            value: token.text,
        }))
    }
}
