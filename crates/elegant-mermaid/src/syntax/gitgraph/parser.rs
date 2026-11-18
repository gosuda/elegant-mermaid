//! Recursive-descent parser for the gitgraph grammar (`spec/grammar/gitgraph.md`).

use crate::diag::Diagnostic;
use crate::source::Span;

use super::ast::{
    Branch, Checkout, CherryPicking, Commit, Merge, Metadata, Order, Start, Statement,
    StatementKind, Value,
};
use super::lexer::{Token, lex};
use super::{C_UNEXPECTED, C_UNKNOWN, C_UNTERMINATED, diagnostic};

pub struct Parsed {
    pub document: Start,
    pub diagnostics: Vec<Diagnostic>,
}

const COMMIT_OPTIONS: &[&str] = &["STRING", "id:", "msg:", "tag:", "type:"];
const MERGE_OPTIONS: &[&str] = &["id:", "tag:", "type:"];
const PICK_OPTIONS: &[&str] = &["id:", "parent:", "tag:"];
const COMMIT_TYPES: &[&str] = &["HIGHLIGHT", "NORMAL", "REVERSE"];

pub fn parse(source: &str, removed: &[Span]) -> Parsed {
    let mut parser = Parser {
        source,
        tokens: lex(source, removed),
        at: 0,
        statement_end: 0,
        diagnostics: Vec::new(),
    };
    parser.skip_newlines();
    let (header, direction) = parser.header();
    let statements = parser.statements();
    Parsed {
        document: Start {
            span: Span {
                start: header.span.start,
                end: source.len(),
            },
            header,
            direction,
            statements,
        },
        diagnostics: parser.diagnostics,
    }
}

enum Outcome {
    Unknown,
    Rejected,
    Parsed(StatementKind),
}

#[derive(Default)]
struct Options {
    id: Option<Value>,
    message: Option<Value>,
    parent: Option<Value>,
    commit_type: Option<Value>,
    tags: Vec<Value>,
}

impl Options {
    fn assign(&mut self, keyword: &str, value: Value) {
        match keyword {
            "id:" => self.id = Some(value),
            "msg:" => self.message = Some(value),
            "parent:" => self.parent = Some(value),
            "type:" => self.commit_type = Some(value),
            _ => self.tags.push(value),
        }
    }
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

    fn header(&mut self) -> (Token, Option<Token>) {
        match self.kind() {
            "gitGraph:" => (self.take(), None),
            "gitGraph" => self.bare_header(),
            _ => {
                self.unexpected(&["gitGraph", "gitGraph:"]);
                (
                    Token {
                        kind: "gitGraph",
                        text: String::new(),
                        span: Span { start: 0, end: 0 },
                    },
                    None,
                )
            }
        }
    }

    fn bare_header(&mut self) -> (Token, Option<Token>) {
        let header = self.take();
        match self.kind() {
            ":" => {
                self.take();
                (header, None)
            }
            "LR" | "TB" | "BT" => {
                let direction = self.take();
                if self.kind() == ":" {
                    self.take();
                } else {
                    self.unexpected(&[":"]);
                }
                (header, Some(direction))
            }
            _ => (header, None),
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
        match self.statement_kind(first.kind) {
            Outcome::Unknown => {
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
            }
            Outcome::Rejected => {}
            Outcome::Parsed(kind) => statements.push(Statement {
                span: Span {
                    start: first.span.start,
                    end: self.statement_end,
                },
                kind,
            }),
        }
    }

    fn statement_kind(&mut self, first: &str) -> Outcome {
        let parsed = match first {
            "commit" => self.commit(),
            "branch" => self.branch(),
            "merge" => self.merge(),
            "checkout" | "switch" => self.checkout(),
            "cherry-pick" => self.cherry_pick(),
            "ACC_DESCR" | "ACC_TITLE" | "TITLE" => self.metadata(),
            _ => return Outcome::Unknown,
        };
        parsed.map_or(Outcome::Rejected, Outcome::Parsed)
    }

    fn finish(&mut self, kind: StatementKind, expected: &[&str]) -> Option<StatementKind> {
        let end = self.content_end();
        match self.kind() {
            "NEWLINE" => {
                self.take();
            }
            "EOF" => {}
            _ => {
                let mut names = expected.to_vec();
                names.extend(["EOF", "NEWLINE"]);
                self.unexpected(&names);
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

    fn text(&mut self, kind: &'static str) -> Option<Value> {
        if self.kind() != kind {
            self.unexpected(&[kind]);
            return None;
        }
        let token = self.take();
        Some(Value {
            text: token.text,
            span: token.span,
        })
    }

    fn name(&mut self) -> Option<Value> {
        if matches!(self.kind(), "REFERENCE" | "STRING") {
            let token = self.take();
            return Some(Value {
                text: token.text,
                span: token.span,
            });
        }
        self.unexpected(&["REFERENCE", "STRING"]);
        None
    }

    fn commit_type(&mut self) -> Option<Value> {
        if matches!(self.kind(), "NORMAL" | "REVERSE" | "HIGHLIGHT") {
            let token = self.take();
            return Some(Value {
                text: token.kind.to_owned(),
                span: token.span,
            });
        }
        self.unexpected(COMMIT_TYPES);
        None
    }

    fn options(&mut self, allowed: &[&str]) -> Option<Options> {
        let mut found = Options::default();
        while allowed.contains(&self.kind()) {
            let mut keyword = self.kind();
            if keyword == "STRING" {
                keyword = "msg:";
            } else {
                self.take();
            }
            let value = if keyword == "type:" {
                self.commit_type()?
            } else {
                self.text("STRING")?
            };
            found.assign(keyword, value);
        }
        Some(found)
    }

    fn commit(&mut self) -> Option<StatementKind> {
        let keyword = self.take().span;
        let Some(found) = self.options(COMMIT_OPTIONS) else {
            return self.reject();
        };
        let node = StatementKind::Commit(Commit {
            keyword,
            id: found.id,
            message: found.message,
            tags: found.tags,
            commit_type: found.commit_type,
        });
        self.finish(node, COMMIT_OPTIONS)
    }

    fn merge(&mut self) -> Option<StatementKind> {
        let keyword = self.take().span;
        let Some(branch) = self.name() else {
            return self.reject();
        };
        let Some(found) = self.options(MERGE_OPTIONS) else {
            return self.reject();
        };
        let node = StatementKind::Merge(Merge {
            keyword,
            branch,
            id: found.id,
            tags: found.tags,
            commit_type: found.commit_type,
        });
        self.finish(node, MERGE_OPTIONS)
    }

    fn cherry_pick(&mut self) -> Option<StatementKind> {
        let keyword = self.take().span;
        let Some(found) = self.options(PICK_OPTIONS) else {
            return self.reject();
        };
        let node = StatementKind::CherryPicking(CherryPicking {
            keyword,
            id: found.id,
            tags: found.tags,
            parent: found.parent,
        });
        self.finish(node, PICK_OPTIONS)
    }

    fn branch(&mut self) -> Option<StatementKind> {
        let keyword = self.take().span;
        let Some(name) = self.name() else {
            return self.reject();
        };
        if self.kind() != "order:" {
            let node = StatementKind::Branch(Branch {
                keyword,
                name,
                order: None,
            });
            return self.finish(node, &["order:"]);
        }
        self.take();
        let token = self.token();
        if token.kind != "INT" {
            self.unexpected(&["INT"]);
            return self.reject();
        }
        self.take();
        let node = StatementKind::Branch(Branch {
            keyword,
            name,
            order: Some(Order {
                value: parse_order(&token.text),
                span: token.span,
            }),
        });
        self.finish(node, &[])
    }

    fn checkout(&mut self) -> Option<StatementKind> {
        let keyword = self.take();
        let Some(branch) = self.name() else {
            return self.reject();
        };
        let node = StatementKind::Checkout(Checkout {
            keyword: keyword.span,
            switch: keyword.kind == "switch",
            branch,
        });
        self.finish(node, &[])
    }

    fn metadata(&mut self) -> Option<StatementKind> {
        let token = self.take();
        let field = match token.kind {
            "ACC_DESCR" => "accDescr",
            "ACC_TITLE" => "accTitle",
            _ => "title",
        };
        let node = StatementKind::Metadata(Metadata {
            field,
            value: token.text,
        });
        self.finish(node, &[])
    }
}

fn parse_order(text: &str) -> i64 {
    text.parse::<i32>().map_or(i64::from(i32::MAX), i64::from)
}
