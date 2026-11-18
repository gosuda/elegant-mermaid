//! Recursive-descent parser for `spec/grammar/architecture.md`.
//!
//! An error records one diagnostic and skips to the next physical line; a skipped
//! statement creates no node. Consecutive metadata statements merge into one.

use crate::diag::Diagnostic;
use crate::source::Span;

use super::ast::{
    Alignment, Architecture, Edge, Group, Junction, Metadata, MetadataItem, Service, Statement,
    StatementKind, Value,
};
use super::lexer::{Token, lex};
use super::{C_DIRECTION, C_TOO_FEW, C_UNEXPECTED, C_UNKNOWN, C_UNTERMINATED, diagnostic};

type Slots<'a> = &'a [&'a [&'static str]];

const GROUP_SLOTS: Slots = &[&["ARCH_ICON"], &["ARCH_TITLE"], &["in"]];
const SERVICE_SLOTS: Slots = &[&["ARCH_ICON", "STRING"], &["ARCH_TITLE"], &["in"]];
const JUNCTION_SLOTS: Slots = &[&["in"]];

pub struct Parsed {
    pub document: Architecture,
    pub diagnostics: Vec<Diagnostic>,
}

pub fn parse(source: &str, removed: &[Span]) -> Parsed {
    let mut parser = Parser {
        src: source,
        tokens: lex(source, removed),
        at: 0,
        statement_end: 0,
        diags: Vec::new(),
    };
    parser.skip_newlines();
    let header = parser.header();
    let mut statements = Vec::new();
    parser.statements(&mut statements);
    Parsed {
        document: Architecture {
            span: Span {
                start: header.span.start,
                end: source.len(),
            },
            header,
            statements,
        },
        diagnostics: parser.diags,
    }
}

struct Parser<'a> {
    src: &'a str,
    tokens: Vec<Token>,
    at: usize,
    statement_end: usize,
    diags: Vec<Diagnostic>,
}

fn metadata_field(kind: &str) -> &'static str {
    match kind {
        "ACC_DESCR" => "accDescr",
        "ACC_TITLE" => "accTitle",
        _ => "title",
    }
}

fn absent(span: &Option<Span>, kind: &'static str) -> Vec<&'static str> {
    if span.is_none() {
        vec![kind]
    } else {
        Vec::new()
    }
}

fn pending(slots: Slots, from: usize) -> Vec<&'static str> {
    slots[from..]
        .iter()
        .flat_map(|kinds| kinds.iter().copied())
        .collect()
}

impl Parser<'_> {
    fn token(&self) -> Token {
        self.tokens.get(self.at).cloned().unwrap_or(Token {
            kind: "EOF",
            text: String::new(),
            span: Span {
                start: self.src.len(),
                end: self.src.len(),
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

    fn content_end(&self) -> usize {
        self.tokens[..self.at.min(self.tokens.len())]
            .iter()
            .rev()
            .find(|t| t.kind != "NEWLINE")
            .map_or(0, |t| t.span.end)
    }

    fn issue(&mut self, code: &'static str, message: String, span: Span) {
        self.diags.push(diagnostic(code, message, span));
    }

    fn unexpected(&mut self, expected: &[&str]) {
        let token = self.token();
        if token.kind == "UNTERMINATED" {
            return;
        }
        let mut names = expected.to_vec();
        names.sort_unstable();
        let message = format!(
            "unexpected {}, expected one of: {}",
            &self.src[token.span.start..token.span.end],
            names.join(", ")
        );
        self.issue(C_UNEXPECTED, message, token.span);
    }

    fn line_end(&self) -> usize {
        self.tokens
            .get(self.at..)
            .unwrap_or_default()
            .iter()
            .find(|t| matches!(t.kind, "NEWLINE" | "EOF" | "UNTERMINATED"))
            .map_or(self.src.len(), |t| t.span.start)
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
        if matches!(self.kind(), "architecture-beta" | "architecture") {
            return self.take();
        }
        self.unexpected(&["architecture", "architecture-beta"]);
        Token {
            kind: "architecture-beta",
            text: String::new(),
            span: Span { start: 0, end: 0 },
        }
    }

    fn statements(&mut self, out: &mut Vec<Statement>) {
        loop {
            match self.kind() {
                "EOF" => return,
                "UNTERMINATED" => {
                    let token = self.token();
                    self.issue(
                        C_UNTERMINATED,
                        format!("unterminated {}", token.text),
                        token.span,
                    );
                    return;
                }
                "NEWLINE" => {
                    self.take();
                }
                _ => self.statement_or_unknown(out),
            }
        }
    }

    fn statement_or_unknown(&mut self, out: &mut Vec<Statement>) {
        let first = self.token();
        let parsed = match first.kind {
            "group" => self.group(),
            "service" => self.service(),
            "junction" => self.junction(),
            "align" => self.alignment(),
            "ID" => self.edge(),
            "ACC_DESCR" | "ACC_TITLE" | "TITLE" => self.metadata(),
            _ => {
                let end = self.line_end().max(first.span.end);
                self.issue(
                    C_UNKNOWN,
                    format!(
                        "unknown statement {}",
                        &self.src[first.span.start..first.span.end]
                    ),
                    Span {
                        start: first.span.start,
                        end,
                    },
                );
                self.skip_line();
                return;
            }
        };
        let Some(kind) = parsed else { return };
        let span = Span {
            start: first.span.start,
            end: self.statement_end,
        };
        if let StatementKind::Metadata(incoming) = &kind
            && let Some(Statement {
                kind: StatementKind::Metadata(existing),
                span: last,
            }) = out.last_mut()
        {
            existing.items.extend(incoming.items.iter().cloned());
            last.end = span.end;
            return;
        }
        out.push(Statement { span, kind });
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

    fn value(&mut self, kind: &'static str) -> Option<Value> {
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

    fn fill(&mut self, slots: Slots, mut assign: impl FnMut(usize, &str, Value)) -> Option<usize> {
        let mut next = 0;
        for (i, kinds) in slots.iter().enumerate() {
            let kind = self.kind();
            if !kinds.contains(&kind) {
                continue;
            }
            let token = self.take();
            let value = if kind == "in" {
                self.value("ID")?
            } else {
                Value {
                    text: token.text,
                    span: token.span,
                }
            };
            assign(i, kind, value);
            next = i + 1;
        }
        Some(next)
    }

    fn group(&mut self) -> Option<StatementKind> {
        let keyword = self.take().span;
        let Some(id) = self.value("ID") else {
            return self.reject();
        };
        let (mut icon, mut title, mut parent) = (None, None, None);
        let filled = self.fill(GROUP_SLOTS, |slot, _, v| match slot {
            0 => icon = Some(v),
            1 => title = Some(v),
            _ => parent = Some(v),
        });
        let Some(next) = filled else {
            return self.reject();
        };
        let node = Group {
            keyword,
            id,
            icon,
            title,
            parent,
        };
        self.finish(StatementKind::Group(node), &pending(GROUP_SLOTS, next))
    }

    fn service(&mut self) -> Option<StatementKind> {
        let keyword = self.take().span;
        let Some(id) = self.value("ID") else {
            return self.reject();
        };
        let (mut icon_text, mut icon, mut title, mut parent) = (None, None, None, None);
        let filled = self.fill(SERVICE_SLOTS, |slot, kind, v| match (slot, kind) {
            (0, "STRING") => icon_text = Some(v),
            (0, _) => icon = Some(v),
            (1, _) => title = Some(v),
            _ => parent = Some(v),
        });
        let Some(next) = filled else {
            return self.reject();
        };
        let node = Service {
            keyword,
            id,
            icon_text,
            icon,
            title,
            parent,
        };
        self.finish(StatementKind::Service(node), &pending(SERVICE_SLOTS, next))
    }

    fn junction(&mut self) -> Option<StatementKind> {
        let keyword = self.take().span;
        let Some(id) = self.value("ID") else {
            return self.reject();
        };
        let mut parent = None;
        let Some(next) = self.fill(JUNCTION_SLOTS, |_, _, v| parent = Some(v)) else {
            return self.reject();
        };
        let node = Junction {
            keyword,
            id,
            parent,
        };
        self.finish(
            StatementKind::Junction(node),
            &pending(JUNCTION_SLOTS, next),
        )
    }

    fn alignment(&mut self) -> Option<StatementKind> {
        let keyword = self.take().span;
        if !matches!(self.kind(), "row" | "column") {
            self.unexpected(&["column", "row"]);
            return self.reject();
        }
        let direction = self.take();
        let mut members = Vec::new();
        while self.kind() == "ID" {
            let member = self.take();
            members.push(Value {
                text: member.text,
                span: member.span,
            });
        }
        if members.len() < 2 {
            if matches!(self.kind(), "NEWLINE" | "EOF") {
                let span = Span {
                    start: keyword.start,
                    end: self.content_end(),
                };
                self.issue(
                    C_TOO_FEW,
                    "alignment requires at least two members".into(),
                    span,
                );
                return self.reject();
            }
            self.unexpected(&["ID"]);
            return self.reject();
        }
        let node = Alignment {
            keyword,
            direction: Value {
                text: direction.kind.into(),
                span: direction.span,
            },
            members,
        };
        self.finish(StatementKind::Alignment(node), &["ID"])
    }

    fn optional_span(&mut self, kind: &'static str) -> Option<Span> {
        (self.kind() == kind).then(|| self.take().span)
    }

    fn colon(&mut self, alternatives: &[&'static str]) -> bool {
        if self.kind() == ":" {
            self.take();
            return true;
        }
        let mut names = vec![":"];
        names.extend_from_slice(alternatives);
        self.unexpected(&names);
        false
    }

    fn edge(&mut self) -> Option<StatementKind> {
        let lhs = self.take();
        let lhs_group = self.optional_span("ARROW_GROUP");
        if !self.colon(&absent(&lhs_group, "ARROW_GROUP")) {
            return self.reject();
        }
        let Some(lhs_dir) = self.port(&[]) else {
            return self.reject();
        };
        let lhs_into = self.optional_span("ARROW_INTO");
        let Some(title) = self.dashes(&lhs_into) else {
            return self.reject();
        };
        let rhs_into = self.optional_span("ARROW_INTO");
        let Some(rhs_dir) = self.port(&absent(&rhs_into, "ARROW_INTO")) else {
            return self.reject();
        };
        if !self.colon(&[]) {
            return self.reject();
        }
        let Some(rhs_id) = self.value("ID") else {
            return self.reject();
        };
        let rhs_group = self.optional_span("ARROW_GROUP");
        let node = Edge {
            lhs_id: Value {
                text: lhs.text,
                span: lhs.span,
            },
            lhs_group,
            lhs_dir,
            lhs_into,
            title,
            rhs_into,
            rhs_dir,
            rhs_id,
            rhs_group,
        };
        self.finish(StatementKind::Edge(node), &["ARROW_GROUP"])
    }

    fn port(&mut self, alternatives: &[&'static str]) -> Option<Value> {
        match self.kind() {
            "ARROW_DIRECTION" => {
                let token = self.take();
                return Some(Value {
                    text: token.text,
                    span: token.span,
                });
            }
            "ID" => {
                let token = self.token();
                self.issue(
                    C_DIRECTION,
                    format!("invalid edge direction {}; expected L, R, T, B", token.text),
                    token.span,
                );
                return None;
            }
            _ => {}
        }
        let mut names = vec!["ARROW_DIRECTION"];
        names.extend_from_slice(alternatives);
        self.unexpected(&names);
        None
    }

    fn dashes(&mut self, lhs_into: &Option<Span>) -> Option<Option<Value>> {
        match self.kind() {
            "--" => {
                self.take();
                return Some(None);
            }
            "-" => {
                self.take();
                let title = self.value("ARCH_TITLE")?;
                self.value("-")?;
                return Some(Some(title));
            }
            _ => {}
        }
        let mut names = vec!["--", "-"];
        names.extend(absent(lhs_into, "ARROW_INTO"));
        self.unexpected(&names);
        None
    }

    fn metadata(&mut self) -> Option<StatementKind> {
        let token = self.take();
        let item = MetadataItem {
            field: metadata_field(token.kind),
            value: token.text,
            span: token.span,
        };
        self.finish(StatementKind::Metadata(Metadata { items: vec![item] }), &[])
    }
}
