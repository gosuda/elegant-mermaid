//! Recursive-descent parser for the radar grammar (`spec/grammar/radar.md`).

use crate::diag::Diagnostic;
use crate::source::Span;

use super::ast::{
    Axis, Curve, DetailedEntry, Entry, Label, Number, NumberEntry, RadarOption, Start, Text,
};
use super::lexer::{Token, lex};
use super::{C_UNEXPECTED, C_UNKNOWN, C_UNTERMINATED, diagnostic};

pub struct Parsed {
    pub document: Start,
    pub diagnostics: Vec<Diagnostic>,
}

const HEADER: &str = "radar-beta";
const OPTION_KEYWORDS: &[&str] = &["graticule", "max", "min", "showLegend", "ticks"];

fn option_value_kind(keyword: &str) -> &'static str {
    match keyword {
        "showLegend" => "BOOLEAN",
        "graticule" => "GRATICULE",
        _ => "NUMBER",
    }
}

pub fn parse(source: &str, removed: &[Span]) -> Parsed {
    let mut parser = Parser {
        source,
        tokens: lex(source, removed),
        at: 0,
        start: Start {
            span: Span { start: 0, end: 0 },
            header: Token {
                kind: "EOF",
                text: String::new(),
                span: Span { start: 0, end: 0 },
            },
            axes: Vec::new(),
            curves: Vec::new(),
            options: Vec::new(),
            title: None,
            acc_title: None,
            acc_descr: None,
        },
        diagnostics: Vec::new(),
    };
    parser.skip_newlines();
    parser.start.header = parser.header();
    parser.statements();
    let header_span = parser.start.header.span;
    parser.start.span = Span {
        start: header_span.start,
        end: parser.content_end().max(header_span.end),
    };
    Parsed {
        document: parser.start,
        diagnostics: parser.diagnostics,
    }
}

struct Parser<'a> {
    source: &'a str,
    tokens: Vec<Token>,
    at: usize,
    start: Start,
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

    fn expect(&mut self, kind: &'static str) -> Option<Token> {
        if self.kind() == kind {
            return Some(self.take());
        }
        self.unexpected(&[kind]);
        None
    }

    fn header(&mut self) -> Token {
        match self.kind() {
            "radar-beta:" => self.take(),
            HEADER => {
                let header = self.take();
                if self.kind() == ":" {
                    self.take();
                }
                header
            }
            _ => {
                self.unexpected(&[HEADER, "radar-beta:"]);
                Token {
                    kind: HEADER,
                    text: String::new(),
                    span: Span { start: 0, end: 0 },
                }
            }
        }
    }

    fn statements(&mut self) {
        loop {
            match self.kind() {
                "EOF" => return,
                "UNTERMINATED" => {
                    let token = self.token();
                    let message = format!("unterminated {}", token.text);
                    self.issue(C_UNTERMINATED, message, token.span);
                    return;
                }
                "NEWLINE" => {
                    self.take();
                }
                "ACC_DESCR" | "ACC_TITLE" | "TITLE" => self.metadata(),
                "axis" => self.axes(),
                "curve" => self.curves(),
                kind if OPTION_KEYWORDS.contains(&kind) => self.options(),
                _ => self.unknown(),
            }
        }
    }

    fn unknown(&mut self) {
        let first = self.take();
        let end = self.skip_statement();
        let message = format!("unknown statement {}", self.raw(first.span));
        self.issue(
            C_UNKNOWN,
            message,
            Span {
                start: first.span.start,
                end: end.max(first.span.end),
            },
        );
    }

    fn skip_statement(&mut self) -> usize {
        let mut end = self.content_end();
        let mut depth = 0usize;
        loop {
            match self.kind() {
                "EOF" | "UNTERMINATED" => return end,
                "NEWLINE" => {
                    self.take();
                    if depth == 0 {
                        return end;
                    }
                    continue;
                }
                "{" => depth += 1,
                "}" => depth = depth.saturating_sub(1),
                _ => {}
            }
            end = self.take().span.end;
        }
    }

    fn skip_braces(&mut self) {
        let mut depth = 1usize;
        while depth > 0 {
            match self.kind() {
                "EOF" | "UNTERMINATED" => return,
                "{" => depth += 1,
                "}" => depth -= 1,
                _ => {}
            }
            self.take();
        }
    }

    fn metadata(&mut self) {
        let token = self.take();
        match self.kind() {
            "NEWLINE" => self.skip_newlines(),
            "EOF" => {}
            _ => {
                self.unexpected(&["EOF", "NEWLINE"]);
                self.skip_statement();
                return;
            }
        }
        let text = Some(Text {
            value: token.text,
            span: token.span,
        });
        match token.kind {
            "ACC_DESCR" => self.start.acc_descr = text,
            "ACC_TITLE" => self.start.acc_title = text,
            _ => self.start.title = text,
        }
    }

    fn label(&mut self) -> Option<Option<Label>> {
        if self.kind() != "[" {
            return Some(None);
        }
        let open = self.take();
        let value = self.expect("STRING")?;
        let closing = self.expect("]")?;
        Some(Some(Label {
            span: Span {
                start: open.span.start,
                end: closing.span.end,
            },
            value,
        }))
    }

    fn axes(&mut self) {
        self.take();
        loop {
            let Some(name) = self.expect("ID") else {
                self.skip_statement();
                return;
            };
            let Some(label) = self.label() else {
                self.skip_statement();
                return;
            };
            let span = Span {
                start: name.span.start,
                end: self.content_end(),
            };
            self.start.axes.push(Axis { span, name, label });
            if self.kind() != "," {
                return;
            }
            self.take();
        }
    }

    fn curves(&mut self) {
        self.take();
        loop {
            let Some(curve) = self.curve() else {
                return;
            };
            self.start.curves.push(curve);
            if self.kind() != "," {
                return;
            }
            self.take();
        }
    }

    fn curve(&mut self) -> Option<Curve> {
        let Some(name) = self.expect("ID") else {
            self.skip_statement();
            return None;
        };
        let Some(label) = self.label() else {
            self.skip_statement();
            return None;
        };
        if self.expect("{").is_none() {
            self.skip_statement();
            return None;
        }
        let Some(entries) = self.entries() else {
            self.skip_braces();
            return None;
        };
        let Some(closing) = self.expect("}") else {
            self.skip_braces();
            return None;
        };
        Some(Curve {
            span: Span {
                start: name.span.start,
                end: closing.span.end,
            },
            name,
            label,
            entries,
        })
    }

    fn entries(&mut self) -> Option<Vec<Entry>> {
        self.skip_newlines();
        let first = self.kind();
        if first != "NUMBER" && first != "ID" {
            self.unexpected(&["ID", "NUMBER"]);
            return None;
        }
        let mut entries = Vec::new();
        loop {
            entries.push(self.entry(first)?);
            if self.kind() != "," {
                self.skip_newlines();
                return Some(entries);
            }
            self.take();
            self.skip_newlines();
        }
    }

    fn entry(&mut self, kind: &str) -> Option<Entry> {
        if kind == "NUMBER" {
            return Some(Entry::Number(NumberEntry {
                value: self.number()?,
            }));
        }
        let axis = self.expect("ID")?;
        if self.kind() == ":" {
            self.take();
        }
        let value = self.number()?;
        Some(Entry::Detailed(DetailedEntry {
            span: Span {
                start: axis.span.start,
                end: value.span.end,
            },
            axis,
            value,
        }))
    }

    fn number(&mut self) -> Option<Number> {
        let token = self.expect("NUMBER")?;
        Some(Number {
            span: token.span,
            text: token.text,
        })
    }

    fn options(&mut self) {
        loop {
            let name = self.take();
            let Some(value) = self.expect(option_value_kind(name.kind)) else {
                self.skip_statement();
                return;
            };
            self.start.options.push(RadarOption {
                span: Span {
                    start: name.span.start,
                    end: value.span.end,
                },
                name,
                value,
            });
            if self.kind() != "," {
                return;
            }
            self.take();
            if !OPTION_KEYWORDS.contains(&self.kind()) {
                self.unexpected(OPTION_KEYWORDS);
                self.skip_statement();
                return;
            }
        }
    }
}
