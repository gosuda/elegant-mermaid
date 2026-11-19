//! Recursive-descent parser for the quadrant grammar (`spec/grammar/quadrant.md`).

use crate::diag::Diagnostic;
use crate::source::Span;

use super::ast::{
    Accessibility, AxisDetails, ClassDefStatement, Document, IdString, Line, Points,
    QuadrantDetails, Start, Statement, StatementKind, Style, StylesOpt, Text, Title,
};
use super::lexer::{Token, lex};
use super::{C_UNEXPECTED, C_UNKNOWN, C_UNTERMINATED, diagnostic};

const TEXT_TAIL_TOKENS: &[&str] = &[
    "ALPHA",
    "AMP",
    "BRKT",
    "COMMA",
    "DOT",
    "EQUALS",
    "MULT",
    "NUM",
    "PLUS",
    "PUNCTUATION",
    "UNDERSCORE",
    "UNICODE_TEXT",
    "MINUS",
    "SPACE",
];

const TEXT_STARTS: &[&str] = &[
    "ALPHA",
    "AMP",
    "BRKT",
    "COMMA",
    "DOT",
    "EQUALS",
    "MULT",
    "NUM",
    "PLUS",
    "PUNCTUATION",
    "UNDERSCORE",
    "UNICODE_TEXT",
    "MD_STR",
    "STR",
];

const STYLE_COMPONENTS: &[&str] = &["ALPHA", "BRKT", "COLON", "MINUS", "NUM", "SPACE"];

const ID_STRING_TOKENS: &[&str] = &[
    "ALPHA",
    "AMP",
    "BRKT",
    "COLON",
    "COMMA",
    "MINUS",
    "MULT",
    "NUM",
    "UNICODE_TEXT",
];

const END_OF_LINE: &[&str] = &["EOF", "NEWLINE", "SEMI"];

pub struct Parsed<'a> {
    pub document: Start<'a>,
    pub diagnostics: Vec<Diagnostic>,
}

pub fn parse<'a>(source: &'a str, removed: &[Span]) -> Parsed<'a> {
    let mut parser = Parser {
        source,
        tokens: lex(source, removed),
        at: 0,
        diagnostics: Vec::new(),
    };
    let document = parser.start();
    Parsed {
        document,
        diagnostics: parser.diagnostics,
    }
}

struct Parser<'a> {
    source: &'a str,
    tokens: Vec<Token<'a>>,
    at: usize,
    diagnostics: Vec<Diagnostic>,
}

type Outcome<'a> = (Option<StatementKind<'a>>, bool);

fn blank_token<'a>(kind: &'static str, at: usize) -> Token<'a> {
    let span = Span { start: at, end: at };
    Token {
        kind,
        text: "",
        span,
        content: span,
    }
}

fn settle<'a, T>(node: Option<T>, wrap: fn(T) -> StatementKind<'a>) -> Outcome<'a> {
    match node {
        Some(node) => (Some(wrap(node)), true),
        None => (None, false),
    }
}

impl<'a> Parser<'a> {
    fn token(&self) -> Token<'a> {
        self.tokens
            .get(self.at)
            .cloned()
            .unwrap_or_else(|| blank_token("EOF", self.source.len()))
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

    fn last_end(&self) -> usize {
        self.at
            .checked_sub(1)
            .and_then(|i| self.tokens.get(i))
            .map_or(0, |t| t.span.end)
    }

    fn is(&self, kinds: &[&str]) -> bool {
        kinds.contains(&self.kind())
    }

    fn raw(&self, from: usize, to: usize) -> &'a str {
        self.source.get(from..to).unwrap_or("")
    }

    fn issue(&mut self, code: &'static str, message: String, span: Span) {
        self.diagnostics.push(diagnostic(code, message, span));
    }

    fn describe(&self, token: &Token<'_>) -> &'a str {
        if token.kind == "EOF" {
            return "end of input";
        }
        if token.kind == "INVALID" && token.span.start == token.span.end {
            return "end of line";
        }
        self.raw(token.span.start, token.span.end)
    }

    fn unexpected(&mut self, expected: &[&str]) {
        let token = self.token();
        if token.kind == "UNTERMINATED" {
            self.unterminated(&token);
            return;
        }
        let mut names = expected.to_vec();
        names.sort_unstable();
        names.dedup();
        let message = format!(
            "unexpected {}, expected one of: {}",
            self.describe(&token),
            names.join(", ")
        );
        self.issue(C_UNEXPECTED, message, token.span);
        let end = self.last_end();
        self.recover(end);
    }

    fn unterminated(&mut self, token: &Token<'_>) {
        self.issue(
            C_UNTERMINATED,
            format!("unterminated {}", token.text),
            token.span,
        );
        self.take();
    }

    fn boundary(&self, prev_end: usize) -> bool {
        let token = self.token();
        if matches!(token.kind, "NEWLINE" | "SEMI" | "EOF" | "UNTERMINATED") {
            return true;
        }
        self.raw(prev_end.min(token.span.start), token.span.start)
            .contains(['\n', '\r'])
    }

    fn recover(&mut self, mut prev_end: usize) {
        while !self.boundary(prev_end) {
            prev_end = self.take().span.end;
        }
    }

    fn start(&mut self) -> Start<'a> {
        let first = self.token().span.start;
        while matches!(self.kind(), "NEWLINE" | "SEMI" | "SPACE") {
            self.take();
        }
        let end = self.source.len();
        if self.kind() != "QUADRANT" {
            self.unexpected(&["QUADRANT", "NEWLINE", "SEMI", "SPACE"]);
            return Start {
                span: Span { start: first, end },
                header: blank_token("", 0),
                document: Document {
                    span: Span { start: end, end },
                    lines: Vec::new(),
                },
            };
        }
        let header = self.take();
        let document = self.document();
        Start {
            span: Span { start: first, end },
            header,
            document,
        }
    }

    fn document(&mut self) -> Document<'a> {
        let start = self.token().span.start;
        let mut end = start;
        let mut lines = Vec::new();
        while self.kind() != "EOF" {
            if self.kind() == "UNTERMINATED" {
                let token = self.token();
                self.unterminated(&token);
                continue;
            }
            let line = self.line();
            end = end.max(line.span.end);
            lines.push(line);
        }
        Document {
            span: Span { start, end },
            lines,
        }
    }

    fn line(&mut self) -> Line<'a> {
        let (statement, ok) = self.statement();
        let mut span = statement.span;
        if ok && !self.is(END_OF_LINE) {
            self.unexpected(END_OF_LINE);
        }
        let eol = self.terminate(&mut span);
        Line {
            span,
            statement,
            eol,
        }
    }

    fn terminate(&mut self, span: &mut Span) -> Token<'a> {
        let eol = match self.kind() {
            "NEWLINE" | "SEMI" => self.take(),
            "EOF" => self.token(),
            _ => return blank_token("EOF", self.last_end()),
        };
        span.end = span.end.max(eol.span.end);
        eol
    }

    fn statement(&mut self) -> (Statement<'a>, bool) {
        let first = self.token().span.start;
        while self.kind() == "SPACE" {
            self.take();
        }
        let at = self.at;
        let (kind, ok) = self.statement_kind();
        let mut end = self.last_end();
        if self.at == at {
            end = first.max(self.last_end());
            if self.at == 0 || end < first {
                end = first;
            }
        }
        (
            Statement {
                span: Span { start: first, end },
                kind,
            },
            ok,
        )
    }

    fn statement_kind(&mut self) -> Outcome<'a> {
        match self.kind() {
            "CLASSDEF" => settle(self.class_def(), StatementKind::ClassDef),
            "X-AXIS" | "Y-AXIS" => settle(self.axis(), StatementKind::AxisDetails),
            "QUADRANT_1" | "QUADRANT_2" | "QUADRANT_3" | "QUADRANT_4" => {
                settle(self.quadrant_details(), StatementKind::QuadrantDetails)
            }
            "title" => settle(self.title(), StatementKind::Title),
            "acc_title" | "acc_descr" => settle(self.accessibility(), StatementKind::Accessibility),
            "acc_descr_multiline_value" => {
                let value = self.take();
                let node = Accessibility {
                    span: value.span,
                    title: false,
                    multiline: true,
                    value,
                };
                (Some(StatementKind::Accessibility(node)), true)
            }
            "NEWLINE" | "SEMI" | "EOF" | "UNTERMINATED" => (None, true),
            _ if self.is(TEXT_STARTS) => settle(self.points(), StatementKind::Points),
            _ => {
                self.unknown_statement();
                (None, false)
            }
        }
    }

    fn unknown_statement(&mut self) {
        let first = self.take();
        let mut end = first.span.end;
        while !self.boundary(end) {
            end = self.take().span.end;
        }
        self.issue(
            C_UNKNOWN,
            format!("unknown statement {}", first.text),
            Span {
                start: first.span.start,
                end,
            },
        );
    }

    fn accessibility(&mut self) -> Option<Accessibility<'a>> {
        let keyword = self.take();
        let expected = if keyword.kind == "acc_title" {
            "acc_title_value"
        } else {
            "acc_descr_value"
        };
        if self.kind() != expected {
            self.unexpected(&[expected]);
            return None;
        }
        let value = self.take();
        Some(Accessibility {
            span: Span {
                start: keyword.span.start,
                end: value.span.end,
            },
            title: keyword.kind == "acc_title",
            multiline: false,
            value,
        })
    }

    fn title(&mut self) -> Option<Title<'a>> {
        let keyword = self.take();
        if self.kind() != "title_value" {
            self.unexpected(&["title_value"]);
            return None;
        }
        let value = self.take();
        Some(Title {
            span: Span {
                start: keyword.span.start,
                end: value.span.end,
            },
            value,
        })
    }

    fn text(&mut self, expected: &[&str]) -> Option<Text> {
        if !self.is(TEXT_STARTS) {
            self.unexpected(expected);
            return None;
        }
        let first = self.take();
        let mut value = first.text.to_owned();
        let mut end = first.span.end;
        let mut content_end = first.content.end;
        while self.is(TEXT_TAIL_TOKENS) {
            let token = self.take();
            value.push_str(token.text);
            end = token.span.end;
            content_end = token.span.end;
        }
        Some(Text {
            span: Span {
                start: first.span.start,
                end,
            },
            content: Span {
                start: first.content.start,
                end: content_end,
            },
            value,
            markdown: first.kind == "MD_STR",
        })
    }

    fn axis(&mut self) -> Option<AxisDetails<'a>> {
        let keyword = self.take();
        let first = self.text(TEXT_STARTS)?;
        let mut axis = AxisDetails {
            span: Span {
                start: keyword.span.start,
                end: first.span.end,
            },
            y: keyword.kind == "Y-AXIS",
            first,
            delimiter: None,
            second: None,
        };
        if self.kind() != "AXIS-TEXT-DELIMITER" {
            return Some(axis);
        }
        let delimiter = self.take();
        axis.span.end = delimiter.span.end;
        axis.delimiter = Some(delimiter);
        if !self.is(TEXT_STARTS) {
            return Some(axis);
        }
        let second = self.text(TEXT_STARTS)?;
        axis.span.end = second.span.end;
        axis.second = Some(second);
        Some(axis)
    }

    fn quadrant_details(&mut self) -> Option<QuadrantDetails> {
        let keyword = self.take();
        let text = self.text(TEXT_STARTS)?;
        let number = keyword
            .kind
            .bytes()
            .last()
            .map_or(0, |digit| usize::from(digit - b'0'));
        Some(QuadrantDetails {
            span: Span {
                start: keyword.span.start,
                end: text.span.end,
            },
            number,
            text,
        })
    }

    fn class_def(&mut self) -> Option<ClassDefStatement> {
        let keyword = self.take();
        if self.kind() != "SPACE" {
            self.unexpected(&["SPACE"]);
            return None;
        }
        self.take();
        let name = self.id_string()?;
        if self.kind() != "SPACE" {
            let mut expected = ID_STRING_TOKENS.to_vec();
            expected.push("SPACE");
            self.unexpected(&expected);
            return None;
        }
        self.take();
        let styles = self.styles_opt()?;
        Some(ClassDefStatement {
            span: Span {
                start: keyword.span.start,
                end: styles.span.end,
            },
            name,
            styles,
        })
    }

    fn id_string(&mut self) -> Option<IdString> {
        if !self.is(ID_STRING_TOKENS) {
            self.unexpected(ID_STRING_TOKENS);
            return None;
        }
        let first = self.token();
        let mut text = String::new();
        let mut end = first.span.end;
        while self.is(ID_STRING_TOKENS) {
            let token = self.take();
            text.push_str(token.text);
            end = token.span.end;
        }
        Some(IdString {
            span: Span {
                start: first.span.start,
                end,
            },
            text,
        })
    }

    fn styles_opt(&mut self) -> Option<StylesOpt> {
        let first = self.token().span.start;
        let mut opt = StylesOpt {
            span: Span {
                start: first,
                end: first,
            },
            styles: Vec::new(),
        };
        loop {
            let style = self.style()?;
            opt.span.end = style.span.end;
            opt.styles.push(style);
            if self.kind() != "COMMA" {
                return Some(opt);
            }
            self.take();
        }
    }

    fn style(&mut self) -> Option<Style> {
        if !self.is(STYLE_COMPONENTS) {
            self.unexpected(STYLE_COMPONENTS);
            return None;
        }
        let first = self.token();
        let mut text = String::new();
        let mut end = first.span.end;
        while self.is(STYLE_COMPONENTS) {
            let token = self.take();
            text.push_str(token.text);
            end = token.span.end;
        }
        Some(Style {
            span: Span {
                start: first.span.start,
                end,
            },
            text,
        })
    }

    fn points(&mut self) -> Option<Points<'a>> {
        let text = self.text(TEXT_STARTS)?;
        let class = (self.kind() == "class_name").then(|| self.take());
        if self.kind() != "point_start" {
            let mut expected = vec!["point_start"];
            if class.is_none() {
                expected.push("class_name");
                expected.extend_from_slice(TEXT_TAIL_TOKENS);
            }
            self.unexpected(&expected);
            return None;
        }
        self.take();
        if self.kind() != "point_x" {
            self.unexpected(&["point_x"]);
            return None;
        }
        let point_x = self.take();
        if self.kind() != "point_y" {
            self.unexpected(&["point_y"]);
            return None;
        }
        let point_y = self.take();
        let mut point = Points {
            span: Span {
                start: text.span.start,
                end: point_y.span.end,
            },
            text,
            class,
            point_x,
            point_y,
            styles: None,
        };
        if self.is(STYLE_COMPONENTS) {
            let styles = self.styles_opt()?;
            point.span.end = styles.span.end;
            point.styles = Some(styles);
        }
        Some(point)
    }
}
