//! Recursive-descent parser for the venn grammar (`spec/grammar/venn.md`).

use crate::diag::Diagnostic;
use crate::source::Span;

use super::ast::{
    Document, Identifier, IdentifierList, IndentedText, IndentedTextTail, Line, Number,
    OptNewlines, Set, Start, Statement, StatementKind, StyleField, StyleValue, StylesOpt, Text,
    Title, Union, ValueToken, ValueTokens,
};
use super::lexer::{Lexer, Token};
use super::{C_UNEXPECTED, C_UNKNOWN, C_UNTERMINATED, diagnostic};

const IDENTIFIER_KINDS: &[&str] = &["IDENTIFIER", "STRING"];
const TEXT_ID_KINDS: &[&str] = &["IDENTIFIER", "NUMERIC", "STRING"];
const LIST_FOLLOW_KINDS: &[&str] = &["COMMA", "IDENTIFIER", "NUMERIC", "STRING"];
const STYLE_KEY_KINDS: &[&str] = &["COMMA", "IDENTIFIER"];
const VALUE_KINDS: &[&str] = &["HEXCOLOR", "IDENTIFIER", "NUMERIC", "RGBACOLOR", "RGBCOLOR"];
const STYLE_VALUE_KINDS: &[&str] = &[
    "HEXCOLOR",
    "IDENTIFIER",
    "NUMERIC",
    "RGBACOLOR",
    "RGBCOLOR",
    "STRING",
];

pub struct Parsed {
    pub document: Start,
    pub diagnostics: Vec<Diagnostic>,
}

pub fn parse(source: &str, removed: &[Span]) -> Parsed {
    let mut lexer = Lexer::new(source, removed);
    let cur = lexer.next();
    let mut parser = Parser {
        source,
        lexer,
        cur,
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
    lexer: Lexer,
    cur: Token,
    diagnostics: Vec<Diagnostic>,
}

fn starts_statement(kind: &str) -> bool {
    matches!(
        kind,
        "TITLE" | "SET" | "UNION" | "TEXT" | "INDENT_TEXT" | "STYLE"
    )
}

fn statement_span(kind: &StatementKind) -> Span {
    match kind {
        StatementKind::Title(s) => s.span,
        StatementKind::Set(s) => s.span,
        StatementKind::Union(s) => s.span,
        StatementKind::Text(s) => s.span,
        StatementKind::IndentedText(s) => s.span,
        StatementKind::Style(s) => s.span,
    }
}

fn identifier_of(token: Token) -> Identifier {
    Identifier {
        span: token.span,
        kind: token.kind,
        text: token.text,
    }
}

impl Parser<'_> {
    fn kind(&self) -> &'static str {
        self.cur.kind
    }

    fn take(&mut self) -> Token {
        let next = if self.cur.kind == "EOF" {
            self.cur.clone()
        } else {
            self.lexer.next()
        };
        std::mem::replace(&mut self.cur, next)
    }

    fn raw(&self, span: Span) -> &str {
        self.source.get(span.start..span.end).unwrap_or("")
    }

    fn issue(&mut self, code: &'static str, message: String, span: Span) {
        self.diagnostics.push(diagnostic(code, message, span));
    }

    fn unexpected(&mut self, expected: &[&str]) {
        if self.kind() == "UNTERMINATED" {
            self.unterminated();
            return;
        }
        let mut names = expected.to_vec();
        names.sort_unstable();
        let found = if self.kind() == "EOF" {
            "end of input"
        } else {
            self.raw(self.cur.span)
        };
        let message = format!("unexpected {found}, expected one of: {}", names.join(", "));
        let span = self.cur.span;
        self.issue(C_UNEXPECTED, message, span);
        self.recover();
    }

    fn unterminated(&mut self) {
        let token = self.take();
        self.issue(
            C_UNTERMINATED,
            format!("unterminated {}", token.text),
            token.span,
        );
    }

    fn at_boundary(&self) -> bool {
        matches!(self.kind(), "NEWLINE" | "EOF" | "UNTERMINATED")
    }

    fn recover(&mut self) {
        while !self.at_boundary() {
            self.take();
        }
    }

    fn start(&mut self) -> Start {
        let first = self.cur.span.start;
        let mut leading = OptNewlines {
            span: Span {
                start: first,
                end: 0,
            },
            newlines: Vec::new(),
        };
        while self.kind() == "NEWLINE" {
            let token = self.take();
            leading.span.end = token.span.end;
            leading.newlines.push(token);
        }
        let header = if self.kind() == "VENN" {
            Some(self.take())
        } else {
            self.unexpected(&["VENN"]);
            None
        };
        let document = self.document();
        Start {
            span: Span {
                start: first,
                end: self.source.len(),
            },
            leading,
            header,
            document,
        }
    }

    fn document(&mut self) -> Document {
        let start = self.cur.span.start;
        let mut document = Document {
            span: Span { start, end: start },
            lines: Vec::new(),
        };
        while self.kind() != "EOF" {
            if let Some(line) = self.line() {
                document.span.end = document.span.end.max(line.span.end);
                document.lines.push(line);
            }
        }
        document
    }

    fn line(&mut self) -> Option<Line> {
        match self.kind() {
            "NEWLINE" => {
                let token = self.take();
                return Some(Line {
                    span: token.span,
                    newline: Some(token),
                    statement: None,
                });
            }
            "UNTERMINATED" => {
                self.unterminated();
                return None;
            }
            kind if !starts_statement(kind) => {
                self.unknown_statement();
                return None;
            }
            _ => {}
        }
        let kind = self.statement()?;
        let span = statement_span(&kind);
        Some(Line {
            span,
            newline: None,
            statement: Some(Statement { span, kind }),
        })
    }

    fn unknown_statement(&mut self) {
        let first = self.take();
        let mut end = first.span.end;
        while !self.at_boundary() {
            end = self.take().span.end;
        }
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

    fn statement(&mut self) -> Option<StatementKind> {
        match self.kind() {
            "TITLE" => {
                let token = self.take();
                Some(StatementKind::Title(Title {
                    span: token.span,
                    token,
                }))
            }
            "SET" => self.set().map(StatementKind::Set),
            "UNION" => self.union().map(StatementKind::Union),
            "TEXT" => self.text().map(StatementKind::Text),
            "INDENT_TEXT" => self.indented_text().map(StatementKind::IndentedText),
            _ => self.style().map(StatementKind::Style),
        }
    }

    fn identifier(&mut self, expected: &[&str]) -> Option<Identifier> {
        if !expected.contains(&self.kind()) {
            self.unexpected(expected);
            return None;
        }
        Some(identifier_of(self.take()))
    }

    fn identifier_list(&mut self) -> Option<IdentifierList> {
        let first = self.identifier(IDENTIFIER_KINDS)?;
        let mut list = IdentifierList {
            span: first.span,
            ids: vec![first],
        };
        while self.kind() == "COMMA" {
            self.take();
            let next = self.identifier(IDENTIFIER_KINDS)?;
            list.span.end = next.span.end;
            list.ids.push(next);
        }
        Some(list)
    }

    fn optional_label(&mut self) -> Option<Token> {
        (self.kind() == "BRACKET_LABEL").then(|| self.take())
    }

    fn optional_size(&mut self) -> Result<Option<Number>, ()> {
        if self.kind() != "COLON" {
            return Ok(None);
        }
        self.take();
        if self.kind() != "NUMERIC" {
            self.unexpected(&["NUMERIC"]);
            return Err(());
        }
        let token = self.take();
        Ok(Some(Number {
            span: token.span,
            text: token.text,
        }))
    }

    fn set(&mut self) -> Option<Set> {
        let keyword = self.take();
        let id = self.identifier(IDENTIFIER_KINDS)?;
        let mut span = Span {
            start: keyword.span.start,
            end: id.span.end,
        };
        let label = self.optional_label();
        if let Some(label) = &label {
            span.end = label.span.end;
        }
        let size = self.optional_size().ok()?;
        if let Some(size) = &size {
            span.end = size.span.end;
        }
        self.lexer.indent = true;
        Some(Set {
            span,
            keyword,
            id,
            label,
            size,
        })
    }

    fn union(&mut self) -> Option<Union> {
        let keyword = self.take();
        let ids = self.identifier_list()?;
        let mut span = Span {
            start: keyword.span.start,
            end: ids.span.end,
        };
        let label = self.optional_label();
        if let Some(label) = &label {
            span.end = label.span.end;
        }
        let size = self.optional_size().ok()?;
        if let Some(size) = &size {
            span.end = size.span.end;
        }
        self.lexer.indent = true;
        Some(Union {
            span,
            keyword,
            ids,
            label,
            size,
        })
    }

    fn text_id(&mut self) -> Option<Identifier> {
        if !TEXT_ID_KINDS.contains(&self.kind()) {
            self.unexpected(LIST_FOLLOW_KINDS);
            return None;
        }
        Some(identifier_of(self.take()))
    }

    fn text(&mut self) -> Option<Text> {
        let keyword = self.take();
        let targets = self.identifier_list()?;
        let id = self.text_id()?;
        let mut span = Span {
            start: keyword.span.start,
            end: id.span.end,
        };
        let label = if id.kind == "NUMERIC" {
            None
        } else {
            self.optional_label()
        };
        if let Some(label) = &label {
            span.end = label.span.end;
        }
        Some(Text {
            span,
            keyword,
            targets,
            id,
            label,
        })
    }

    fn indented_text(&mut self) -> Option<IndentedText> {
        let keyword = self.take();
        if !TEXT_ID_KINDS.contains(&self.kind()) {
            self.unexpected(TEXT_ID_KINDS);
            return None;
        }
        let id = identifier_of(self.take());
        let mut tail = IndentedTextTail {
            span: id.span,
            label: None,
            id,
        };
        if tail.id.kind != "NUMERIC" {
            tail.label = self.optional_label();
        }
        if let Some(label) = &tail.label {
            tail.span.end = label.span.end;
        }
        Some(IndentedText {
            span: Span {
                start: keyword.span.start,
                end: tail.span.end,
            },
            keyword,
            tail,
        })
    }

    fn style(&mut self) -> Option<super::ast::Style> {
        let keyword = self.take();
        let targets = self.identifier_list()?;
        if self.kind() != "IDENTIFIER" {
            self.unexpected(STYLE_KEY_KINDS);
            return None;
        }
        let styles = self.styles_opt()?;
        Some(super::ast::Style {
            span: Span {
                start: keyword.span.start,
                end: styles.span.end,
            },
            keyword,
            targets,
            styles,
        })
    }

    fn styles_opt(&mut self) -> Option<StylesOpt> {
        let mut out = StylesOpt {
            span: Span {
                start: self.cur.span.start,
                end: self.cur.span.start,
            },
            fields: Vec::new(),
        };
        loop {
            let field = self.style_field()?;
            out.span.end = field.span.end;
            out.fields.push(field);
            if self.kind() != "COMMA" {
                return Some(out);
            }
            self.take();
            if self.kind() != "IDENTIFIER" {
                self.unexpected(&["IDENTIFIER"]);
                return None;
            }
        }
    }

    fn style_field(&mut self) -> Option<StyleField> {
        let key = self.take();
        if self.kind() != "COLON" {
            self.unexpected(&["COLON"]);
            return None;
        }
        self.take();
        let value = self.style_value()?;
        Some(StyleField {
            span: Span {
                start: key.span.start,
                end: value.span.end,
            },
            key,
            value,
        })
    }

    fn style_value(&mut self) -> Option<StyleValue> {
        if self.kind() == "STRING" {
            let token = self.take();
            return Some(StyleValue {
                span: token.span,
                string: Some(token),
                tokens: None,
            });
        }
        if VALUE_KINDS.contains(&self.kind()) {
            let tokens = self.value_tokens();
            return Some(StyleValue {
                span: tokens.span,
                string: None,
                tokens: Some(tokens),
            });
        }
        self.unexpected(STYLE_VALUE_KINDS);
        None
    }

    fn value_tokens(&mut self) -> ValueTokens {
        let start = self.cur.span.start;
        let mut out = ValueTokens {
            span: Span { start, end: start },
            tokens: Vec::new(),
        };
        while VALUE_KINDS.contains(&self.kind()) {
            let token = self.take();
            out.span.end = token.span.end;
            out.tokens.push(ValueToken {
                span: token.span,
                kind: token.kind,
                text: token.text,
            });
        }
        out
    }
}
