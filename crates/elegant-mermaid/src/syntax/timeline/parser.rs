//! Recursive-descent parser for the timeline grammar (`spec/grammar/timeline.md`).

use crate::diag::Diagnostic;
use crate::source::Span;

use super::ast::{
    AccDescr, AccDescrBlock, AccTitle, Document, EventStatement, Line, PeriodStatement, Section,
    Start, Statement, StatementKind, TimelineHeader, Title,
};
use super::lexer::{
    ACC_BLOCK_VALUE, ACC_DESCR, ACC_DESCR_VALUE, ACC_TITLE, ACC_TITLE_VALUE, EOF, EVENT, NEWLINE,
    PERIOD, SECTION, Scanner, TIMELINE, TIMELINE_LR, TIMELINE_TD, TITLE, Token, UNTERMINATED,
};
use super::{C_UNEXPECTED, C_UNKNOWN, C_UNTERMINATED, diagnostic};

pub struct Parsed {
    pub document: Start,
    pub diagnostics: Vec<Diagnostic>,
}

const HEADER_TOKENS: &[&str] = &[TIMELINE, TIMELINE_LR, TIMELINE_TD];

pub fn parse(source: &str, removed: &[Span]) -> Parsed {
    let mut parser = Parser {
        source,
        scan: Scanner::new(source, removed),
        tok: Token::empty(),
        diagnostics: Vec::new(),
    };
    parser.advance();
    let document = parser.start();
    Parsed {
        document,
        diagnostics: parser.diagnostics,
    }
}

struct Parser<'a> {
    source: &'a str,
    scan: Scanner,
    tok: Token,
    diagnostics: Vec<Diagnostic>,
}

fn direction(kind: &str) -> &'static str {
    match kind {
        TIMELINE_LR => "LR",
        TIMELINE_TD => "TD",
        _ => "",
    }
}

impl Parser<'_> {
    fn advance(&mut self) {
        self.tok = self.scan.next();
    }

    fn take(&mut self) -> Token {
        let next = self.scan.next();
        std::mem::replace(&mut self.tok, next)
    }

    fn describe(&self, token: &Token) -> String {
        if token.span.start == token.span.end {
            return "end of input".into();
        }
        self.source
            .get(token.span.start..token.span.end)
            .unwrap_or("")
            .to_owned()
    }

    fn unexpected(&mut self, expected: &[&str]) {
        let mut names = expected.to_vec();
        names.sort_unstable();
        let message = format!(
            "unexpected {}, expected one of: {}",
            self.describe(&self.tok),
            names.join(", ")
        );
        self.diagnostics
            .push(diagnostic(C_UNEXPECTED, message, self.tok.span));
    }

    fn start(&mut self) -> Start {
        while self.tok.kind == NEWLINE {
            self.advance();
        }
        if !HEADER_TOKENS.contains(&self.tok.kind) {
            self.unexpected(HEADER_TOKENS);
            return Start {
                span: Span {
                    start: self.tok.span.start,
                    end: self.source.len(),
                },
                header: TimelineHeader {
                    token: Token::empty(),
                    direction: "",
                },
                document: Document {
                    span: Span { start: 0, end: 0 },
                    lines: Vec::new(),
                },
            };
        }
        let token = self.take();
        let document = self.document();
        Start {
            span: Span {
                start: token.span.start,
                end: document.span.end.max(token.span.end),
            },
            header: TimelineHeader {
                direction: direction(token.kind),
                token,
            },
            document,
        }
    }

    fn document(&mut self) -> Document {
        let begin = self.tok.span.start;
        let mut document = Document {
            span: Span {
                start: begin,
                end: begin,
            },
            lines: Vec::new(),
        };
        while self.tok.kind != EOF {
            if let Some(line) = self.line() {
                document.span.end = document.span.end.max(line.span.end);
                document.lines.push(line);
            }
        }
        document
    }

    fn line(&mut self) -> Option<Line> {
        match self.tok.kind {
            NEWLINE => {
                let separator = self.take();
                Some(Line {
                    span: separator.span,
                    separator: Some(separator),
                    statement: None,
                })
            }
            UNTERMINATED => {
                let t = self.take();
                let message = format!("unterminated {}", t.text);
                self.diagnostics
                    .push(diagnostic(C_UNTERMINATED, message, t.span));
                None
            }
            _ => {
                let statement = self.statement()?;
                Some(Line {
                    span: statement.span,
                    separator: None,
                    statement: Some(statement),
                })
            }
        }
    }

    fn statement(&mut self) -> Option<Statement> {
        let kind = self.tok.kind;
        match kind {
            TITLE | SECTION | PERIOD | EVENT => {
                let token = self.take();
                let span = token.span;
                let node = match kind {
                    TITLE => StatementKind::Title(Title { token }),
                    SECTION => StatementKind::Section(Section { token }),
                    PERIOD => StatementKind::Period(PeriodStatement { token }),
                    _ => StatementKind::Event(EventStatement { token }),
                };
                Some(Statement { span, kind: node })
            }
            ACC_BLOCK_VALUE => {
                let value = self.take();
                let span = Span {
                    start: value.open.start,
                    end: value.close.end,
                };
                Some(Statement {
                    span,
                    kind: StatementKind::AccDescrBlock(AccDescrBlock { value }),
                })
            }
            ACC_TITLE => self.accessibility(ACC_TITLE_VALUE, |opener, value| {
                StatementKind::AccTitle(AccTitle { opener, value })
            }),
            ACC_DESCR => self.accessibility(ACC_DESCR_VALUE, |opener, value| {
                StatementKind::AccDescr(AccDescr { opener, value })
            }),
            _ => {
                self.unknown();
                None
            }
        }
    }

    fn accessibility(
        &mut self,
        value: &'static str,
        build: impl FnOnce(Token, Token) -> StatementKind,
    ) -> Option<Statement> {
        let opener = self.take();
        if self.tok.kind != value {
            self.unexpected(&[value]);
            return None;
        }
        let v = self.take();
        let span = Span {
            start: opener.span.start,
            end: opener.span.end.max(v.span.end),
        };
        Some(Statement {
            span,
            kind: build(opener, v),
        })
    }

    fn unknown(&mut self) {
        let first = self.tok.clone();
        let end = self.scan.skip_line(first.span.end);
        self.advance();
        let message = format!("unknown statement {}", self.describe(&first));
        self.diagnostics.push(diagnostic(
            C_UNKNOWN,
            message,
            Span {
                start: first.span.start,
                end,
            },
        ));
    }
}
