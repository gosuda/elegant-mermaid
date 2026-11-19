//! Recursive-descent parser for the gantt grammar (`spec/grammar/gantt.md`).

use crate::diag::Diagnostic;
use crate::source::Span;

use super::ast::{
    Accessibility, ClickStatement, ClickToken, Document, Line, Start, Statement, StatementKind,
    Task, Weekday, Weekend,
};
use super::lexer::{
    ACC_BLOCK_VALUE, ACC_DESCR, ACC_DESCR_VALUE, ACC_TITLE, ACC_TITLE_VALUE, AXIS_FORMAT,
    CALLBACK_ARGS, CALLBACK_NAME, CLICK, DATE_FORMAT, EOF, EXCLUDES, GANTT, HREF, INCLUDES,
    INCLUSIVE_END_DATES, NEWLINE, SECTION, Scanner, TASK_DATA, TASK_TEXT, TICK_INTERVAL, TITLE,
    TODAY_MARKER, TOP_AXIS, Token, UNTERMINATED, WEEKDAY_PREFIX, WEEKEND_PREFIX,
};
use super::{C_UNEXPECTED, C_UNKNOWN, C_UNTERMINATED, diagnostic};

pub struct Parsed {
    pub document: Start,
    pub diagnostics: Vec<Diagnostic>,
}

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

fn simple(kind: &str) -> Option<fn(Token) -> StatementKind> {
    Some(match kind {
        DATE_FORMAT => StatementKind::DateFormat,
        INCLUSIVE_END_DATES => StatementKind::InclusiveEndDates,
        TOP_AXIS => StatementKind::TopAxis,
        AXIS_FORMAT => StatementKind::AxisFormat,
        TICK_INTERVAL => StatementKind::TickInterval,
        EXCLUDES => StatementKind::Excludes,
        INCLUDES => StatementKind::Includes,
        TODAY_MARKER => StatementKind::TodayMarker,
        TITLE => StatementKind::Title,
        SECTION => StatementKind::Section,
        _ => return None,
    })
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
        if self.tok.kind == UNTERMINATED {
            return;
        }
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

    fn discard(&mut self) {
        if matches!(self.tok.kind, NEWLINE | EOF | UNTERMINATED) {
            return;
        }
        self.scan.skip_line(self.tok.span.end);
        self.advance();
    }

    fn start(&mut self) -> Start {
        while self.tok.kind == NEWLINE {
            self.advance();
        }
        if self.tok.kind != GANTT {
            self.unexpected(&[GANTT]);
            return Start {
                span: Span {
                    start: self.tok.span.start,
                    end: self.source.len(),
                },
                header: Token::empty(),
                document: Document {
                    span: Span { start: 0, end: 0 },
                    lines: Vec::new(),
                },
            };
        }
        let header = self.take();
        let document = self.document();
        Start {
            span: Span {
                start: header.span.start,
                end: document.span.end.max(header.span.end),
            },
            header,
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
        if let Some(name) = kind.strip_prefix(WEEKDAY_PREFIX) {
            let token = self.take();
            let span = token.span;
            return Some(Statement {
                span,
                kind: StatementKind::Weekday(Weekday { token, name }),
            });
        }
        if let Some(name) = kind.strip_prefix(WEEKEND_PREFIX) {
            let token = self.take();
            let span = token.span;
            return Some(Statement {
                span,
                kind: StatementKind::Weekend(Weekend { token, name }),
            });
        }
        match kind {
            ACC_BLOCK_VALUE => {
                let value = self.take();
                let span = Span {
                    start: value.open.start,
                    end: value.close.end,
                };
                Some(Statement {
                    span,
                    kind: StatementKind::AccDescrBlock(value),
                })
            }
            ACC_TITLE => self.accessibility(ACC_TITLE_VALUE, StatementKind::AccTitle),
            ACC_DESCR => self.accessibility(ACC_DESCR_VALUE, StatementKind::AccDescr),
            CLICK => self.click(),
            TASK_TEXT => self.task(),
            _ => self.simple_or_unknown(kind),
        }
    }

    fn simple_or_unknown(&mut self, kind: &'static str) -> Option<Statement> {
        match simple(kind) {
            Some(build) => {
                let taken = self.take();
                Some(Statement {
                    span: taken.span,
                    kind: build(taken),
                })
            }
            None => {
                self.unknown();
                None
            }
        }
    }

    fn accessibility(
        &mut self,
        value: &'static str,
        build: impl FnOnce(Accessibility) -> StatementKind,
    ) -> Option<Statement> {
        let opener = self.take();
        if self.tok.kind != value {
            self.unexpected(&[value]);
            self.discard();
            return None;
        }
        let v = self.take();
        let span = Span {
            start: opener.span.start,
            end: opener.span.end.max(v.span.end),
        };
        Some(Statement {
            span,
            kind: build(Accessibility { opener, value: v }),
        })
    }

    fn task(&mut self) -> Option<Statement> {
        let text = self.take();
        if self.tok.kind != TASK_DATA {
            self.unexpected(&[TASK_DATA]);
            self.discard();
            return None;
        }
        let data = self.take();
        Some(Statement {
            span: Span {
                start: text.span.start,
                end: data.span.end,
            },
            kind: StatementKind::Task(Task { text, data }),
        })
    }

    fn grab(
        &mut self,
        kind: &'static str,
        c: &mut ClickStatement,
        end: &mut usize,
    ) -> Option<ClickToken> {
        if self.tok.kind != kind {
            return None;
        }
        let t = self.take();
        c.order.push(kind);
        *end = (*end).max(t.span.end);
        Some(t.into())
    }

    fn click(&mut self) -> Option<Statement> {
        let click = self.take();
        let mut end = click.span.end;
        let start = click.span.start;
        let mut c = ClickStatement {
            click: click.into(),
            callback: None,
            args: None,
            href: None,
            order: Vec::new(),
        };
        match self.tok.kind {
            CALLBACK_NAME => {
                c.callback = self.grab(CALLBACK_NAME, &mut c, &mut end);
                c.args = self.grab(CALLBACK_ARGS, &mut c, &mut end);
                c.href = self.grab(HREF, &mut c, &mut end);
            }
            HREF => {
                c.href = self.grab(HREF, &mut c, &mut end);
                c.callback = self.grab(CALLBACK_NAME, &mut c, &mut end);
                if c.callback.is_some() {
                    c.args = self.grab(CALLBACK_ARGS, &mut c, &mut end);
                }
            }
            _ => {
                self.unexpected(&[CALLBACK_NAME, HREF]);
                self.discard();
                return None;
            }
        }
        Some(Statement {
            span: Span { start, end },
            kind: StatementKind::Click(c),
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
