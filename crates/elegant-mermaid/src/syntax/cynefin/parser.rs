//! Recursive-descent parser for the cynefin grammar (`spec/grammar/cynefin.md`).

use crate::diag::Diagnostic;
use crate::source::Span;
use crate::syntax::langium::{
    self, Codes, Cursor, EOF, Field, Grammar, Keyword, NEWLINE, STRING, Terminal, Token,
    UNTERMINATED,
};

use super::ast::{Cynefin, DomainBlock, DomainItem, Transition, Value};
use super::{C_UNEXPECTED, C_UNKNOWN, C_UNTERMINATED, DOMAIN_NAMES};

const HEADER: &str = "cynefin-beta";
const HEADER_COLON: &str = "cynefin-beta:";
const ARROW: &str = "-->";
const COLON: &str = ":";
const DOMAIN_NAME: &str = "DOMAIN_NAME";
const HEADER_KINDS: [&str; 2] = [HEADER, HEADER_COLON];

const GRAMMAR: Grammar = Grammar {
    keywords: &[
        Keyword {
            text: HEADER_COLON,
            guard: false,
        },
        Keyword {
            text: HEADER,
            guard: true,
        },
        Keyword {
            text: ARROW,
            guard: false,
        },
        Keyword {
            text: COLON,
            guard: false,
        },
    ],
    locals: &[Terminal {
        kind: DOMAIN_NAME,
        matcher: domain_length,
    }],
};

fn domain_length(rest: &str) -> usize {
    DOMAIN_NAMES
        .iter()
        .find(|name| rest.starts_with(**name))
        .map_or(0, |name| name.len())
}

pub struct Parsed {
    pub document: Cynefin,
    pub diagnostics: Vec<Diagnostic>,
}

pub fn parse(source: &str, removed: &[Span]) -> Parsed {
    let codes = Codes {
        unexpected: C_UNEXPECTED,
        unknown: C_UNKNOWN,
        unterminated: C_UNTERMINATED,
    };
    let mut parser = Parser {
        cur: Cursor::new(source, removed, GRAMMAR, codes),
    };
    parser.cur.skip_newlines();
    let header = parser.header();
    parser.cur.skip_newlines();
    let mut document = Cynefin {
        span: Span {
            start: header.span.start,
            end: source.len(),
        },
        header,
        domains: Vec::new(),
        transitions: Vec::new(),
        title: None,
        acc_title: None,
        acc_descr: None,
    };
    parser.body(&mut document);
    Parsed {
        document,
        diagnostics: parser.cur.diags,
    }
}

struct Parser<'a> {
    cur: Cursor<'a>,
}

impl Parser<'_> {
    fn header(&mut self) -> Token {
        if HEADER_KINDS.contains(&self.cur.kind()) {
            return self.cur.take();
        }
        self.cur.unexpected(&HEADER_KINDS);
        self.cur.skip_line();
        Token {
            kind: "",
            text: String::new(),
            span: Span { start: 0, end: 0 },
        }
    }

    fn body(&mut self, doc: &mut Cynefin) {
        loop {
            match self.cur.kind() {
                EOF => return,
                UNTERMINATED => {
                    self.cur.unterminated();
                    return;
                }
                NEWLINE => {
                    self.cur.take();
                }
                DOMAIN_NAME if self.cur.kind_ahead(1) == ARROW => self.transition(doc),
                DOMAIN_NAME => self.domain(doc),
                kind if langium::is_metadata(kind) => self.metadata(doc),
                _ => self.cur.unknown(),
            }
        }
    }

    fn domain(&mut self, doc: &mut Cynefin) {
        let domain = self.cur.take();
        let mut end = domain.span.end;
        let mut items = Vec::new();
        loop {
            self.cur.skip_newlines();
            if self.cur.kind() != STRING {
                break;
            }
            let token = self.cur.take();
            end = token.span.end;
            items.push(DomainItem {
                span: token.span,
                label: Value {
                    text: token.text,
                    span: token.span,
                },
            });
        }
        doc.domains.push(DomainBlock {
            span: Span {
                start: domain.span.start,
                end,
            },
            domain,
            items,
        });
    }

    fn transition(&mut self, doc: &mut Cynefin) {
        let from = self.cur.take();
        self.cur.take();
        if self.cur.kind() != DOMAIN_NAME {
            self.cur.unexpected(&[DOMAIN_NAME]);
            self.cur.skip_line();
            return;
        }
        let to = self.cur.take();
        let mut expected: &[&str] = &[COLON];
        let mut label = None;
        if self.cur.kind() == COLON {
            self.cur.take();
            if self.cur.kind() != STRING {
                self.cur.unexpected(&[STRING]);
                self.cur.skip_line();
                return;
            }
            let token = self.cur.take();
            label = Some(Value {
                text: token.text,
                span: token.span,
            });
            expected = &[];
        }
        if !self.cur.finish(expected) {
            return;
        }
        doc.transitions.push(Transition {
            span: Span {
                start: from.span.start,
                end: self.cur.end,
            },
            from,
            to,
            label,
        });
    }

    fn metadata(&mut self, doc: &mut Cynefin) {
        let Some((field, token)) = self.cur.metadata() else {
            return;
        };
        let value = Some(Value {
            text: token.text,
            span: token.span,
        });
        match field {
            Field::AccDescr => doc.acc_descr = value,
            Field::AccTitle => doc.acc_title = value,
            Field::Title => doc.title = value,
        }
    }
}
