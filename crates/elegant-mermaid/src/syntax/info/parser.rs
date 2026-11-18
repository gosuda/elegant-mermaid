//! Recursive-descent parser for the info grammar (`spec/grammar/info.md`).

use crate::diag::Diagnostic;
use crate::source::Span;
use crate::syntax::langium::{
    self, ACC_DESCR, ACC_TITLE, Codes, Cursor, EOF, Field, Grammar, Keyword, NEWLINE, TITLE, Token,
    UNTERMINATED,
};

use super::ast::{Info, Value};
use super::{C_UNEXPECTED, C_UNKNOWN, C_UNTERMINATED};

const HEADER: &str = "info";
const SHOW_INFO: &str = "showInfo";
const AFTER_SHOW_INFO: [&str; 4] = [ACC_DESCR, ACC_TITLE, EOF, TITLE];

const GRAMMAR: Grammar = Grammar {
    keywords: &[
        Keyword {
            text: SHOW_INFO,
            guard: true,
        },
        Keyword {
            text: HEADER,
            guard: true,
        },
    ],
    locals: &[],
};

pub struct Parsed {
    pub document: Info,
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
        fragment: false,
    };
    parser.cur.skip_newlines();
    let header = parser.header();
    parser.cur.skip_newlines();
    let mut document = Info {
        span: Span {
            start: header.span.start,
            end: source.len(),
        },
        header,
        show_info: None,
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
    fragment: bool,
}

impl Parser<'_> {
    fn header(&mut self) -> Token {
        if self.cur.kind() == HEADER {
            return self.cur.take();
        }
        self.cur.unexpected(&[HEADER]);
        self.cur.skip_line();
        Token {
            kind: "",
            text: String::new(),
            span: Span { start: 0, end: 0 },
        }
    }

    fn body(&mut self, doc: &mut Info) {
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
                SHOW_INFO => self.show_info(doc),
                kind if langium::is_metadata(kind) => self.metadata(doc),
                _ => self.cur.unknown(),
            }
        }
    }

    fn show_info(&mut self, doc: &mut Info) {
        if doc.show_info.is_some() || self.fragment {
            self.cur.unexpected(&AFTER_SHOW_INFO);
            self.cur.skip_line();
            return;
        }
        doc.show_info = Some(self.cur.take());
    }

    fn metadata(&mut self, doc: &mut Info) {
        self.fragment = true;
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
