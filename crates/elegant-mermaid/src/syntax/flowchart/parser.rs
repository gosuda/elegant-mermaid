use super::ast::*;
use super::lexer::lex_all;
use super::tokens::{TextVal, Token, TokenKind as K, is_alpha_num_token};
use crate::diag::{Diagnostic, Edit, Fix, FixSafety, Severity};
use crate::source::Span;

pub struct Parsed {
    pub document: Document,
    pub diagnostics: Vec<Diagnostic>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum EndState {
    Clean,
    Bracket,
    Unterminated,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum StatementEnd {
    Clean,
    Broken,
}

struct Parser<'a> {
    src: &'a str,
    tokens: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    end: EndState,
    depth: usize,
}

pub fn parse(src: &str, removed: &[Span]) -> Parsed {
    let lexed = lex_all(src, removed);
    let mut p = Parser {
        src,
        tokens: lexed.tokens,
        i: 0,
        diags: lexed.diagnostics,
        end: EndState::Clean,
        depth: 0,
    };
    let config = p.header();
    let lines = p.statements();
    let document = Document {
        span: Span {
            start: 0,
            end: src.len(),
        },
        config,
        lines,
    };
    p.finish_lexing(
        lexed.eof_shape,
        lexed.eof_acc,
        lexed.eof_label,
        lexed.eof_quote,
    );
    attach_fixes(src, &mut p.diags);
    crate::diag::sort(&mut p.diags);
    Parsed {
        document,
        diagnostics: p.diags,
    }
}

impl Parser<'_> {
    fn finish_lexing(
        &mut self,
        shape: Option<Span>,
        acc: Option<Span>,
        label: Option<Span>,
        quote: Option<usize>,
    ) {
        let src = self.src;
        let p = self;
        match p.end {
            EndState::Unterminated => {
                if let Some(span) = shape {
                    p.token_diag(
                        "flowchart/unterminated",
                        Span {
                            start: span.start,
                            end: src.len(),
                        },
                        "@{",
                    );
                }
                if let Some(span) = acc {
                    p.token_diag(
                        "flowchart/unterminated",
                        Span {
                            start: span.start,
                            end: src.len(),
                        },
                        "{",
                    );
                }
            }
            EndState::Bracket => {
                if let Some(span) = label {
                    p.token_diag(
                        "flowchart/unclosed-node-bracket",
                        Span {
                            start: span.start,
                            end: src.len(),
                        },
                        src.get(span.start..span.end).unwrap_or(""),
                    );
                }
            }
            EndState::Clean => {
                if let Some(start) = quote {
                    p.plain(
                        "flowchart/quote-unclosed",
                        Span {
                            start,
                            end: src.len(),
                        },
                    );
                }
            }
        }
    }
}

mod cursor;
mod diagnostics;
mod interaction;
mod links;
mod statements;
mod styles;
mod token_rules;
mod vertices;
use diagnostics::*;
use token_rules::*;
#[cfg(test)]
mod fix_tests;
