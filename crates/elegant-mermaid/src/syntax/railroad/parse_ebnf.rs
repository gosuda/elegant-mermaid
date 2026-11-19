use super::ast::{
    EbnfChoice, EbnfExceptionPostfix, EbnfGroup, EbnfNonTerminal, EbnfOneOrMorePostfix,
    EbnfOptional, EbnfOptionalPostfix, EbnfPostfix, EbnfPrimary, EbnfRepetition, EbnfSequence,
    EbnfSpecial, EbnfTerm, EbnfTerminal, EbnfZeroOrMorePostfix, Token, Value,
};
use super::parser::Parser;
use super::text::{decode_escapes, trim_js};

const EBNF_STARTS: [&str; 6] = ["(", "ID", "SPECIAL", "STRING", "[", "{"];

fn ebnf_primary_start(kind: &str) -> bool {
    matches!(kind, "STRING" | "SPECIAL" | "ID" | "(" | "[" | "{")
}

fn ebnf_closer(open: &str) -> &'static str {
    match open {
        "(" => ")",
        "[" => "]",
        _ => "}",
    }
}

impl Parser<'_> {
    pub(super) fn ebnf_choice(&mut self) -> Option<EbnfChoice> {
        let start = self.tok().span.start;
        let mut alternatives = Vec::new();
        loop {
            alternatives.push(self.ebnf_sequence()?);
            if self.kind() != "|" {
                break;
            }
            self.take();
        }
        Some(EbnfChoice {
            span: self.since(start),
            alternatives,
        })
    }

    fn ebnf_sequence(&mut self) -> Option<EbnfSequence> {
        let start = self.tok().span.start;
        let mut elements = Vec::new();
        loop {
            elements.push(self.ebnf_term()?);
            if self.kind() == "," {
                self.take();
                continue;
            }
            if !ebnf_primary_start(self.kind()) {
                break;
            }
        }
        Some(EbnfSequence {
            span: self.since(start),
            elements,
        })
    }

    fn ebnf_term(&mut self) -> Option<EbnfTerm> {
        let start = self.tok().span.start;
        let base = self.ebnf_primary()?;
        let mut postfixes = Vec::new();
        let mut levels = 0;
        while let Some(postfix) = self.ebnf_postfix(&mut levels)? {
            postfixes.push(postfix);
        }
        self.depth -= levels;
        Some(EbnfTerm {
            span: self.since(start),
            base,
            postfixes,
        })
    }

    fn ebnf_postfix(&mut self, levels: &mut i64) -> Option<Option<EbnfPostfix>> {
        let token = self.tok().clone();
        if !matches!(token.kind.as_str(), "?" | "*" | "+" | "-") {
            return Some(None);
        }
        if !self.enter(&token) {
            return None;
        }
        *levels += 1;
        self.take();
        let span = token.span;
        let postfix = match token.kind.as_str() {
            "?" => EbnfPostfix::Optional(EbnfOptionalPostfix { span }),
            "*" => EbnfPostfix::ZeroOrMore(EbnfZeroOrMorePostfix { span }),
            "+" => EbnfPostfix::OneOrMore(EbnfOneOrMorePostfix { span }),
            _ => {
                let except = self.ebnf_primary()?;
                EbnfPostfix::Exception(EbnfExceptionPostfix {
                    span: self.since(token.span.start),
                    except,
                })
            }
        };
        Some(Some(postfix))
    }

    fn ebnf_primary(&mut self) -> Option<EbnfPrimary> {
        let token = self.tok().clone();
        match token.kind.as_str() {
            "STRING" => {
                self.take();
                Some(EbnfPrimary::Terminal(EbnfTerminal {
                    span: token.span,
                    value: Value {
                        span: token.span,
                        text: decode_escapes(&token.text),
                    },
                }))
            }
            "SPECIAL" => {
                self.take();
                let inner = token
                    .text
                    .get(1..token.text.len().saturating_sub(1))
                    .unwrap_or("");
                Some(EbnfPrimary::Special(EbnfSpecial {
                    span: token.span,
                    text: Value {
                        span: token.span,
                        text: trim_js(inner).to_owned(),
                    },
                }))
            }
            "ID" => {
                self.take();
                Some(EbnfPrimary::NonTerminal(EbnfNonTerminal {
                    span: token.span,
                    name: Value {
                        span: token.span,
                        text: token.text,
                    },
                }))
            }
            "(" | "[" | "{" => self.ebnf_group(&token),
            _ => {
                self.fail(&EBNF_STARTS);
                None
            }
        }
    }

    fn ebnf_group(&mut self, open: &Token) -> Option<EbnfPrimary> {
        if !self.enter(open) {
            return None;
        }
        self.take();
        let element = self.ebnf_choice()?;
        self.expect(ebnf_closer(&open.kind), &[])?;
        self.depth -= 1;
        let span = self.since(open.span.start);
        Some(match open.kind.as_str() {
            "(" => EbnfPrimary::Group(EbnfGroup { span, element }),
            "[" => EbnfPrimary::Optional(EbnfOptional { span, element }),
            _ => EbnfPrimary::Repetition(EbnfRepetition { span, element }),
        })
    }
}
