use super::ast::{
    AbnfAlternation, AbnfConcatenation, AbnfElement, AbnfGroup, AbnfNumVal, AbnfOptionalGroup,
    AbnfPrimary, AbnfRuleName, AbnfStringLiteral, Token, Value,
};
use super::parser::Parser;
use super::text::strip_quotes;

fn abnf_element_start(kind: &str) -> bool {
    matches!(
        kind,
        "REPEAT" | "EXACT_REPEAT" | "STRING" | "NUMVAL" | "ID" | "(" | "["
    )
}

impl Parser<'_> {
    pub(super) fn abnf_alternation(&mut self) -> Option<AbnfAlternation> {
        let start = self.tok().span.start;
        let mut alternatives = Vec::new();
        loop {
            alternatives.push(self.abnf_concatenation()?);
            if self.kind() != "/" {
                break;
            }
            self.take();
        }
        Some(AbnfAlternation {
            span: self.since(start),
            alternatives,
        })
    }

    fn abnf_concatenation(&mut self) -> Option<AbnfConcatenation> {
        let start = self.tok().span.start;
        let mut elements = Vec::new();
        loop {
            elements.push(self.abnf_element()?);
            if !abnf_element_start(self.kind()) {
                break;
            }
        }
        Some(AbnfConcatenation {
            span: self.since(start),
            elements,
        })
    }

    fn abnf_element(&mut self) -> Option<AbnfElement> {
        let start = self.tok().span.start;
        let mut repeat = None;
        if matches!(self.kind(), "REPEAT" | "EXACT_REPEAT") {
            let token = self.tok().clone();
            if !self.enter(&token) {
                return None;
            }
            self.take();
            repeat = Some(token);
        }
        let primary = self.abnf_primary();
        if repeat.is_some() {
            self.depth -= 1;
        }
        let primary = primary?;
        Some(AbnfElement {
            span: self.since(start),
            repeat,
            primary,
        })
    }

    fn abnf_primary(&mut self) -> Option<AbnfPrimary> {
        let token = self.tok().clone();
        match token.kind.as_str() {
            "STRING" => {
                self.take();
                Some(AbnfPrimary::StringLiteral(AbnfStringLiteral {
                    span: token.span,
                    value: Value {
                        span: token.span,
                        text: strip_quotes(&token.text).to_owned(),
                    },
                }))
            }
            "NUMVAL" => {
                self.take();
                Some(AbnfPrimary::NumVal(AbnfNumVal {
                    span: token.span,
                    value: Value {
                        span: token.span,
                        text: token.text,
                    },
                }))
            }
            "ID" => {
                self.take();
                Some(AbnfPrimary::RuleName(AbnfRuleName {
                    span: token.span,
                    name: Value {
                        span: token.span,
                        text: token.text,
                    },
                }))
            }
            "(" | "[" => self.abnf_group(&token),
            _ => {
                self.fail(&["(", "STRING", "NUMVAL", "ID", "["]);
                None
            }
        }
    }

    fn abnf_group(&mut self, open: &Token) -> Option<AbnfPrimary> {
        if !self.enter(open) {
            return None;
        }
        self.take();
        let element = self.abnf_alternation()?;
        let closer = if open.kind == "[" { "]" } else { ")" };
        self.expect(closer, &[])?;
        self.depth -= 1;
        let span = self.since(open.span.start);
        Some(if open.kind == "(" {
            AbnfPrimary::Group(AbnfGroup { span, element })
        } else {
            AbnfPrimary::OptionalGroup(AbnfOptionalGroup { span, element })
        })
    }
}
