use super::ast::{
    PegAny, PegGroup, PegIdentifier, PegLiteral, PegOrderedChoice, PegPrefix, PegPrimary,
    PegSequence, PegSuffix, Token, Value,
};
use super::parser::Parser;
use super::text::decode_escapes;

fn peg_prefix_start(kind: &str) -> bool {
    matches!(kind, "&" | "!" | "STRING" | "ID" | "(" | ".")
}

impl Parser<'_> {
    pub(super) fn peg_choice(&mut self) -> Option<PegOrderedChoice> {
        let start = self.tok().span.start;
        let mut alternatives = Vec::new();
        loop {
            alternatives.push(self.peg_sequence()?);
            if self.kind() != "/" {
                break;
            }
            self.take();
        }
        Some(PegOrderedChoice {
            span: self.since(start),
            alternatives,
        })
    }

    fn peg_sequence(&mut self) -> Option<PegSequence> {
        let start = self.tok().span.start;
        let mut elements = Vec::new();
        loop {
            elements.push(self.peg_prefix()?);
            if !peg_prefix_start(self.kind()) {
                break;
            }
        }
        Some(PegSequence {
            span: self.since(start),
            elements,
        })
    }

    fn peg_prefix(&mut self) -> Option<PegPrefix> {
        let start = self.tok().span.start;
        let mut levels = 0;
        let mut operator = None;
        if matches!(self.kind(), "&" | "!") {
            let token = self.tok().clone();
            if !self.enter(&token) {
                return None;
            }
            levels += 1;
            self.take();
            operator = Some(token);
        }
        let suffix = self.peg_suffix(&mut levels)?;
        self.depth -= levels;
        Some(PegPrefix {
            span: self.since(start),
            operator,
            suffix,
        })
    }

    fn peg_suffix(&mut self, levels: &mut i64) -> Option<PegSuffix> {
        let start = self.tok().span.start;
        let primary = self.peg_primary()?;
        let mut operator = None;
        if matches!(self.kind(), "?" | "*" | "+") {
            let token = self.tok().clone();
            if !self.enter(&token) {
                return None;
            }
            *levels += 1;
            self.take();
            operator = Some(token);
        }
        Some(PegSuffix {
            span: self.since(start),
            primary,
            operator,
        })
    }

    fn peg_primary(&mut self) -> Option<PegPrimary> {
        let token = self.tok().clone();
        match token.kind.as_str() {
            "STRING" => {
                self.take();
                Some(PegPrimary::Literal(PegLiteral {
                    span: token.span,
                    value: Value {
                        span: token.span,
                        text: decode_escapes(&token.text),
                    },
                }))
            }
            "ID" => {
                self.take();
                Some(PegPrimary::Identifier(PegIdentifier {
                    span: token.span,
                    name: Value {
                        span: token.span,
                        text: token.text,
                    },
                }))
            }
            "." => {
                self.take();
                Some(PegPrimary::Any(PegAny { span: token.span }))
            }
            "(" => self.peg_group(&token),
            _ => {
                self.fail(&["(", "ID", "STRING", "."]);
                None
            }
        }
    }

    fn peg_group(&mut self, open: &Token) -> Option<PegPrimary> {
        if !self.enter(open) {
            return None;
        }
        self.take();
        let element = self.peg_choice()?;
        self.expect(")", &[])?;
        self.depth -= 1;
        Some(PegPrimary::Group(PegGroup {
            span: self.since(open.span.start),
            element,
        }))
    }
}
