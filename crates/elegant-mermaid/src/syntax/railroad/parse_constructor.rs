use super::ast::{
    Expression, RailroadChoiceExpr, RailroadNonTerminalExpr, RailroadOneOrMoreExpr,
    RailroadOptionalExpr, RailroadSequenceExpr, RailroadSpecialExpr, RailroadTerminalExpr,
    RailroadZeroOrMoreExpr, Token, Value,
};
use super::parser::Parser;
use super::text::decode_escapes;
use crate::source::Span;

const CONSTRUCTOR_STARTS: [&str; 8] = [
    "choice",
    "nonterminal",
    "oneOrMore",
    "optional",
    "sequence",
    "special",
    "terminal",
    "zeroOrMore",
];

impl Parser<'_> {
    pub(super) fn railroad_expr(&mut self) -> Option<Expression> {
        let token = self.tok().clone();
        match token.kind.as_str() {
            "sequence" | "choice" => self.railroad_list(&token),
            "optional" | "oneOrMore" | "zeroOrMore" => self.railroad_unary(&token),
            "terminal" | "nonterminal" | "special" => self.railroad_leaf(&token),
            _ => {
                self.fail(&CONSTRUCTOR_STARTS);
                None
            }
        }
    }

    fn railroad_list(&mut self, keyword: &Token) -> Option<Expression> {
        self.take();
        let open = self.expect("(", &[])?;
        if !self.enter(&open) {
            return None;
        }
        let mut items = Vec::new();
        loop {
            items.push(self.railroad_expr()?);
            if self.kind() != "," {
                break;
            }
            self.take();
        }
        self.expect(")", &[")", ","])?;
        self.depth -= 1;
        let span = self.since(keyword.span.start);
        Some(if keyword.kind == "sequence" {
            Expression::RailroadSequence(RailroadSequenceExpr {
                span,
                elements: items,
            })
        } else {
            Expression::RailroadChoice(RailroadChoiceExpr {
                span,
                alternatives: items,
            })
        })
    }

    fn railroad_unary(&mut self, keyword: &Token) -> Option<Expression> {
        self.take();
        let open = self.expect("(", &[])?;
        if !self.enter(&open) {
            return None;
        }
        let item = Box::new(self.railroad_expr()?);
        self.expect(")", &[])?;
        self.depth -= 1;
        let span = self.since(keyword.span.start);
        Some(match keyword.kind.as_str() {
            "optional" => Expression::RailroadOptional(RailroadOptionalExpr {
                span,
                element: item,
            }),
            "oneOrMore" => Expression::RailroadOneOrMore(RailroadOneOrMoreExpr {
                span,
                element: item,
            }),
            _ => Expression::RailroadZeroOrMore(RailroadZeroOrMoreExpr {
                span,
                element: item,
            }),
        })
    }

    fn railroad_leaf(&mut self, keyword: &Token) -> Option<Expression> {
        self.take();
        self.expect("(", &[])?;
        let text = self.expect("STRING", &[])?;
        self.expect(")", &[])?;
        let value = Value {
            span: text.span,
            text: decode_escapes(&text.text),
        };
        let span = Span {
            start: keyword.span.start,
            end: self.last_end(),
        };
        Some(match keyword.kind.as_str() {
            "terminal" => Expression::RailroadTerminal(RailroadTerminalExpr { span, value }),
            "nonterminal" => {
                Expression::RailroadNonTerminal(RailroadNonTerminalExpr { span, name: value })
            }
            _ => Expression::RailroadSpecial(RailroadSpecialExpr { span, text: value }),
        })
    }
}
