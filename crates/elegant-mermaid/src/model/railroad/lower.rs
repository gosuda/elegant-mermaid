use super::{Node, Resolver, UNBOUNDED, parse_count, trim_zeros};
use crate::syntax::railroad::ast::{
    AbnfAlternation, AbnfConcatenation, AbnfElement, AbnfPrimary, EbnfChoice, EbnfPostfix,
    EbnfPrimary, EbnfSequence, EbnfTerm, Expression, PegOrderedChoice, PegPrefix, PegPrimary,
    PegSequence, PegSuffix,
};

fn repetition(element: Node, min: i64, max: i64) -> Node {
    Node::Repetition {
        element: Box::new(element),
        min,
        max,
    }
}

fn optional(element: Node) -> Node {
    Node::Optional(Box::new(element))
}

fn collapse_sequence(mut elements: Vec<Node>) -> Node {
    if elements.len() == 1 {
        return elements.remove(0);
    }
    Node::Sequence(elements)
}

fn collapse_choice(mut alternatives: Vec<Node>) -> Node {
    if alternatives.len() == 1 {
        return alternatives.remove(0);
    }
    Node::Choice(alternatives)
}

fn repeat_bounds(text: &str) -> (i64, i64, &str) {
    let Some((lower_digits, upper_digits)) = text.split_once('*') else {
        let n = parse_count(text);
        return (n, n, trim_zeros(text));
    };
    let upper = if upper_digits.is_empty() {
        UNBOUNDED
    } else {
        parse_count(upper_digits)
    };
    (parse_count(lower_digits), upper, trim_zeros(upper_digits))
}

fn label(node: &Node) -> String {
    match node {
        Node::Terminal(value) => format!("\"{value}\""),
        Node::NonTerminal(name) => name.clone(),
        Node::Special(text) => text.clone(),
        _ => "(...)".into(),
    }
}

impl Resolver {
    pub(super) fn lower_body(&mut self, body: &Expression) -> Node {
        match body {
            Expression::Ebnf(choice) => self.ebnf_choice(choice),
            Expression::Abnf(alternation) => self.abnf_alternation(alternation),
            Expression::Peg(choice) => self.peg_choice(choice),
            Expression::RailroadSequence(v) => collapse_sequence(self.lower_all(&v.elements)),
            Expression::RailroadChoice(v) => collapse_choice(self.lower_all(&v.alternatives)),
            Expression::RailroadOptional(v) => optional(self.lower_body(&v.element)),
            Expression::RailroadOneOrMore(v) => {
                repetition(self.lower_body(&v.element), 1, UNBOUNDED)
            }
            Expression::RailroadZeroOrMore(v) => {
                repetition(self.lower_body(&v.element), 0, UNBOUNDED)
            }
            Expression::RailroadTerminal(v) => Node::Terminal(v.value.text.clone()),
            Expression::RailroadNonTerminal(v) => Node::NonTerminal(v.name.text.clone()),
            Expression::RailroadSpecial(v) => Node::Special(v.text.text.clone()),
        }
    }

    fn lower_all(&mut self, items: &[Expression]) -> Vec<Node> {
        items.iter().map(|item| self.lower_body(item)).collect()
    }

    fn ebnf_choice(&mut self, choice: &EbnfChoice) -> Node {
        let alternatives = choice
            .alternatives
            .iter()
            .map(|sequence| self.ebnf_sequence(sequence))
            .collect();
        collapse_choice(alternatives)
    }

    fn ebnf_sequence(&mut self, sequence: &EbnfSequence) -> Node {
        let elements = sequence
            .elements
            .iter()
            .map(|term| self.ebnf_term(term))
            .collect();
        collapse_sequence(elements)
    }

    fn ebnf_term(&mut self, term: &EbnfTerm) -> Node {
        let mut node = self.ebnf_primary(&term.base);
        for postfix in &term.postfixes {
            node = self.ebnf_postfix(node, postfix);
        }
        node
    }

    fn ebnf_postfix(&mut self, node: Node, postfix: &EbnfPostfix) -> Node {
        match postfix {
            EbnfPostfix::Optional(_) => optional(node),
            EbnfPostfix::ZeroOrMore(_) => repetition(node, 0, UNBOUNDED),
            EbnfPostfix::OneOrMore(_) => repetition(node, 1, UNBOUNDED),
            EbnfPostfix::Exception(exception) => Node::Sequence(vec![
                node,
                Node::Terminal("-".into()),
                self.ebnf_primary(&exception.except),
            ]),
        }
    }

    fn ebnf_primary(&mut self, primary: &EbnfPrimary) -> Node {
        match primary {
            EbnfPrimary::Terminal(v) => Node::Terminal(v.value.text.clone()),
            EbnfPrimary::NonTerminal(v) => Node::NonTerminal(v.name.text.clone()),
            EbnfPrimary::Special(v) => Node::Special(v.text.text.clone()),
            EbnfPrimary::Group(v) => self.ebnf_choice(&v.element),
            EbnfPrimary::Optional(v) => optional(self.ebnf_choice(&v.element)),
            EbnfPrimary::Repetition(v) => repetition(self.ebnf_choice(&v.element), 0, UNBOUNDED),
        }
    }

    fn abnf_alternation(&mut self, alternation: &AbnfAlternation) -> Node {
        let alternatives = alternation
            .alternatives
            .iter()
            .map(|concatenation| self.abnf_concatenation(concatenation))
            .collect();
        collapse_choice(alternatives)
    }

    fn abnf_concatenation(&mut self, concatenation: &AbnfConcatenation) -> Node {
        let elements = concatenation
            .elements
            .iter()
            .map(|element| self.abnf_element(element))
            .collect();
        collapse_sequence(elements)
    }

    fn abnf_element(&mut self, element: &AbnfElement) -> Node {
        let inner = self.abnf_primary(&element.primary);
        let Some(repeat) = &element.repeat else {
            return inner;
        };
        let (lower, upper, upper_text) = repeat_bounds(&repeat.text);
        if lower == 0 && upper == 1 {
            return optional(inner);
        }
        if upper != UNBOUNDED {
            self.repeat_notice(repeat, upper_text);
        }
        repetition(inner, lower, upper)
    }

    fn abnf_primary(&mut self, primary: &AbnfPrimary) -> Node {
        match primary {
            AbnfPrimary::StringLiteral(v) => Node::Terminal(v.value.text.clone()),
            AbnfPrimary::NumVal(v) => Node::Terminal(v.value.text.clone()),
            AbnfPrimary::RuleName(v) => Node::NonTerminal(v.name.text.clone()),
            AbnfPrimary::Group(v) => self.abnf_alternation(&v.element),
            AbnfPrimary::OptionalGroup(v) => optional(self.abnf_alternation(&v.element)),
        }
    }

    fn peg_choice(&mut self, choice: &PegOrderedChoice) -> Node {
        let alternatives = choice
            .alternatives
            .iter()
            .map(|sequence| self.peg_sequence(sequence))
            .collect();
        collapse_choice(alternatives)
    }

    fn peg_sequence(&mut self, sequence: &PegSequence) -> Node {
        let elements = sequence
            .elements
            .iter()
            .map(|prefix| self.peg_prefix(prefix))
            .collect();
        collapse_sequence(elements)
    }

    fn peg_prefix(&mut self, prefix: &PegPrefix) -> Node {
        let inner = self.peg_suffix(&prefix.suffix);
        match &prefix.operator {
            None => inner,
            Some(operator) => Node::Special(format!("{}{}", operator.text, label(&inner))),
        }
    }

    fn peg_suffix(&mut self, suffix: &PegSuffix) -> Node {
        let inner = self.peg_primary(&suffix.primary);
        let Some(operator) = &suffix.operator else {
            return inner;
        };
        match operator.kind.as_str() {
            "?" => optional(inner),
            "*" => repetition(inner, 0, UNBOUNDED),
            _ => repetition(inner, 1, UNBOUNDED),
        }
    }

    fn peg_primary(&mut self, primary: &PegPrimary) -> Node {
        match primary {
            PegPrimary::Literal(v) => Node::Terminal(v.value.text.clone()),
            PegPrimary::Identifier(v) => Node::NonTerminal(v.name.text.clone()),
            PegPrimary::Group(v) => self.peg_choice(&v.element),
            PegPrimary::Any(_) => Node::Special(".".into()),
        }
    }
}
