mod lower;
#[cfg(test)]
mod tests;

use crate::diag::{Diagnostic, Severity};
use crate::source::Span;
use crate::syntax::railroad::ast::{MetaKind, Notation, Start, Token};

const CODE_NO_RULES: &str = "railroad/no-rules";
const CODE_REPEAT_MAX: &str = "railroad/repeat-max-ignored";
const COUNT_CAP: i64 = 1 << 62;

pub const UNBOUNDED: i64 = -1;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Node {
    Terminal(String),
    NonTerminal(String),
    Special(String),
    Sequence(Vec<Node>),
    Choice(Vec<Node>),
    Optional(Box<Node>),
    Repetition {
        element: Box<Node>,
        min: i64,
        max: i64,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rule {
    pub name: String,
    pub index: usize,
    pub definition: Node,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Model {
    pub notation: Notation,
    pub title: String,
    pub acc_title: String,
    pub acc_descr: String,
    pub rules: Vec<Rule>,
}

pub fn resolve(start: &Start) -> (Model, Vec<Diagnostic>) {
    let mut resolver = Resolver { diags: Vec::new() };
    let mut model = Model {
        notation: start.notation,
        title: String::new(),
        acc_title: String::new(),
        acc_descr: String::new(),
        rules: Vec::new(),
    };
    for meta in &start.meta {
        match meta.kind {
            MetaKind::Title => model.title.clone_from(&meta.value),
            MetaKind::AccTitle => model.acc_title.clone_from(&meta.value),
            MetaKind::AccDescr => model.acc_descr.clone_from(&meta.value),
        }
    }
    for rule in &start.rules {
        model.rules.push(Rule {
            name: rule.name.text.clone(),
            index: rule.index,
            definition: resolver.lower_body(&rule.body),
            span: rule.span,
        });
    }
    if model.rules.is_empty() {
        resolver.diags.push(registry_diagnostic(
            CODE_NO_RULES,
            "diagram has no railroad rules",
            start.header.span,
        ));
    }
    (model, resolver.diags)
}

struct Resolver {
    diags: Vec<Diagnostic>,
}

fn registry_diagnostic(code: &'static str, message: &str, span: Span) -> Diagnostic {
    let row = crate::r#gen::diagnostics::DIAGNOSTICS
        .iter()
        .find(|row| row.code == code);
    Diagnostic {
        code,
        severity: match row.map(|row| row.severity) {
            Some("info") => Severity::Info,
            _ => Severity::Warning,
        },
        message: message.into(),
        span,
        related: Vec::new(),
        help: row.map_or("", |row| row.help).into(),
        fixes: Vec::new(),
    }
}

impl Resolver {
    fn repeat_notice(&mut self, token: &Token, max: &str) {
        self.diags.push(registry_diagnostic(
            CODE_REPEAT_MAX,
            &format!("finite repetition maximum {max} is not drawn"),
            token.span,
        ));
    }
}

fn parse_count(digits: &str) -> i64 {
    let mut n: i64 = 0;
    for byte in digits.bytes() {
        let d = i64::from(byte.wrapping_sub(b'0'));
        if n > (COUNT_CAP - d) / 10 {
            return COUNT_CAP;
        }
        n = n * 10 + d;
    }
    n
}

fn trim_zeros(digits: &str) -> &str {
    let mut rest = digits;
    while rest.len() > 1 && rest.starts_with('0') {
        rest = &rest[1..];
    }
    if rest.is_empty() { "0" } else { rest }
}
