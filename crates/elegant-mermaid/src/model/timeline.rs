//! Semantic resolution of the timeline model (`spec/grammar/timeline.md`, resolution).

use crate::diag::Diagnostic;
use crate::source::Span;
use crate::syntax::entities::decode_entities as decode;
use crate::syntax::timeline::ast::{Start, StatementKind};
use crate::syntax::timeline::lexer::Token;
use crate::syntax::timeline::{diagnostic, is_space};

const C_EVENT_WITHOUT_PERIOD: &str = "timeline/event-without-period";

#[derive(Debug, Clone)]
pub struct Event {
    pub text: String,
    pub label: String,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Period {
    pub text: String,
    pub label: String,
    pub section: Option<usize>,
    pub section_name: String,
    pub events: Vec<Event>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Section {
    pub name: String,
    pub label: String,
    pub span: Span,
}

#[derive(Debug, Clone, Default)]
pub struct Model {
    pub acc_title: String,
    pub acc_descr: String,
    pub title: String,
    pub title_label: String,
    pub direction: String,
    pub sections: Vec<Section>,
    pub periods: Vec<Period>,
}

impl Model {
    pub fn vertical(&self) -> bool {
        self.direction == "TD"
    }

    fn statement(&mut self, kind: &StatementKind) -> Option<Diagnostic> {
        match kind {
            StatementKind::Title(node) => {
                self.title.clone_from(&node.token.value);
                self.title_label = label(&self.title);
            }
            StatementKind::AccTitle(node) => self.acc_title = trim(&node.value.value).into(),
            StatementKind::AccDescr(node) => self.acc_descr = description(&node.value.value),
            StatementKind::AccDescrBlock(node) => self.acc_descr = description(&node.value.value),
            StatementKind::Section(node) => self.sections.push(Section {
                name: node.token.value.clone(),
                label: label(&node.token.value),
                span: node.token.span,
            }),
            StatementKind::Period(node) => self.add_period(&node.token),
            StatementKind::Event(node) => return self.add_event(&node.token),
        }
        None
    }

    fn add_period(&mut self, token: &Token) {
        let (section, section_name) = match self.sections.last() {
            Some(last) => (Some(self.sections.len() - 1), last.name.clone()),
            None => (None, String::new()),
        };
        self.periods.push(Period {
            text: token.value.clone(),
            label: label(&token.value),
            section,
            section_name,
            events: Vec::new(),
            span: token.span,
        });
    }

    fn add_event(&mut self, token: &Token) -> Option<Diagnostic> {
        let Some(last) = self.periods.last_mut() else {
            return Some(diagnostic(
                C_EVENT_WITHOUT_PERIOD,
                "event has no preceding period".into(),
                token.span,
            ));
        };
        last.events.push(Event {
            text: token.value.clone(),
            label: label(&token.value),
            span: token.span,
        });
        None
    }
}

pub fn resolve(_source: &str, document: &Start) -> (Model, Vec<Diagnostic>) {
    let mut model = Model {
        direction: if document.header.direction == "TD" {
            "TD".into()
        } else {
            "LR".into()
        },
        ..Model::default()
    };
    let mut diagnostics = Vec::new();
    for line in &document.document.lines {
        if let Some(statement) = &line.statement {
            diagnostics.extend(model.statement(&statement.kind));
        }
    }
    (model, diagnostics)
}

fn trim(text: &str) -> &str {
    text.trim_matches(is_space)
}

fn description(text: &str) -> String {
    let mut out = String::new();
    let mut chars = trim(text).chars().peekable();
    while let Some(c) = chars.next() {
        out.push(c);
        if c == '\n' {
            while chars.next_if(|next| is_space(*next)).is_some() {}
        }
    }
    out
}

fn label(text: &str) -> String {
    decode(trim(text))
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod tests;
