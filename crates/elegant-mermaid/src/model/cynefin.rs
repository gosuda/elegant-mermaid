//! The cynefin model: five domains in declaration-then-canonical order, transitions with
//! self-loops dropped, the title and accessibility text, and the honoured config keys
//! (`spec/grammar/cynefin.md`).

use std::collections::BTreeMap;

use crate::diag::{Diagnostic, Severity};
use crate::scene::DumpValue;
use crate::source::Span;
use crate::syntax::config_value::{ConfigValue, Entry};
use crate::syntax::cynefin::DOMAIN_NAMES;
use crate::syntax::cynefin::ast::{Cynefin, DomainBlock, Transition as AstTransition};
use crate::syntax::entities::decode_entities;
use crate::syntax::langium;
use crate::syntax::preprocess::preprocess;

const CONFIG_KEY: &str = "cynefin";
const MAX_CANVAS_PX: i64 = 65536;
const MAX_SEED: i64 = (1 << 32) - 1;
const SELF_LOOP: &str = "cynefin/self-loop-transition";
const NO_SPAN: Span = Span { start: 0, end: 0 };

const INTEGER_KEYS: [(&str, i64, i64); 4] = [
    ("width", 1, MAX_CANVAS_PX),
    ("height", 1, MAX_CANVAS_PX),
    ("boundaryAmplitude", 0, MAX_CANVAS_PX),
    ("seed", 1, MAX_SEED),
];

#[derive(Debug, Clone)]
pub struct Item {
    pub label: String,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Domain {
    pub name: String,
    pub declared: bool,
    pub span: Span,
    pub items: Vec<Item>,
}

#[derive(Debug, Clone)]
pub struct Transition {
    pub from: String,
    pub to: String,
    pub label: String,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Model {
    pub title: String,
    pub title_span: Span,
    pub acc_title: String,
    pub acc_descr: String,
    pub domains: Vec<Domain>,
    pub transitions: Vec<Transition>,
    pub config: BTreeMap<String, DumpValue>,
}

pub fn resolve(source: &str, document: &Cynefin) -> (Model, Vec<Diagnostic>) {
    let mut model = Model {
        title: String::new(),
        title_span: NO_SPAN,
        acc_title: String::new(),
        acc_descr: String::new(),
        domains: Vec::new(),
        transitions: Vec::new(),
        config: BTreeMap::new(),
    };
    model.read_config(source);
    model.domains(&document.domains);
    let diagnostics = model.transitions(&document.transitions);
    model.metadata(document);
    (model, diagnostics)
}

impl Model {
    fn domains(&mut self, blocks: &[DomainBlock]) {
        for block in blocks {
            let domain = Domain {
                name: block.domain.text.clone(),
                declared: true,
                span: block.span,
                items: block
                    .items
                    .iter()
                    .map(|item| Item {
                        label: decode_entities(&item.label.text),
                        span: item.span,
                    })
                    .collect(),
            };
            match self.domains.iter().position(|d| d.name == domain.name) {
                Some(at) => self.domains[at] = domain,
                None => self.domains.push(domain),
            }
        }
        for name in DOMAIN_NAMES {
            if !self.domains.iter().any(|d| d.name == name) {
                self.domains.push(Domain {
                    name: name.to_owned(),
                    declared: false,
                    span: NO_SPAN,
                    items: Vec::new(),
                });
            }
        }
    }

    fn transitions(&mut self, nodes: &[AstTransition]) -> Vec<Diagnostic> {
        let mut out = Vec::new();
        for node in nodes {
            if node.from.text == node.to.text {
                out.push(langium::diagnostic(
                    SELF_LOOP,
                    Severity::Warning,
                    format!(
                        "self-loop transition on domain {} is skipped",
                        node.from.text
                    ),
                    node.span,
                ));
                continue;
            }
            self.transitions.push(Transition {
                from: node.from.text.clone(),
                to: node.to.text.clone(),
                label: node
                    .label
                    .as_ref()
                    .map_or_else(String::new, |label| decode_entities(&label.text)),
                span: node.span,
            });
        }
        out
    }

    fn metadata(&mut self, document: &Cynefin) {
        if let Some(title) = &document.title {
            self.title = decode_entities(&title.text).trim().to_owned();
            self.title_span = title.span;
        }
        if let Some(value) = &document.acc_title {
            self.acc_title.clone_from(&value.text);
        }
        if let Some(value) = &document.acc_descr {
            self.acc_descr.clone_from(&value.text);
        }
    }

    fn read_config(&mut self, source: &str) {
        let preprocessed = preprocess(source);
        let mut blocks = Vec::new();
        if let Some(front) = preprocessed.frontmatter {
            self.read_front_title(&front.value);
            blocks.extend(front.config);
        }
        blocks.extend(preprocessed.init_config);
        for block in &blocks {
            self.read_chart(block);
        }
    }

    fn read_front_title(&mut self, root: &ConfigValue) {
        let ConfigValue::Mapping(entries) = root else {
            return;
        };
        for entry in entries.iter().filter(|entry| entry.key == "title") {
            if let ConfigValue::String(value) = &entry.value {
                self.title = decode_entities(value).trim().to_owned();
            }
        }
    }

    fn read_chart(&mut self, block: &ConfigValue) {
        let ConfigValue::Mapping(entries) = block else {
            return;
        };
        let Some(ConfigValue::Mapping(fields)) = entries
            .iter()
            .find(|entry| entry.key == CONFIG_KEY)
            .map(|entry| &entry.value)
        else {
            return;
        };
        for field in fields {
            self.read_field(field);
        }
    }

    fn read_field(&mut self, field: &Entry) {
        let Some((_, low, high)) = INTEGER_KEYS.iter().find(|(key, _, _)| *key == field.key) else {
            return;
        };
        if let Some(n) = integer(&field.value, *low, *high) {
            self.config.insert(field.key.clone(), DumpValue::Integer(n));
        }
    }
}

fn integer(value: &ConfigValue, low: i64, high: i64) -> Option<i64> {
    let ConfigValue::Integer(text) = value else {
        return None;
    };
    text.parse::<i64>()
        .ok()
        .filter(|n| (low..=high).contains(n))
}
