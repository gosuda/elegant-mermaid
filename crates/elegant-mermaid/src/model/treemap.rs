//! Treemap resolution in source order, with a flat preorder arena and indentation stack.
use crate::diag::Diagnostic;
use crate::scene::DumpValue;
use crate::source::Span;
use crate::syntax::config_value::ConfigValue;
use crate::syntax::preprocess::preprocess;
use crate::syntax::treemap::{self as syn, Item, RowContent, Statement, Treemap};
use std::collections::BTreeMap;

#[derive(Debug, Clone)]
pub struct Class {
    pub name: String,
    pub styles: Vec<String>,
    pub text_styles: Vec<String>,
}
#[derive(Debug, Clone)]
pub struct Node {
    pub name: String,
    pub leaf: bool,
    pub value: i64,
    pub selector: String,
    pub styles: Vec<String>,
    pub index: usize,
    pub span: Span,
    pub name_span: Span,
    pub value_span: Option<Span>,
    pub exact_zero: bool,
    pub next_more_indented: bool,
    pub parent: Option<usize>,
    pub children: Vec<usize>,
}
#[derive(Debug, Clone)]
pub struct Model {
    pub title: String,
    pub acc_title: String,
    pub acc_descr: String,
    pub config: BTreeMap<String, DumpValue>,
    pub classes: Vec<Class>,
    pub nodes: Vec<Node>,
    pub roots: Vec<usize>,
    pub span: Span,
}
const LABEL_STYLES: [&str; 18] = [
    "color",
    "font-size",
    "font-family",
    "font-weight",
    "font-style",
    "text-decoration",
    "text-align",
    "text-transform",
    "line-height",
    "letter-spacing",
    "word-spacing",
    "text-shadow",
    "text-overflow",
    "white-space",
    "word-wrap",
    "word-break",
    "overflow-wrap",
    "hyphens",
];

pub fn thousandths(literal: &str) -> i64 {
    let (whole, fraction) = literal.split_once('.').unwrap_or((literal, ""));
    let mut value = 0_i64;
    for b in whole.bytes() {
        value = (value * 10 + i64::from(b - b'0')).min(1_i64 << 32);
    }
    value *= 1000;
    let mut tail = 0;
    for i in 0..4 {
        tail = tail * 10
            + fraction
                .as_bytes()
                .get(i)
                .map_or(0, |b| i64::from(*b - b'0'));
    }
    value + tail / 10 + i64::from(tail % 10 >= 5)
}
pub fn format_value(value: i64) -> String {
    let whole = (value / 1000).to_string();
    let mut out = String::new();
    for (i, c) in whole.chars().enumerate() {
        if i > 0 && (whole.len() - i).is_multiple_of(3) {
            out.push(',');
        }
        out.push(c);
    }
    let fraction = value % 1000;
    if fraction != 0 {
        out.push('.');
        out.push_str(format!("{fraction:03}").trim_end_matches('0'));
    }
    out
}
fn read_config(model: &mut Model, source: &str) {
    let pre = preprocess(source);
    let mut blocks = Vec::new();
    if let Some(front) = pre.frontmatter {
        if let ConfigValue::Mapping(entries) = front.value {
            for e in entries.into_iter().filter(|e| e.key == "title") {
                let ConfigValue::String(s) = e.value else {
                    continue;
                };
                model.title = s.trim().to_owned();
            }
        }
        blocks.extend(front.config);
    }
    blocks.extend(pre.init_config);
    for block in blocks {
        read_chart_config(model, &block);
    }
}
fn read_chart_config(model: &mut Model, block: &ConfigValue) {
    let ConfigValue::Mapping(entries) = block else {
        return;
    };
    let Some(ConfigValue::Mapping(fields)) = entries
        .iter()
        .find(|e| e.key == "treemap")
        .map(|e| &e.value)
    else {
        return;
    };
    for field in fields {
        let low = match field.key.as_str() {
            "padding" => 0,
            "nodeWidth" | "nodeHeight" => 1,
            _ => continue,
        };
        let ConfigValue::Integer(text) = &field.value else {
            continue;
        };
        let Ok(n) = text.parse::<i64>() else {
            continue;
        };
        if (low..=65536).contains(&n) {
            model
                .config
                .insert(field.key.clone(), DumpValue::Integer(n));
        }
    }
}
fn collect_classes(model: &mut Model, doc: &Treemap) {
    for statement in &doc.rows {
        let Statement::Row(row) = statement else {
            continue;
        };
        let RowContent::ClassDef(class) = &row.content else {
            continue;
        };
        let i = match model.classes.iter().position(|c| c.name == class.name) {
            Some(i) => i,
            None => {
                model.classes.push(Class {
                    name: class.name.clone(),
                    styles: Vec::new(),
                    text_styles: Vec::new(),
                });
                model.classes.len() - 1
            }
        };
        let style = class
            .style
            .replace("\\,", "\0")
            .replace(',', ";")
            .replace('\0', ",");
        for s in style.split(';') {
            if LABEL_STYLES.contains(&s) {
                model.classes[i].text_styles.push(s.to_owned());
            }
            model.classes[i].styles.push(s.to_owned());
        }
    }
}
fn metadata(model: &mut Model, doc: &Treemap) {
    let mut last = BTreeMap::new();
    for statement in &doc.rows {
        let Statement::Metadata(group) = statement else {
            continue;
        };
        for (kind, text) in &group.tokens {
            last.insert(*kind, text.as_str());
        }
    }
    if let Some(title) = last.get("TITLE").filter(|s| !s.is_empty()) {
        model.title = (*title).to_owned();
    }
    model.acc_title = last.get("ACC_TITLE").copied().unwrap_or("").to_owned();
    model.acc_descr = last.get("ACC_DESCR").copied().unwrap_or("").to_owned();
}
fn node_of(model: &Model, item: &Item, parent: Option<usize>) -> Node {
    let (name, selector, span, leaf, value) = match item {
        Item::Section(s) => (&s.name, &s.selector, s.span, false, 0),
        Item::Leaf(l) => (
            &l.name,
            &l.selector,
            l.span,
            true,
            if l.value.valid {
                thousandths(&l.value.literal)
            } else {
                0
            },
        ),
    };
    let selector = selector.as_ref().map_or("", |s| s.name.as_str());
    let styles = model
        .classes
        .iter()
        .find(|c| c.name == selector)
        .map_or_else(Vec::new, |c| c.styles.clone());
    Node {
        name: name.value.clone(),
        leaf,
        value,
        selector: selector.to_owned(),
        styles,
        index: model.nodes.len(),
        span,
        name_span: name.span,
        value_span: match item {
            Item::Leaf(l) => Some(l.value.span),
            Item::Section(_) => None,
        },
        exact_zero: matches!(item, Item::Leaf(l) if l.value.valid && l.value.literal.trim_matches(['0', '.']).is_empty()),
        next_more_indented: false,
        parent,
        children: Vec::new(),
    }
}
pub fn resolve(source: &str, doc: &Treemap) -> (Model, Vec<Diagnostic>) {
    let mut model = Model {
        span: doc.span,
        title: String::new(),
        acc_title: String::new(),
        acc_descr: String::new(),
        config: BTreeMap::new(),
        classes: Vec::new(),
        nodes: Vec::new(),
        roots: Vec::new(),
    };
    let mut diagnostics = Vec::new();
    read_config(&mut model, source);
    collect_classes(&mut model, doc);
    metadata(&mut model, doc);
    let mut stack: Vec<(usize, usize)> = Vec::new();
    let mut deep = false;
    let mut previous: Option<(usize, usize)> = None;
    for statement in &doc.rows {
        let Statement::Row(row) = statement else {
            continue;
        };
        let RowContent::Item(item) = &row.content else {
            continue;
        };
        let level = row.indent.unwrap_or(0);
        if let Some((index, previous_level)) = previous {
            model.nodes[index].next_more_indented =
                model.nodes[index].leaf && level > previous_level;
        }
        while stack.last().is_some_and(|(_, indent)| *indent >= level) {
            stack.pop();
        }
        let parent = stack.last().map(|(i, _)| *i);
        let node = node_of(&model, item, parent);
        let index = node.index;
        let span = node.span;
        let leaf = node.leaf;
        model.nodes.push(node);
        previous = Some((index, level));
        if let Some(p) = parent {
            model.nodes[p].children.push(index);
        } else {
            model.roots.push(index);
        }
        if !leaf {
            stack.push((index, level));
        }
        if stack.len() > 64 && !deep {
            deep = true;
            diagnostics.push(syn::diagnostic(
                "limit/nesting-depth",
                "nesting depth exceeds 64".to_owned(),
                span,
            ));
        }
    }
    (model, diagnostics)
}
