use crate::diag::Diagnostic;
use crate::scene::DumpValue;
use crate::source::Span;
use crate::syntax::config_value::ConfigValue;
use crate::syntax::entities::decode_entities as decode;
use crate::syntax::preprocess::preprocess;
use crate::syntax::sankey::ast::{Field, Start};
use std::collections::BTreeMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ValueKind {
    Finite,
    NonFinite,
    Overflow,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Value {
    pub kind: ValueKind,
    pub thousandths: i64,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node {
    pub id: String,
    pub label: Option<String>,
    pub span: Span,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Link {
    pub source: usize,
    pub target: usize,
    pub value: Value,
    pub span: Span,
}
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Model {
    pub config: BTreeMap<String, DumpValue>,
    pub nodes: Vec<Node>,
    pub links: Vec<Link>,
}

pub fn resolve(source: &str, document: &Start) -> (Model, Vec<Diagnostic>) {
    let mut model = Model::default();
    let pre = preprocess(source);
    let mut blocks = Vec::new();
    if let Some(front) = pre.frontmatter {
        blocks.extend(front.config);
    }
    blocks.extend(pre.init_config);
    for block in blocks {
        read_config(&mut model.config, block);
    }
    let mut indices = BTreeMap::new();
    for record in &document.csv.records {
        let source = node(&mut model.nodes, &mut indices, &record.source);
        let target = node(&mut model.nodes, &mut indices, &record.target);
        model.links.push(Link {
            source,
            target,
            value: parse_value(record.value.text()),
            span: record.span,
        });
    }
    (model, Vec::new())
}

fn node(nodes: &mut Vec<Node>, indices: &mut BTreeMap<String, usize>, field: &Field) -> usize {
    let id = decode(&field.text().trim().replace("\"\"", "\""));
    if let Some(index) = indices.get(&id) {
        return *index;
    }
    let index = nodes.len();
    indices.insert(id.clone(), index);
    nodes.push(Node {
        id,
        label: None,
        span: field.span,
    });
    index
}

fn read_config(config: &mut BTreeMap<String, DumpValue>, block: ConfigValue) {
    let ConfigValue::Mapping(entries) = block else {
        return;
    };
    for entry in entries {
        if entry.key != "sankey" {
            continue;
        }
        let ConfigValue::Mapping(fields) = entry.value else {
            continue;
        };
        for field in fields {
            let value = match (field.key.as_str(), field.value) {
                ("width" | "height", ConfigValue::Integer(text)) => text
                    .parse::<i64>()
                    .ok()
                    .filter(|n| (1..=65536).contains(n))
                    .map(DumpValue::Integer),
                ("showValues", ConfigValue::Bool(value)) => Some(DumpValue::Bool(value)),
                ("nodeAlignment", ConfigValue::String(value))
                    if ["left", "right", "center", "justify"].contains(&value.as_str()) =>
                {
                    Some(DumpValue::String(value))
                }
                _ => None,
            };
            if let Some(value) = value {
                config.insert(field.key, value);
            }
        }
    }
}

pub fn parse_value(text: &str) -> Value {
    let Some(decimal) = Decimal::scan(text.trim()) else {
        return Value {
            kind: ValueKind::NonFinite,
            thousandths: 0,
        };
    };
    match decimal.scaled() {
        Some(thousandths) => Value {
            kind: ValueKind::Finite,
            thousandths,
        },
        None => Value {
            kind: ValueKind::Overflow,
            thousandths: 0,
        },
    }
}

struct Decimal {
    negative: bool,
    digits: String,
    fraction: i64,
    exponent: i64,
}

impl Decimal {
    fn scan(text: &str) -> Option<Self> {
        let bytes = text.as_bytes();
        let start = usize::from(matches!(bytes.first(), Some(b'+' | b'-')));
        let mut at = digit_end(bytes, start);
        let whole_end = at;
        let mut fraction = at;
        if bytes.get(at) == Some(&b'.') {
            fraction = at + 1;
            at = digit_end(bytes, fraction);
        }
        if whole_end == start && at == fraction {
            return None;
        }
        let digits = format!("{}{}", &text[start..whole_end], &text[fraction..at]);
        Some(Self {
            negative: bytes.first() == Some(&b'-'),
            digits: digits.trim_start_matches('0').to_owned(),
            fraction: i64::try_from(at - fraction).ok()?,
            exponent: exponent(bytes, at),
        })
    }

    fn scaled(&self) -> Option<i64> {
        if self.digits.is_empty() {
            return Some(0);
        }
        let size = i64::try_from(self.digits.len()).ok()?;
        let power = self.exponent - self.fraction + 3;
        if size + power > 10 {
            return None;
        }
        let mut value = 0_i64;
        if power >= 0 {
            for byte in self.digits.bytes() {
                value = value * 10 + i64::from(byte - b'0');
            }
            for _ in 0..power {
                value *= 10;
            }
        } else if size >= -power {
            let keep = usize::try_from(size + power).ok()?;
            for byte in self.digits[..keep].bytes() {
                value = value * 10 + i64::from(byte - b'0');
            }
            if self.digits.as_bytes()[keep] >= b'5' {
                value += 1;
            }
        }
        if value > i64::from(i32::MAX) {
            return None;
        }
        Some(if self.negative { -value } else { value })
    }
}

fn digit_end(bytes: &[u8], mut at: usize) -> usize {
    while bytes.get(at).is_some_and(u8::is_ascii_digit) {
        at += 1;
    }
    at
}

fn exponent(bytes: &[u8], mut at: usize) -> i64 {
    if !matches!(bytes.get(at), Some(b'e' | b'E')) {
        return 0;
    }
    at += 1;
    let negative = bytes.get(at) == Some(&b'-');
    if matches!(bytes.get(at), Some(b'+' | b'-')) {
        at += 1;
    }
    let mut value = 0_i64;
    for byte in &bytes[at..digit_end(bytes, at)] {
        value = (value * 10 + i64::from(*byte - b'0')).min(999999999);
    }
    if negative { -value } else { value }
}

#[cfg(test)]
#[path = "sankey/tests.rs"]
mod tests;
