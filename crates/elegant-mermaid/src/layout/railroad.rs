//! The railroad family: `from_railroad` authors the model-stage input, and [`layout`]
//! places every rule of the diagram (`spec/layout/railroad.md`).
//!
//! The input tree is one `rule` group box for each rule, holding one box for the rule
//! definition, and nested group boxes for the composite nodes. Layout rebuilds the node
//! tree from those boxes, so the family needs no model type.

mod place;
mod rails;
mod size;
#[cfg(test)]
mod tests;
mod tree;

use std::collections::BTreeMap;

use self::tree::{Constants, Kind, Node, Params, Rule};
use super::{
    input::{Box as InputBox, Input, Label, Route, Spacing},
    layered::LayoutError,
};
use crate::{
    geom::GeomError,
    measure::{Metric, Role},
    model::railroad::{self as model, Model},
    scene::{BoxRole, Direction, DumpOptions, Profile, Scene, TextRole},
};

const KIND: &str = "railroad";
const RULE_SHAPE: &str = "rule";

const KINDS: [(&str, Kind); 8] = [
    ("terminal", Kind::Terminal),
    ("nonterminal", Kind::NonTerminal),
    ("special", Kind::Special),
    ("sequence", Kind::Sequence),
    ("choice", Kind::Choice),
    ("optional", Kind::Optional),
    ("zeroOrMore", Kind::ZeroOrMore),
    ("oneOrMore", Kind::OneOrMore),
];

pub fn from_railroad(
    model: &Model,
    profile: Profile,
    mut options: DumpOptions,
) -> Result<Input, GeomError> {
    options.config.clear();
    let mut input = Input {
        kind: KIND,
        profile,
        direction: Direction::Tb,
        options,
        boxes: Vec::new(),
        routes: Vec::new(),
        labels: Vec::new(),
        groups: Vec::new(),
        sizes: Vec::new(),
        attachments: Vec::new(),
        region_sets: Vec::new(),
        spacing: Spacing::default(),
    };
    let mut rules = Vec::with_capacity(model.rules.len());
    for (index, rule) in model.rules.iter().enumerate() {
        let id = format!("r{index}");
        let mut next = 0;
        let rule = Rule {
            root: tree_of(&rule.definition, &id, &mut next),
            title: format!("{} =", rule.name),
            id,
        };
        add_rule(&mut input, &rule);
        rules.push(rule);
    }
    for join in tree::joins(&rules) {
        input.routes.push(Route {
            id: join.id,
            from: join.from,
            to: join.to,
            orthogonal: true,
            marker_start: String::new(),
            marker_end: String::new(),
            line: String::new(),
            min_length: 0,
            from_side: None,
            to_side: None,
        });
    }
    Ok(input)
}

fn tree_of(node: &model::Node, rule: &str, next: &mut usize) -> Node {
    let id = format!("{rule}.{next}");
    *next += 1;
    let (kind, text, children) = match node {
        model::Node::Terminal(value) => (Kind::Terminal, display_text(value), Vec::new()),
        model::Node::NonTerminal(name) => (Kind::NonTerminal, display_text(name), Vec::new()),
        model::Node::Special(text) => (
            Kind::Special,
            display_text(&format!("? {text} ?")),
            Vec::new(),
        ),
        model::Node::Sequence(elements) => (
            Kind::Sequence,
            String::new(),
            children_of(elements, rule, next),
        ),
        model::Node::Choice(alternatives) => (
            Kind::Choice,
            String::new(),
            children_of(alternatives, rule, next),
        ),
        model::Node::Optional(element) => (
            Kind::Optional,
            String::new(),
            vec![tree_of(element, rule, next)],
        ),
        model::Node::Repetition { element, min, .. } => {
            let kind = if *min == 0 {
                Kind::ZeroOrMore
            } else {
                Kind::OneOrMore
            };
            (kind, String::new(), vec![tree_of(element, rule, next)])
        }
    };
    Node {
        id,
        kind,
        text,
        children,
    }
}

fn children_of(nodes: &[model::Node], rule: &str, next: &mut usize) -> Vec<Node> {
    nodes.iter().map(|node| tree_of(node, rule, next)).collect()
}

fn display_text(text: &str) -> String {
    text.chars()
        .map(|c| match c {
            '\t' | '\n' | '\r' => ' ',
            c if c < ' ' || ('\u{7f}'..='\u{9f}').contains(&c) => '\u{fffd}',
            c => c,
        })
        .collect()
}

fn add_rule(input: &mut Input, rule: &Rule) {
    input.boxes.push(InputBox {
        icon: false,
        id: rule.id.clone(),
        role: BoxRole::Group,
        shape: RULE_SHAPE.into(),
        parent: String::new(),
        exclusive: false,
        text: rule.title.clone(),
        direction: String::new(),
    });
    input.labels.push(Label {
        id: format!("{}.label", rule.id),
        owner: rule.id.clone(),
        role: TextRole::Label,
        text: rule.title.clone(),
    });
    add_node(input, &rule.root, &rule.id);
}

fn add_node(input: &mut Input, node: &Node, parent: &str) {
    let mut entry = InputBox {
        icon: false,
        id: node.id.clone(),
        role: BoxRole::Node,
        shape: shape_of(node.kind).into(),
        parent: parent.to_owned(),
        exclusive: false,
        text: String::new(),
        direction: String::new(),
    };
    if node.kind.leaf() {
        entry.exclusive = true;
        entry.text = node.text.clone();
        input.boxes.push(entry);
        input.labels.push(Label {
            id: format!("{}.label", node.id),
            owner: node.id.clone(),
            role: TextRole::Label,
            text: node.text.clone(),
        });
    } else {
        entry.role = BoxRole::Group;
        input.boxes.push(entry);
    }
    for child in &node.children {
        add_node(input, child, &node.id);
    }
}

fn shape_of(kind: Kind) -> &'static str {
    KINDS
        .iter()
        .find(|(_, candidate)| *candidate == kind)
        .map_or("", |(shape, _)| shape)
}

fn kind_of(shape: &str) -> Kind {
    KINDS
        .iter()
        .find(|(candidate, _)| *candidate == shape)
        .map_or(Kind::Terminal, |(_, kind)| *kind)
}

pub fn layout(input: &Input) -> Result<(Scene, bool), LayoutError> {
    let rules = rules_of(input)?;
    let constants = constants_of(input.profile)?;
    let mut options = input.options.clone();
    options.profile = input.profile;
    options.direction = input.direction;
    let metric = if input.profile == Profile::Cell {
        Metric::cell()
    } else {
        Metric::for_role(Role::Label)
    };
    let scene = place::layout(
        &rules,
        Params {
            profile: input.profile,
            options,
            constants,
            metric,
        },
    )?;
    Ok((scene, false))
}

struct Builder<'a> {
    input: &'a Input,
    children: BTreeMap<&'a str, Vec<usize>>,
    seen: Vec<bool>,
    text: BTreeMap<&'a str, &'a str>,
}

fn rules_of(input: &Input) -> Result<Vec<Rule>, GeomError> {
    let mut builder = Builder {
        input,
        children: BTreeMap::new(),
        seen: vec![false; input.boxes.len()],
        text: BTreeMap::new(),
    };
    for (index, entry) in input.boxes.iter().enumerate() {
        builder
            .children
            .entry(entry.parent.as_str())
            .or_default()
            .push(index);
    }
    for label in &input.labels {
        builder
            .text
            .entry(label.owner.as_str())
            .or_insert(label.text.as_str());
    }
    let tops = builder.children.get("").cloned().unwrap_or_default();
    tops.into_iter().map(|index| builder.rule(index)).collect()
}

impl Builder<'_> {
    fn rule(&mut self, index: usize) -> Result<Rule, GeomError> {
        let input = self.input;
        let entry = &input.boxes[index];
        if entry.shape != RULE_SHAPE {
            return Ok(Rule {
                id: String::new(),
                title: String::new(),
                root: self.node(index)?,
            });
        }
        self.seen[index] = true;
        let kids = self
            .children
            .get(entry.id.as_str())
            .cloned()
            .unwrap_or_default();
        let [only] = kids.as_slice() else {
            return Err(GeomError::Domain);
        };
        Ok(Rule {
            id: entry.id.clone(),
            title: self.display_of(entry),
            root: self.node(*only)?,
        })
    }

    fn display_of(&self, entry: &InputBox) -> String {
        if let Some(text) = self.text.get(entry.id.as_str()) {
            return (*text).to_owned();
        }
        if entry.text.is_empty() {
            entry.id.clone()
        } else {
            entry.text.clone()
        }
    }

    fn node(&mut self, index: usize) -> Result<Node, GeomError> {
        if self.seen[index] {
            return Err(GeomError::Domain);
        }
        self.seen[index] = true;
        let input = self.input;
        let entry = &input.boxes[index];
        let kids = self
            .children
            .get(entry.id.as_str())
            .cloned()
            .unwrap_or_default();
        let children = kids
            .into_iter()
            .map(|child| self.node(child))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Node {
            id: entry.id.clone(),
            kind: kind_of(&entry.shape),
            text: self.display_of(entry),
            children,
        })
    }
}

fn constants_of(profile: Profile) -> Result<Constants, GeomError> {
    let value = |name: &str| -> Result<i64, GeomError> {
        let key = format!("{}.{KIND}.{name}", profile.as_str());
        crate::r#gen::layoutconst::LAYOUT_CONST
            .iter()
            .find(|row| row.name == key)
            .map(|row| i64::from(row.value))
            .ok_or(GeomError::Domain)
    };
    Ok(Constants {
        pad_x: value("pad_x")?,
        pad_y: value("pad_y")?,
        line_height: value("line_height")?,
        hsep: value("hsep")?,
        vsep: value("vsep")?,
        arc_radius: value("arc_radius")?,
        terminal_radius: value("terminal_radius")?,
        marker_radius: value("marker_radius")?,
        margin: value("margin")?,
        rule_name_gap: value("rule_name_gap")?,
        rule_end_gap: value("rule_end_gap")?,
        rule_min_baseline: value("rule_min_baseline")?,
        rule_min_height: value("rule_min_height")?,
        empty_width: value("empty_width")?,
        empty_height: value("empty_height")?,
    })
}
