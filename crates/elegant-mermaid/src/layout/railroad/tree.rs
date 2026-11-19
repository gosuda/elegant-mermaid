use crate::geom::GeomError;
use crate::measure::Metric;
use crate::scene::{DumpOptions, Profile};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Kind {
    Terminal,
    NonTerminal,
    Special,
    Sequence,
    Choice,
    Optional,
    ZeroOrMore,
    OneOrMore,
}

impl Kind {
    pub(super) fn leaf(self) -> bool {
        matches!(self, Kind::Terminal | Kind::NonTerminal | Kind::Special)
    }

    pub(super) fn arity(self) -> (usize, usize) {
        match self {
            Kind::Terminal | Kind::NonTerminal | Kind::Special => (0, 0),
            Kind::Sequence | Kind::Choice => (2, usize::MAX),
            Kind::Optional | Kind::ZeroOrMore | Kind::OneOrMore => (1, 1),
        }
    }
}

#[derive(Debug, Clone)]
pub(super) struct Node {
    pub id: String,
    pub kind: Kind,
    pub text: String,
    pub children: Vec<Node>,
}

#[derive(Debug, Clone)]
pub(super) struct Rule {
    pub id: String,
    pub title: String,
    pub root: Node,
}

#[derive(Debug, Clone, Copy, Default)]
pub(super) struct Constants {
    pub pad_x: i64,
    pub pad_y: i64,
    pub line_height: i64,
    pub hsep: i64,
    pub vsep: i64,
    pub arc_radius: i64,
    pub terminal_radius: i64,
    pub marker_radius: i64,
    pub margin: i64,
    pub rule_name_gap: i64,
    pub rule_end_gap: i64,
    pub rule_min_baseline: i64,
    pub rule_min_height: i64,
    pub empty_width: i64,
    pub empty_height: i64,
}

#[derive(Debug, Clone)]
pub(super) struct Params {
    pub profile: Profile,
    pub options: DumpOptions,
    pub constants: Constants,
    pub metric: Metric,
}

impl Params {
    pub(super) fn is_cell(&self) -> bool {
        self.profile == Profile::Cell
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Join {
    pub id: String,
    pub from: String,
    pub to: String,
}

pub(super) fn route_id(ordinal: usize) -> String {
    format!("e{ordinal}")
}

pub(super) fn joins(rules: &[Rule]) -> Vec<Join> {
    let mut out = Vec::new();
    for rule in rules {
        append_joins(&mut out, &rule.root);
    }
    out
}

fn append_joins(out: &mut Vec<Join>, node: &Node) {
    if node.kind == Kind::Sequence {
        for pair in node.children.windows(2) {
            out.push(Join {
                id: route_id(out.len()),
                from: pair[0].id.clone(),
                to: pair[1].id.clone(),
            });
        }
    }
    for child in &node.children {
        append_joins(out, child);
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct Pt {
    pub x: i64,
    pub y: i64,
}

pub(super) fn fit(value: i64) -> Result<i32, GeomError> {
    i32::try_from(value).map_err(|_| GeomError::Overflow)
}
