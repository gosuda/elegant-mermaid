//! The cynefin payload and the dump skeleton: box, route, and label ids, texts, and
//! parents in declaration order, before measurement and placement.

use std::collections::BTreeMap;

use crate::scene::{BoxRole, DumpValue, SceneBox, SceneLabel, SceneRoute};

use super::ZERO_RECT;

pub(crate) const KIND: &str = "cynefin";
pub(crate) const FRAME_ID: &str = "frame";
pub(crate) const TITLE_ID: &str = "title";
pub(crate) const CONFUSION: &str = "confusion";

pub(crate) const ORDER: [&str; 5] = ["complex", "complicated", "clear", "chaotic", "confusion"];

#[derive(Debug, Clone)]
pub struct CynefinDomain {
    pub name: String,
    pub items: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct CynefinTransition {
    pub from: String,
    pub to: String,
    pub label: String,
}

#[derive(Debug, Clone)]
pub struct Cynefin {
    pub title: String,
    pub config: BTreeMap<String, DumpValue>,
    pub domains: Vec<CynefinDomain>,
    pub transitions: Vec<CynefinTransition>,
}

impl Cynefin {
    pub(crate) fn integer(&self, key: &str) -> Option<i64> {
        match self.config.get(key) {
            Some(DumpValue::Integer(n)) => Some(*n),
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Frame {
    pub boxes: Vec<SceneBox>,
    pub routes: Vec<SceneRoute>,
    pub labels: Vec<SceneLabel>,
}

#[derive(Debug, Clone)]
pub(crate) struct RouteSpec {
    pub id: String,
    pub from: String,
    pub to: String,
    pub label: String,
}

pub(crate) fn domain_title(name: &str) -> String {
    let mut chars = name.chars();
    chars.next().map_or_else(String::new, |first| {
        first.to_uppercase().chain(chars).collect()
    })
}

pub(crate) fn domain_label_id(name: &str) -> String {
    format!("{name}.label")
}

pub(crate) fn item_label_id(name: &str, index: usize) -> String {
    format!("{name}.i{index}")
}

pub(crate) fn route_id(index: usize) -> String {
    format!("e{index}")
}

pub(crate) fn route_label_id(index: usize) -> String {
    format!("{}.label", route_id(index))
}

pub(crate) fn normalized_domains(chart: &Cynefin) -> Vec<CynefinDomain> {
    let mut out: Vec<CynefinDomain> = Vec::new();
    for domain in &chart.domains {
        if ORDER.contains(&domain.name.as_str()) && !out.iter().any(|o| o.name == domain.name) {
            out.push(domain.clone());
        }
    }
    for name in ORDER {
        if !out.iter().any(|o| o.name == name) {
            out.push(CynefinDomain {
                name: name.to_owned(),
                items: Vec::new(),
            });
        }
    }
    out
}

pub(crate) fn cynefin_routes(chart: &Cynefin) -> Vec<RouteSpec> {
    let mut out: Vec<RouteSpec> = Vec::new();
    for t in &chart.transitions {
        let known = |name: &str| ORDER.contains(&name);
        if t.from == t.to || !known(&t.from) || !known(&t.to) {
            continue;
        }
        out.push(RouteSpec {
            id: route_id(out.len()),
            from: t.from.clone(),
            to: t.to.clone(),
            label: t.label.clone(),
        });
    }
    out
}

fn skeleton_box(id: &str, parent: &str) -> SceneBox {
    SceneBox {
        id: id.to_owned(),
        role: BoxRole::Node,
        rect: ZERO_RECT,
        parent: parent.to_owned(),
        exclusive: false,
    }
}

fn skeleton_label(id: String, owner: &str, text: &str) -> SceneLabel {
    SceneLabel {
        id,
        owner: owner.to_owned(),
        text: text.to_owned(),
        rect: ZERO_RECT,
        lines: Vec::new(),
    }
}

pub fn cynefin_skeleton(chart: &Cynefin) -> Frame {
    let mut frame = Frame {
        boxes: vec![skeleton_box(FRAME_ID, "")],
        routes: Vec::new(),
        labels: Vec::new(),
    };
    if !chart.title.is_empty() {
        frame
            .labels
            .push(skeleton_label(TITLE_ID.to_owned(), FRAME_ID, &chart.title));
    }
    for domain in normalized_domains(chart) {
        frame.boxes.push(skeleton_box(&domain.name, FRAME_ID));
        frame.labels.push(skeleton_label(
            domain_label_id(&domain.name),
            &domain.name,
            &domain_title(&domain.name),
        ));
        for (i, item) in domain.items.iter().enumerate() {
            frame.labels.push(skeleton_label(
                item_label_id(&domain.name, i),
                &domain.name,
                item,
            ));
        }
    }
    for (i, route) in cynefin_routes(chart).into_iter().enumerate() {
        frame.routes.push(SceneRoute {
            id: route.id.clone(),
            from: route.from,
            to: route.to,
            orthogonal: true,
            points: Vec::new(),
            marker_start: String::new(),
            marker_end: String::new(),
            stroke: String::new(),
        });
        if !route.label.is_empty() {
            frame
                .labels
                .push(skeleton_label(route_label_id(i), &route.id, &route.label));
        }
    }
    frame
}
