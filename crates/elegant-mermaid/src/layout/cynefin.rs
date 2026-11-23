//! The cynefin adapter and family entry (`spec/layout/charts.md`).
//!
//! [`from_cynefin`] authors the model-stage input: the dump skeleton as boxes, routes, and
//! labels, and the typed config entries as options. [`layout`] decodes that input again and
//! runs the chart family.

use crate::model::cynefin as mc;
use crate::scene::{Direction, DumpOptions, Profile, Scene, TextRole};

use super::chart::{Cynefin, CynefinDomain, CynefinTransition, cynefin_skeleton, layout_cynefin};
use super::input::{Box as InputBox, Input, Label as InputLabel, Route, Spacing};
use super::layered::LayoutError;

const KIND: &str = "cynefin";
const FRAME: &str = "frame";
const TITLE: &str = "title";

pub(crate) fn from_cynefin(
    model: &mc::Model,
    profile: Profile,
    mut options: DumpOptions,
) -> Result<Input, LayoutError> {
    options.set_kind_config(model.config.clone());
    options.profile = profile;
    let frame = cynefin_skeleton(&payload(model));
    Ok(Input {
        kind: KIND,
        profile,
        direction: Direction::Tb,
        options,
        boxes: frame
            .boxes
            .into_iter()
            .map(|b| InputBox {
                icon: false,
                id: b.id,
                role: b.role,
                shape: String::new(),
                parent: b.parent,
                exclusive: b.exclusive,
                text: String::new(),
                direction: String::new(),
            })
            .collect(),
        routes: frame
            .routes
            .into_iter()
            .map(|r| Route {
                id: r.id,
                from: r.from,
                to: r.to,
                orthogonal: r.orthogonal,
                marker_start: "none".to_owned(),
                marker_end: "point".to_owned(),
                line: "normal".to_owned(),
                min_length: 0,
                from_side: None,
                to_side: None,
            })
            .collect(),
        labels: frame
            .labels
            .into_iter()
            .map(|l| InputLabel {
                id: l.id,
                owner: l.owner,
                role: TextRole::Label,
                text: l.text,
            })
            .collect(),
        groups: Vec::new(),
        sizes: Vec::new(),
        attachments: Vec::new(),
        region_sets: Vec::new(),
        spacing: Spacing::default(),
    })
}

fn payload(model: &mc::Model) -> Cynefin {
    Cynefin {
        title: model.title.clone(),
        config: model.config.clone(),
        domains: model
            .domains
            .iter()
            .map(|d| CynefinDomain {
                name: d.name.clone(),
                items: d.items.iter().map(|item| item.label.clone()).collect(),
            })
            .collect(),
        transitions: model
            .transitions
            .iter()
            .map(|t| CynefinTransition {
                from: t.from.clone(),
                to: t.to.clone(),
                label: t.label.clone(),
            })
            .collect(),
    }
}

fn chart_of(input: &Input) -> Cynefin {
    let mut chart = Cynefin {
        title: String::new(),
        config: input.options.config.clone(),
        domains: input
            .boxes
            .iter()
            .filter(|b| b.id != FRAME)
            .map(|b| CynefinDomain {
                name: b.id.clone(),
                items: Vec::new(),
            })
            .collect(),
        transitions: Vec::new(),
    };
    for label in &input.labels {
        decode_label(&mut chart, label);
    }
    chart.transitions = input
        .routes
        .iter()
        .map(|r| CynefinTransition {
            from: r.from.clone(),
            to: r.to.clone(),
            label: route_label_text(input, &r.id),
        })
        .collect();
    chart
}

fn route_label_text(input: &Input, id: &str) -> String {
    input
        .labels
        .iter()
        .find(|l| l.owner == id)
        .map_or_else(String::new, |l| l.text.clone())
}

fn decode_label(chart: &mut Cynefin, label: &InputLabel) {
    if label.id == TITLE {
        chart.title.clone_from(&label.text);
        return;
    }
    let Some((name, rest)) = label.id.split_once(".i") else {
        return;
    };
    if rest.parse::<usize>().is_err() || label.owner != name {
        return;
    }
    if let Some(domain) = chart.domains.iter_mut().find(|d| d.name == name) {
        domain.items.push(label.text.clone());
    }
}

pub fn layout(input: &Input) -> Result<(Scene, bool), LayoutError> {
    let mut options = input.options.clone();
    options.profile = input.profile;
    layout_cynefin(&chart_of(input), &options)
}

#[cfg(test)]
mod tests;
