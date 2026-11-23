//! The quadrant adapter and family entry (`spec/layout/charts.md`).
//!
//! [`from_quadrant`] authors the model-stage input: the dump skeleton as boxes and labels,
//! the honoured config keys as options, and the point coordinates and radii as region
//! sets, because the closed [`Input`] has no chart payload. [`layout`] decodes that input
//! again and runs the chart family.

use crate::model::quadrant as mq;
use crate::scene::{Direction, DumpOptions, DumpValue, Profile, Scene, TextRole};

use super::chart::{self, NO_POINT_RADIUS, Quadrant, QuadrantPoint};
use super::input::{Box as InputBox, Input, Label as InputLabel, RegionSet, Spacing};
use super::layered::LayoutError;

const KIND: &str = "quadrant";
const FIRST_POINT_BOX: usize = 5;

pub(crate) fn from_quadrant(
    model: &mq::Model,
    profile: Profile,
    mut options: DumpOptions,
) -> Result<Input, LayoutError> {
    options.set_kind_config(model
        .config
        .iter()
        .map(|(key, value)| (key.clone(), DumpValue::Integer(*value)))
        .collect());
    options.profile = profile;
    let payload = payload(model);
    let skeleton = chart::quadrant_skeleton(&payload);
    let boxes = skeleton
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
        .collect();
    let labels = skeleton
        .labels
        .into_iter()
        .map(|l| InputLabel {
            id: l.id,
            owner: l.owner,
            role: TextRole::Label,
            text: l.text,
        })
        .collect();
    Ok(Input {
        kind: KIND,
        profile,
        direction: Direction::Tb,
        options,
        boxes,
        routes: Vec::new(),
        labels,
        groups: Vec::new(),
        sizes: Vec::new(),
        attachments: Vec::new(),
        region_sets: regions(&payload),
        spacing: Spacing::default(),
    })
}

fn payload(model: &mq::Model) -> Quadrant {
    Quadrant {
        title: model.title.clone(),
        config: model.config.clone(),
        tiles: model.quadrants.clone(),
        x_left: model.x_left.clone(),
        x_right: model.x_right.clone(),
        y_bottom: model.y_bottom.clone(),
        y_top: model.y_top.clone(),
        points: model
            .points
            .iter()
            .map(|p| QuadrantPoint {
                x: p.x,
                y: p.y,
                radius: p.radius,
                label: p.text.clone(),
            })
            .collect(),
    }
}

fn regions(q: &Quadrant) -> Vec<RegionSet> {
    q.points
        .iter()
        .enumerate()
        .map(|(i, p)| RegionSet {
            parent: FIRST_POINT_BOX + i,
            regions: [p.x, p.y, p.radius - NO_POINT_RADIUS]
                .map(|n| usize::try_from(n).unwrap_or(0))
                .to_vec(),
        })
        .collect()
}

fn quadrant_of(input: &Input) -> Quadrant {
    let mut q = Quadrant {
        config: input
            .options
            .config
            .iter()
            .filter_map(|(key, value)| match value {
                DumpValue::Integer(n) => Some((key.clone(), *n)),
                _ => None,
            })
            .collect(),
        ..Quadrant::default()
    };
    for set in &input.region_sets {
        if let [x, y, radius, ..] = set.regions[..] {
            let field = |n: usize| i64::try_from(n).unwrap_or(i64::MAX);
            q.points.push(QuadrantPoint {
                x: field(x),
                y: field(y),
                radius: field(radius) + NO_POINT_RADIUS,
                label: String::new(),
            });
        }
    }
    for label in &input.labels {
        decode_label(&mut q, &label.id, &label.text);
    }
    q
}

fn decode_label(q: &mut Quadrant, id: &str, text: &str) {
    match id {
        "title" => q.title = text.to_owned(),
        "x.left" => q.x_left = text.to_owned(),
        "x.right" => q.x_right = text.to_owned(),
        "y.bottom" => q.y_bottom = text.to_owned(),
        "y.top" => q.y_top = text.to_owned(),
        _ => {}
    }
    let Some(owner) = id.strip_suffix(".label") else {
        return;
    };
    let (Some(prefix), Some(digits)) = (owner.get(..1), owner.get(1..)) else {
        return;
    };
    let Ok(index) = digits.parse::<usize>() else {
        return;
    };
    match prefix {
        "q" if (1..=q.tiles.len()).contains(&index) => q.tiles[index - 1] = text.to_owned(),
        "p" if index < q.points.len() => q.points[index].label = text.to_owned(),
        _ => {}
    }
}

pub fn layout(input: &Input) -> Result<(Scene, bool), LayoutError> {
    let mut options = input.options.clone();
    options.profile = input.profile;
    chart::layout_quadrant(&quadrant_of(input), &options)
}

#[cfg(test)]
mod tests;
