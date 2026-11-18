//! The quadrant payload, its dump boxes, and its dump labels.

use std::collections::BTreeMap;

use crate::geom::Rect;
use crate::scene::{Align, BoxRole, SceneBox, SceneLabel};

use super::{Skeleton, ZERO_RECT};

pub(crate) const NO_POINT_RADIUS: i64 = -1;
pub(super) const TILE_COUNT: usize = 4;
pub(super) const KIND: &str = "quadrant";
pub(super) const PLOT_ID: &str = "plot";

#[derive(Debug, Clone)]
pub(crate) struct QuadrantPoint {
    pub x: i64,
    pub y: i64,
    pub radius: i64,
    pub label: String,
}

#[derive(Debug, Clone, Default)]
pub(crate) struct Quadrant {
    pub title: String,
    pub config: BTreeMap<String, i64>,
    pub tiles: [String; TILE_COUNT],
    pub x_left: String,
    pub x_right: String,
    pub y_bottom: String,
    pub y_top: String,
    pub points: Vec<QuadrantPoint>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum BoxKind {
    Plot,
    Tile,
    Point,
}

#[derive(Debug, Clone)]
pub(super) struct BoxSpec {
    pub id: String,
    pub kind: BoxKind,
    pub index: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum LabelKind {
    Title,
    XLeft,
    XRight,
    YBottom,
    YTop,
    Tile,
    Point,
}

#[derive(Debug, Clone)]
pub(super) struct LabelSpec {
    pub id: String,
    pub owner: String,
    pub text: String,
    pub kind: LabelKind,
    pub index: usize,
}

#[derive(Debug, Clone)]
pub(super) struct Placed {
    pub box_rects: Vec<Rect>,
    pub label_rects: Vec<Rect>,
    pub label_lines: Vec<Vec<String>>,
    pub aligns: Vec<Align>,
}

pub(super) fn tile_box_id(index: usize) -> String {
    format!("q{}", index + 1)
}

pub(super) fn point_box_id(index: usize) -> String {
    format!("p{index}")
}

pub(super) fn box_specs(q: &Quadrant) -> Vec<BoxSpec> {
    let mut boxes = vec![BoxSpec {
        id: PLOT_ID.to_owned(),
        kind: BoxKind::Plot,
        index: 0,
    }];
    boxes.extend((0..TILE_COUNT).map(|index| BoxSpec {
        id: tile_box_id(index),
        kind: BoxKind::Tile,
        index,
    }));
    boxes.extend((0..q.points.len()).map(|index| BoxSpec {
        id: point_box_id(index),
        kind: BoxKind::Point,
        index,
    }));
    boxes
}

pub(super) fn label_specs(q: &Quadrant) -> Vec<LabelSpec> {
    let fixed = |id: &str, text: &str, kind: LabelKind| LabelSpec {
        id: id.to_owned(),
        owner: PLOT_ID.to_owned(),
        text: text.to_owned(),
        kind,
        index: 0,
    };
    let mut out = vec![
        fixed("title", &q.title, LabelKind::Title),
        fixed("x.left", &q.x_left, LabelKind::XLeft),
        fixed("x.right", &q.x_right, LabelKind::XRight),
        fixed("y.bottom", &q.y_bottom, LabelKind::YBottom),
        fixed("y.top", &q.y_top, LabelKind::YTop),
    ];
    for (index, text) in q.tiles.iter().enumerate() {
        out.push(LabelSpec {
            id: format!("{}.label", tile_box_id(index)),
            owner: tile_box_id(index),
            text: text.clone(),
            kind: LabelKind::Tile,
            index,
        });
    }
    for (index, point) in q.points.iter().enumerate() {
        out.push(LabelSpec {
            id: format!("{}.label", point_box_id(index)),
            owner: point_box_id(index),
            text: point.label.clone(),
            kind: LabelKind::Point,
            index,
        });
    }
    out.retain(|spec| !spec.text.is_empty());
    out
}

pub(super) fn dump_boxes(boxes: &[BoxSpec], placed: Option<&Placed>) -> Vec<SceneBox> {
    boxes
        .iter()
        .enumerate()
        .map(|(i, b)| SceneBox {
            id: b.id.clone(),
            role: BoxRole::Node,
            rect: placed.map_or(ZERO_RECT, |p| p.box_rects[i]),
            parent: if b.kind == BoxKind::Plot {
                String::new()
            } else {
                PLOT_ID.to_owned()
            },
            exclusive: false,
        })
        .collect()
}

pub(super) fn dump_labels(specs: &[LabelSpec], placed: Option<&Placed>) -> Vec<SceneLabel> {
    specs
        .iter()
        .enumerate()
        .map(|(i, s)| SceneLabel {
            id: s.id.clone(),
            owner: s.owner.clone(),
            text: s.text.clone(),
            rect: placed.map_or(ZERO_RECT, |p| p.label_rects[i]),
            lines: placed.map_or_else(Vec::new, |p| p.label_lines[i].clone()),
        })
        .collect()
}

pub(crate) fn skeleton(q: &Quadrant) -> Skeleton {
    Skeleton {
        boxes: dump_boxes(&box_specs(q), None),
        labels: dump_labels(&label_specs(q), None),
    }
}
