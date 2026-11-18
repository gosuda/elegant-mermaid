//! The box and label records of the xychart dump, in declaration order.

use crate::model::chart::{Chart, PlotKind, Xy};
use crate::scene::{BoxRole, SceneBox, SceneLabel};

use super::ZERO_RECT;
use super::xy::XyPlan;
use super::xy_axis::Axis;

pub(crate) const PLOT_ID: &str = "plot";
pub(crate) const DEFAULT_FONT: i32 = 14;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(crate) enum LabelKind {
    #[default]
    Title,
    XTitle,
    YTitle,
    XTick,
    YTick,
    Legend,
    Point,
}

#[derive(Debug, Clone)]
pub(crate) struct LabelSpec {
    pub id: String,
    pub owner: String,
    pub text: String,
    pub kind: LabelKind,
    pub index: usize,
    pub plot: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BoxKind {
    Plot,
    Line,
    Bar,
}

#[derive(Debug, Clone)]
pub(crate) struct BoxSpec {
    pub id: String,
    pub kind: BoxKind,
    pub plot: usize,
    pub point: usize,
}

pub fn series_title(index: usize, title: &str) -> String {
    if title.is_empty() {
        format!("Series {}", index + 1)
    } else {
        title.to_owned()
    }
}

fn series_box_id(plot: usize) -> String {
    format!("p{plot}")
}

fn bar_box_id(plot: usize, point: usize) -> String {
    format!("{}.b{point}", series_box_id(plot))
}

pub(crate) fn point_label_id(plot: usize, point: usize) -> String {
    format!("{}.l{point}", series_box_id(plot))
}

pub(crate) fn box_specs(xy: &Xy) -> Vec<BoxSpec> {
    let mut specs = vec![BoxSpec {
        id: PLOT_ID.to_owned(),
        kind: BoxKind::Plot,
        plot: 0,
        point: 0,
    }];
    for (i, plot) in xy.plots.iter().enumerate() {
        if plot.kind == PlotKind::Line {
            specs.push(BoxSpec {
                id: series_box_id(i),
                kind: BoxKind::Line,
                plot: i,
                point: 0,
            });
            continue;
        }
        for (j, point) in plot.points.iter().enumerate() {
            if point.present {
                specs.push(BoxSpec {
                    id: bar_box_id(i, j),
                    kind: BoxKind::Bar,
                    plot: i,
                    point: j,
                });
            }
        }
    }
    specs
}

fn tick_specs(axis: &Axis, kind: LabelKind, prefix: &str) -> Vec<LabelSpec> {
    axis.labels
        .iter()
        .enumerate()
        .map(|(k, text)| LabelSpec {
            id: format!("{prefix}.t{k}"),
            owner: PLOT_ID.to_owned(),
            text: text.clone(),
            kind,
            index: k,
            plot: 0,
        })
        .collect()
}

fn plain_spec(id: &str, text: &str, kind: LabelKind) -> Option<LabelSpec> {
    (!text.is_empty()).then(|| LabelSpec {
        id: id.to_owned(),
        owner: PLOT_ID.to_owned(),
        text: text.to_owned(),
        kind,
        index: 0,
        plot: 0,
    })
}

pub(crate) fn label_specs(chart: &Chart, xy: &Xy, x: &Axis, y: &Axis) -> Vec<LabelSpec> {
    let mut out: Vec<LabelSpec> = [
        plain_spec("title", &chart.title, LabelKind::Title),
        plain_spec("x.title", &xy.x_title, LabelKind::XTitle),
        plain_spec("y.title", &xy.y_title, LabelKind::YTitle),
    ]
    .into_iter()
    .flatten()
    .collect();
    out.extend(tick_specs(x, LabelKind::XTick, "x"));
    out.extend(tick_specs(y, LabelKind::YTick, "y"));
    for (i, plot) in xy.plots.iter().enumerate() {
        out.push(LabelSpec {
            id: format!("legend.{i}"),
            owner: PLOT_ID.to_owned(),
            text: series_title(i, &plot.title),
            kind: LabelKind::Legend,
            index: 0,
            plot: i,
        });
    }
    for (i, plot) in xy.plots.iter().enumerate() {
        for (j, point) in plot.points.iter().enumerate() {
            if point.present && !point.label.is_empty() {
                out.push(LabelSpec {
                    id: point_label_id(i, j),
                    owner: series_box_id(i),
                    text: point.label.clone(),
                    kind: LabelKind::Point,
                    index: j,
                    plot: i,
                });
            }
        }
    }
    out
}

impl XyPlan<'_> {
    pub(crate) fn dump_boxes(&self) -> Vec<SceneBox> {
        self.boxes
            .iter()
            .enumerate()
            .map(|(i, b)| SceneBox {
                id: b.id.clone(),
                role: BoxRole::Node,
                rect: self
                    .placed
                    .as_ref()
                    .map_or(ZERO_RECT, |placed| placed.box_rects[i]),
                parent: if b.kind == BoxKind::Plot {
                    String::new()
                } else {
                    PLOT_ID.to_owned()
                },
                exclusive: false,
            })
            .collect()
    }

    pub(crate) fn dump_labels(&self) -> Vec<SceneLabel> {
        self.specs
            .iter()
            .enumerate()
            .map(|(i, s)| {
                let (rect, lines) = match &self.placed {
                    Some(placed) => (placed.label_rects[i], placed.label_lines[i].clone()),
                    None => (ZERO_RECT, Vec::new()),
                };
                SceneLabel {
                    id: s.id.clone(),
                    owner: s.owner.clone(),
                    text: s.text.clone(),
                    rect,
                    lines,
                }
            })
            .collect()
    }
}
