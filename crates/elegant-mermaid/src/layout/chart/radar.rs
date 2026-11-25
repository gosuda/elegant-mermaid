//! The radar plan: constants, measured texts, and the phase order of the layout
//! (`spec/layout/charts.md`, charts-87 to charts-94). Geometry is in vector units only;
//! the text back end draws the vector scene as braille dots.

use crate::geom::{GeomError, Rect, Size, floor_div};
use crate::measure::{self, Metric, Role};
use crate::model::chart::{Chart, Radar};
use crate::scene::{
    Align, BoxRole, Direction, Dump, DumpOptions, Profile, Run, Scene, SceneBox, SceneLabel,
};

use super::scale::clamp;
use super::xy::{MeasuredLine, TextBox};
use super::xy_axis::check_magnitude;
use super::{Area, LayoutError, Skeleton, ZERO_RECT, constant};

const KIND: &str = "radar";
pub(super) const PLOT_ID: &str = "plot";
const TITLE_ID: &str = "title";
const TICK_SCALE: i64 = 1000;
const TICKS_AT: i64 = 32 * TICK_SCALE;
const FONT: i32 = 14;
const UNITS_PER_PX: i64 = 64;

#[derive(Debug, Clone, Copy)]
pub(super) struct Consts {
    pub width: i64,
    pub height: i64,
    pub margin: i64,
    pub gap_x: i64,
    pub gap_y: i64,
    pub legend_row: i64,
    pub tension: i64,
    pub marker: i64,
    pub marker_gap: i64,
    pub anchor: i64,
    pub margin_top: i64,
    pub margin_right: i64,
}

fn load_consts(chart: &Chart) -> Result<Consts, LayoutError> {
    let get = |name: &str| constant(Profile::Vector, &format!("radar.{name}"));
    let margin = get("margin")?;
    let mut c = Consts {
        width: get("width")?,
        height: get("height")?,
        margin,
        gap_x: get("label_gap_x")?,
        gap_y: get("label_gap_y")?,
        legend_row: get("legend_row")?,
        tension: get("curve_tension")?,
        marker: get("legend_marker")?,
        marker_gap: get("legend_text_gap")?,
        anchor: get("anchor_q15")?,
        margin_top: margin,
        margin_right: margin,
    };
    for (key, into, unit) in [
        ("width", &mut c.width, UNITS_PER_PX),
        ("height", &mut c.height, UNITS_PER_PX),
        ("marginTop", &mut c.margin_top, UNITS_PER_PX),
        ("marginRight", &mut c.margin_right, UNITS_PER_PX),
        ("curveTension", &mut c.tension, 1),
    ] {
        if let Some(n) = chart.integer(key) {
            *into = n * unit;
        }
    }
    Ok(c)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum LabelKind {
    Title,
    Axis,
    Legend,
}

#[derive(Debug, Clone)]
pub(super) struct Label {
    pub id: String,
    pub text: String,
    pub kind: LabelKind,
    pub index: usize,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(super) struct Pt {
    pub x: i64,
    pub y: i64,
}

pub(super) struct RadarPlan<'a> {
    pub r: &'a Radar,
    pub c: Consts,
    font_family: bool,
    pub radius: i64,
    pub extent: i64,
    pub rings: Vec<i64>,
    pub drawn: Vec<usize>,
    pub lo: i64,
    pub hi: i64,
    pub labels: Vec<Label>,
    pub texts: Vec<TextBox>,
    pub rects: Vec<Area>,
    pub shown: Vec<bool>,
    pub aligns: Vec<Align>,
    pub frame: Area,
    pub plot: Area,
    pub curves: Vec<Vec<Pt>>,
    pub markers: Vec<Area>,
    pub dx: i64,
    pub dy: i64,
    pub canvas: Size,
    pub box_rects: Vec<Rect>,
    pub label_rects: Vec<Rect>,
    pub placed: bool,
}

pub(super) fn curve_id(index: usize) -> String {
    format!("c{index}")
}

fn axis_id(index: usize) -> String {
    format!("axis.{index}")
}

fn legend_id(index: usize) -> String {
    format!("legend.{index}")
}

fn labels_of(chart: &Chart, radar: &Radar) -> Vec<Label> {
    let mut out = Vec::new();
    if !chart.title.is_empty() {
        out.push(Label {
            id: TITLE_ID.to_owned(),
            text: chart.title.clone(),
            kind: LabelKind::Title,
            index: 0,
        });
    }
    for (index, axis) in radar.axes.iter().enumerate() {
        out.push(Label {
            id: axis_id(index),
            text: axis.clone(),
            kind: LabelKind::Axis,
            index,
        });
    }
    for (index, curve) in radar.curves.iter().enumerate() {
        out.push(Label {
            id: legend_id(index),
            text: curve.label.clone(),
            kind: LabelKind::Legend,
            index,
        });
    }
    out
}

pub(super) fn ring_radii(radius: i64, ticks: i64) -> Vec<i64> {
    let ticks = clamp(ticks, 0, TICKS_AT);
    let count = floor_div(ticks + TICK_SCALE - 1, TICK_SCALE);
    (0..count)
        .map(|i| floor_div(radius * (i + 1) * TICK_SCALE, ticks))
        .collect()
}

impl<'a> RadarPlan<'a> {
    pub(super) fn new(chart: &'a Chart, radar: &'a Radar) -> Result<RadarPlan<'a>, LayoutError> {
        let c = load_consts(chart)?;
        let radius = floor_div(c.width.min(c.height), 2);
        let rings = ring_radii(radius, radar.ticks);
        let extent = rings.iter().copied().fold(radius, i64::max);
        let (lo, hi) = resolve_range(radar)?;
        let mut plan = RadarPlan {
            r: radar,
            c,
            font_family: crate::scene::has_font_family(&chart.config),
            radius,
            extent,
            rings,
            drawn: Vec::new(),
            lo,
            hi,
            labels: labels_of(chart, radar),
            texts: Vec::new(),
            rects: Vec::new(),
            shown: Vec::new(),
            aligns: Vec::new(),
            frame: Area::default(),
            plot: Area::default(),
            curves: Vec::new(),
            markers: Vec::new(),
            dx: 0,
            dy: 0,
            canvas: Size { w: 0, h: 0 },
            box_rects: Vec::new(),
            label_rects: Vec::new(),
            placed: false,
        };
        plan.drawn = plan.drawn_curves();
        Ok(plan)
    }

    fn drawn_curves(&self) -> Vec<usize> {
        if self.r.axes.is_empty() || self.hi <= self.lo {
            return Vec::new();
        }
        let axes = self.r.axes.len();
        self.r
            .curves
            .iter()
            .enumerate()
            .filter(|(_, curve)| curve.values.len() == axes)
            .map(|(index, _)| index)
            .collect()
    }

    fn box_ids(&self) -> Vec<String> {
        let mut ids = vec![PLOT_ID.to_owned()];
        ids.extend(self.drawn.iter().map(|&i| curve_id(i)));
        ids
    }

    pub(super) fn dump_boxes(&self) -> Vec<SceneBox> {
        self.box_ids()
            .into_iter()
            .enumerate()
            .map(|(i, id)| SceneBox {
                id,
                role: BoxRole::Node,
                rect: if self.placed {
                    self.box_rects[i]
                } else {
                    ZERO_RECT
                },
                parent: if i == 0 {
                    String::new()
                } else {
                    PLOT_ID.to_owned()
                },
                exclusive: false,
            })
            .collect()
    }

    pub(super) fn dump_labels(&self) -> Vec<SceneLabel> {
        self.labels
            .iter()
            .enumerate()
            .map(|(i, l)| {
                let shown = self.placed && self.shown[i];
                SceneLabel {
                    id: l.id.clone(),
                    owner: PLOT_ID.to_owned(),
                    text: l.text.clone(),
                    rect: if shown {
                        self.label_rects[i]
                    } else {
                        ZERO_RECT
                    },
                    lines: if shown {
                        self.texts[i]
                            .lines
                            .iter()
                            .map(|line| line.text.clone())
                            .collect()
                    } else {
                        Vec::new()
                    },
                }
            })
            .collect()
    }

    fn measure_text(&self, label: &Label) -> Result<TextBox, LayoutError> {
        let (role, size) = role_of(label);
        let metric = Metric::Vector {
            size_px: size,
            weight: role.weight(),
            font_family: self.font_family,
        };
        let lines = measure::styled_lines(&label.text, i32::MAX, metric)?;
        let widest = lines
            .iter()
            .map(|line| i64::from(line.width))
            .max()
            .unwrap_or(0);
        let line_h = measure::round_half_up(
            i64::from(size) * UNITS_PER_PX * i64::from(role.line_height_px()),
            i64::from(role.size_px()),
        );
        let count = i64::try_from(lines.len()).unwrap_or(i64::MAX);
        let lines = lines
            .iter()
            .map(|line| MeasuredLine {
                text: line.text.clone(),
                runs: line
                    .runs
                    .iter()
                    .map(|run| Run {
                        text: run.text.to_owned(),
                        bold: run.bold,
                        italic: run.italic,
                    })
                    .collect(),
            })
            .collect();
        Ok(TextBox {
            lines,
            w: widest,
            h: count * line_h,
        })
    }

    fn measure_all(&mut self) -> Result<(), LayoutError> {
        self.texts = self
            .labels
            .iter()
            .map(|label| self.measure_text(label))
            .collect::<Result<_, _>>()?;
        Ok(())
    }
}

pub(super) fn role_of(label: &Label) -> (Role, i32) {
    if label.kind == LabelKind::Title {
        (Role::Title, Role::Title.size_px())
    } else {
        (Role::Label, FONT)
    }
}

fn resolve_range(radar: &Radar) -> Result<(i64, i64), LayoutError> {
    let mut high = radar.max;
    let mut seen = radar.has_max;
    for curve in &radar.curves {
        for &value in &curve.values {
            check_magnitude(&[value])?;
            if !seen || (!radar.has_max && value > high) {
                high = value;
                seen = true;
            }
        }
    }
    let low = radar.min;
    if !seen {
        high = low;
    }
    check_magnitude(&[low, high])?;
    if high - low > i64::from(i32::MAX) {
        return Err(GeomError::Overflow);
    }
    Ok((low, high))
}

pub(super) fn layout_radar(
    chart: &Chart,
    options: &DumpOptions,
) -> Result<(Scene, bool), LayoutError> {
    let radar = chart.radar.as_ref().ok_or(GeomError::Domain)?;
    let mut plan = RadarPlan::new(chart, radar)?;
    plan.measure_all()?;
    plan.place()?;
    let mut dump_options = options.clone();
    dump_options.profile = Profile::Vector;
    dump_options.direction = Direction::Tb;
    let mut dump = Dump::new(KIND, dump_options);
    dump.boxes = plan.dump_boxes();
    dump.labels = plan.dump_labels();
    let groups = plan.groups()?;
    Ok((Scene::new(plan.canvas, dump, groups), false))
}

pub(super) fn skeleton(chart: &Chart) -> Result<Skeleton, LayoutError> {
    let radar = chart.radar.as_ref().ok_or(GeomError::Domain)?;
    let plan = RadarPlan::new(chart, radar)?;
    Ok(Skeleton {
        boxes: plan.dump_boxes(),
        labels: plan.dump_labels(),
    })
}
