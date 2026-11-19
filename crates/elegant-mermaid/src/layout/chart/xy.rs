//! The xychart plan: constants, measured texts, and the phase order of the layout.

use crate::geom::{GeomError, Rect, Size};
use crate::measure::{self, Metric, Role};
use crate::model::chart::{Chart, Orientation, Xy};
use crate::scene::{Align, Direction, Dump, DumpOptions, Profile, Run, Scene};

use super::xy_axis::{Axis, Position, check_magnitude, new_axes};
use super::xy_spec::{BoxSpec, DEFAULT_FONT, LabelKind, LabelSpec, box_specs, label_specs};
use super::{Area, LayoutError, Skeleton, constant, to_i32};

const KIND: &str = "xychart";
const CELL_CANVAS_PX_WIDE: i64 = 8;
const CELL_CANVAS_PX_HIGH: i64 = 16;
const VECTOR_UNITS_PER_PX: i64 = 64;

#[derive(Debug, Clone, Copy)]
pub(crate) struct Consts {
    pub width: i64,
    pub height: i64,
    pub reserved: i64,
    pub bar_pad: i64,
    pub bar_ratio: i64,
    pub outer_max: i64,
    pub axis_line: i64,
    pub axis_title_pad: i64,
    pub pad_x: i64,
    pub pad_y: i64,
    pub tick_len: i64,
    pub title_pad: i64,
    pub legend_pad: i64,
    pub legend_marker: i64,
    pub marker_gap: i64,
    pub item_gap: i64,
    pub point_offset: i64,
    pub point_size: i64,
    pub edge: i64,
}

fn load_consts(profile: Profile, chart: &Chart) -> Result<Consts, LayoutError> {
    let get = |name: &str| constant(profile, &format!("xychart.{name}"));
    let mut consts = Consts {
        width: get("width")?,
        height: get("height")?,
        reserved: get("plot_reserved_percent")?,
        bar_pad: get("bar_padding_m")?,
        bar_ratio: get("bar_width_ratio_m")?,
        outer_max: get("label_outer_max_m")?,
        axis_line: get("axis_line")?,
        axis_title_pad: get("axis_title_pad")?,
        pad_x: get("label_pad_x")?,
        pad_y: get("label_pad_y")?,
        tick_len: get("tick_length")?,
        title_pad: get("title_pad")?,
        legend_pad: get("legend_pad")?,
        legend_marker: get("legend_marker")?,
        marker_gap: get("legend_marker_gap")?,
        item_gap: get("legend_item_gap")?,
        point_offset: get("point_label_offset")?,
        point_size: get("point_label_size")?,
        edge: i64::from(profile == Profile::Cell),
    };
    if let Some(n) = chart.integer("width") {
        consts.width = canvas_side(profile, n, CELL_CANVAS_PX_WIDE);
    }
    if let Some(n) = chart.integer("height") {
        consts.height = canvas_side(profile, n, CELL_CANVAS_PX_HIGH);
    }
    if let Some(n) = chart.integer("plotReservedSpacePercent") {
        consts.reserved = n;
    }
    Ok(consts)
}

fn canvas_side(profile: Profile, px: i64, cell_px: i64) -> i64 {
    if profile == Profile::Cell {
        measure::ceil_div(px, cell_px)
    } else {
        px * VECTOR_UNITS_PER_PX
    }
}

#[derive(Debug, Clone)]
pub(crate) struct MeasuredLine {
    pub text: String,
    pub runs: Vec<Run>,
}

#[derive(Debug, Clone, Default)]
pub(crate) struct TextBox {
    pub lines: Vec<MeasuredLine>,
    pub w: i64,
    pub h: i64,
}

#[derive(Debug, Clone)]
pub(crate) struct Placed {
    pub box_rects: Vec<Rect>,
    pub label_rects: Vec<Rect>,
    pub label_lines: Vec<Vec<String>>,
    pub shown: Vec<bool>,
    pub aligns: Vec<Align>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AxisId {
    X,
    Y,
}

pub(crate) struct XyPlan<'a> {
    pub xy: &'a Xy,
    pub c: Consts,
    pub cell: bool,
    pub x: Axis,
    pub y: Axis,
    pub capped: bool,
    pub boxes: Vec<BoxSpec>,
    pub specs: Vec<LabelSpec>,
    pub texts: Vec<TextBox>,
    pub width: i64,
    pub height: i64,
    pub plot: Area,
    pub title_shown: bool,
    pub side_title: Option<usize>,
    pub side_shown: bool,
    pub legend: Area,
    pub legend_on: bool,
    pub legend_lh: i64,
    pub legend_rows: i64,
    pub title_h: i64,
    pub placed: Option<Placed>,
}

impl<'a> XyPlan<'a> {
    pub(crate) fn new(
        chart: &'a Chart,
        xy: &'a Xy,
        profile: Profile,
    ) -> Result<XyPlan<'a>, LayoutError> {
        let c = load_consts(profile, chart)?;
        let (mut x, mut y, capped) = new_axes(xy)?;
        check_points(xy)?;
        let horizontal = xy.orientation == Orientation::Horizontal;
        (x.position, y.position) = if horizontal {
            (Position::Left, Position::Top)
        } else {
            (Position::Bottom, Position::Left)
        };
        (x.tick_kind, x.title_kind) = (LabelKind::XTick, LabelKind::XTitle);
        (y.tick_kind, y.title_kind) = (LabelKind::YTick, LabelKind::YTitle);
        (x.show_labels, y.show_labels) = (true, true);
        (x.font_size, y.font_size) = (DEFAULT_FONT, DEFAULT_FONT);
        if let Some(show) = chart.boolean("xAxis.showLabel") {
            x.show_labels = show;
        }
        if let Some(size) = chart.integer("xAxis.labelFontSize") {
            x.font_size = i32::try_from(size).unwrap_or(DEFAULT_FONT);
        }
        let boxes = box_specs(xy);
        let specs = label_specs(chart, xy, &x, &y);
        Ok(XyPlan {
            xy,
            c,
            cell: profile == Profile::Cell,
            x,
            y,
            capped,
            boxes,
            specs,
            texts: Vec::new(),
            width: 0,
            height: 0,
            plot: Area::default(),
            title_shown: false,
            side_title: None,
            side_shown: false,
            legend: Area::default(),
            legend_on: false,
            legend_lh: 0,
            legend_rows: 0,
            title_h: 0,
            placed: None,
        })
    }

    pub(crate) fn horizontal(&self) -> bool {
        self.xy.orientation == Orientation::Horizontal
    }

    pub(crate) fn axis_mut(&mut self, id: AxisId) -> &mut Axis {
        match id {
            AxisId::X => &mut self.x,
            AxisId::Y => &mut self.y,
        }
    }

    pub(crate) fn with_axis<R>(&mut self, id: AxisId, f: impl FnOnce(&Self, &mut Axis) -> R) -> R {
        let mut axis = std::mem::take(self.axis_mut(id));
        let out = f(self, &mut axis);
        *self.axis_mut(id) = axis;
        out
    }

    pub(crate) fn style_of(&self, spec: &LabelSpec) -> (Role, i32) {
        match spec.kind {
            LabelKind::Title => (Role::Title, Role::Title.size_px()),
            LabelKind::XTick => (Role::Label, self.x.font_size),
            LabelKind::Point => (
                Role::Body,
                i32::try_from(self.c.point_size / VECTOR_UNITS_PER_PX).unwrap_or(DEFAULT_FONT),
            ),
            _ => (Role::Label, DEFAULT_FONT),
        }
    }

    fn line_height(&self, role: Role, size: i32) -> i64 {
        if self.cell {
            return 1;
        }
        measure::round_half_up(
            i64::from(size) * VECTOR_UNITS_PER_PX * i64::from(role.line_height_px()),
            i64::from(role.size_px()),
        )
    }

    fn metric(&self, role: Role, size: i32) -> Metric {
        if self.cell {
            Metric::cell()
        } else {
            Metric::Vector {
                size_px: size,
                weight: role.weight(),
                font_family: false,
            }
        }
    }

    fn measure_text(&self, text: &str, role: Role, size: i32) -> Result<TextBox, LayoutError> {
        let lines = measure::styled_lines(text, i32::MAX, self.metric(role, size))?;
        let widest = lines
            .iter()
            .map(|line| i64::from(line.width))
            .max()
            .unwrap_or(0);
        let height = i64::try_from(lines.len()).unwrap_or(i64::MAX) * self.line_height(role, size);
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
            h: height,
        })
    }

    pub(crate) fn measure_all(&mut self) -> Result<(), LayoutError> {
        let mut texts = Vec::with_capacity(self.specs.len());
        for spec in &self.specs {
            let (role, size) = self.style_of(spec);
            texts.push(self.measure_text(&spec.text, role, size)?);
        }
        self.texts = texts;
        Ok(())
    }

    pub(crate) fn find(&self, kind: LabelKind) -> Option<usize> {
        self.specs.iter().position(|spec| spec.kind == kind)
    }

    pub(crate) fn tick_extent(&self, kind: LabelKind) -> (i64, i64) {
        self.specs
            .iter()
            .zip(&self.texts)
            .filter(|(spec, _)| spec.kind == kind)
            .fold((0, 0), |(w, h), (_, text)| (w.max(text.w), h.max(text.h)))
    }
}

fn check_points(xy: &Xy) -> Result<(), LayoutError> {
    for plot in &xy.plots {
        for point in &plot.points {
            check_magnitude(&[point.value, point.x])?;
        }
    }
    Ok(())
}

pub(super) fn layout_xy(
    chart: &Chart,
    options: &DumpOptions,
) -> Result<(Scene, bool), LayoutError> {
    let xy = chart.xy.as_ref().ok_or(GeomError::Domain)?;
    let mut plan = XyPlan::new(chart, xy, options.profile)?;
    plan.measure_all()?;
    plan.arrange();
    plan.place()?;
    let canvas = Size {
        w: to_i32(plan.width)?,
        h: to_i32(plan.height)?,
    };
    let mut dump_options = options.clone();
    dump_options.direction = Direction::Tb;
    let mut dump = Dump::new(KIND, dump_options);
    dump.boxes = plan.dump_boxes();
    dump.labels = plan.dump_labels();
    let groups = plan.groups()?;
    Ok((Scene::new(canvas, dump, groups), plan.capped))
}

pub(super) fn skeleton(chart: &Chart) -> Result<Skeleton, LayoutError> {
    let xy = chart.xy.as_ref().ok_or(GeomError::Domain)?;
    let plan = XyPlan::new(chart, xy, Profile::Vector)?;
    Ok(Skeleton {
        boxes: plan.dump_boxes(),
        labels: plan.dump_labels(),
    })
}
