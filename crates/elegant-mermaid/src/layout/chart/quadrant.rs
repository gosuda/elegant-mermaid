//! The quadrant plan: constants, measured texts, and the phase order of the layout.

use crate::geom::{GeomError, Size};
use crate::measure::{self, Metric, Role};
use crate::scene::{Direction, Dump, DumpOptions, Profile, Scene};

use super::quadrant_spec::{
    BoxKind, BoxSpec, KIND, LabelKind, LabelSpec, Placed, Quadrant, TILE_COUNT, box_specs,
    dump_boxes, dump_labels, label_specs,
};
use super::xy::{MeasuredLine, TextBox};
use super::{Area, LayoutError, constant, to_i32};

pub(super) const UNITS_PER_PX: i64 = 64;
pub(super) const CELL_PX_X: i64 = 8;
pub(super) const CELL_PX_Y: i64 = 16;
pub(super) const MIN_PLOT: i64 = 2;
const CELL_INSET: i64 = 1;
pub(super) const SCALE: i64 = 1000;

pub(super) fn units(profile: Profile, px: i64, cell_px: i64) -> i64 {
    if profile == Profile::Cell {
        measure::ceil_div(px, cell_px)
    } else {
        px * UNITS_PER_PX
    }
}

pub(super) fn units_x(profile: Profile, px: i64) -> i64 {
    units(profile, px, CELL_PX_X)
}

pub(super) fn units_y(profile: Profile, px: i64) -> i64 {
    units(profile, px, CELL_PX_Y)
}

#[derive(Debug, Clone, Copy)]
pub(super) struct QuadConsts {
    pub width: i64,
    pub height: i64,
    pub pad_x: i64,
    pub pad_y: i64,
    pub title_band: i64,
    pub x_band: i64,
    pub y_band: i64,
    pub title_pad_px: i64,
    pub title_font_px: i64,
    pub x_pad_px: i64,
    pub x_font_px: i64,
    pub y_pad_px: i64,
    pub y_font_px: i64,
    pub radius_x: i64,
    pub radius_y: i64,
    pub text_pad: i64,
    pub label_font_px: i64,
    pub point_font_px: i64,
    pub top_pad: i64,
    pub edge: i64,
}

type BandFields = fn(&mut QuadConsts) -> (&mut i64, &mut i64, &mut i64);

struct BandRule {
    pad_key: &'static str,
    font_key: &'static str,
    horizontal: bool,
    fields: BandFields,
}

fn title_fields(c: &mut QuadConsts) -> (&mut i64, &mut i64, &mut i64) {
    (&mut c.title_pad_px, &mut c.title_font_px, &mut c.title_band)
}

fn x_fields(c: &mut QuadConsts) -> (&mut i64, &mut i64, &mut i64) {
    (&mut c.x_pad_px, &mut c.x_font_px, &mut c.x_band)
}

fn y_fields(c: &mut QuadConsts) -> (&mut i64, &mut i64, &mut i64) {
    (&mut c.y_pad_px, &mut c.y_font_px, &mut c.y_band)
}

const BAND_RULES: [BandRule; 3] = [
    BandRule {
        pad_key: "titlePadding",
        font_key: "titleFontSize",
        horizontal: false,
        fields: title_fields,
    },
    BandRule {
        pad_key: "xAxisLabelPadding",
        font_key: "xAxisLabelFontSize",
        horizontal: false,
        fields: x_fields,
    },
    BandRule {
        pad_key: "yAxisLabelPadding",
        font_key: "yAxisLabelFontSize",
        horizontal: true,
        fields: y_fields,
    },
];

impl QuadConsts {
    fn load(profile: Profile, q: &Quadrant) -> Result<QuadConsts, LayoutError> {
        let get = |name: &str| constant(profile, &format!("quadrant.{name}"));
        let padding = get("padding")?;
        let radius = get("point_radius")?;
        let mut consts = QuadConsts {
            width: get("width")?,
            height: get("height")?,
            pad_x: padding,
            pad_y: padding,
            title_band: get("title_band")?,
            x_band: get("axis_band_y")?,
            y_band: get("axis_band_x")?,
            title_pad_px: get("title_padding_px")?,
            title_font_px: get("title_font_px")?,
            x_pad_px: get("axis_label_padding_px")?,
            x_font_px: get("axis_font_px")?,
            y_pad_px: get("axis_label_padding_px")?,
            y_font_px: get("axis_font_px")?,
            radius_x: radius,
            radius_y: radius,
            text_pad: get("point_text_pad")?,
            label_font_px: get("label_font_px")?,
            point_font_px: get("point_font_px")?,
            top_pad: get("text_top_pad")?,
            edge: if profile == Profile::Cell {
                CELL_INSET
            } else {
                0
            },
        };
        consts.apply_geometry(profile, q);
        consts.apply_bands(profile, q);
        Ok(consts)
    }

    fn apply_geometry(&mut self, profile: Profile, q: &Quadrant) {
        let config = &q.config;
        if let Some(n) = config.get("chartWidth") {
            self.width = units_x(profile, *n);
        }
        if let Some(n) = config.get("chartHeight") {
            self.height = units_y(profile, *n);
        }
        if let Some(n) = config.get("quadrantPadding") {
            (self.pad_x, self.pad_y) = (units_x(profile, *n), units_y(profile, *n));
        }
        if let Some(n) = config.get("pointRadius") {
            (self.radius_x, self.radius_y) = (units_x(profile, *n), units_y(profile, *n));
        }
        if let Some(n) = config.get("pointTextPadding") {
            self.text_pad = units_x(profile, *n);
        }
    }

    fn apply_bands(&mut self, profile: Profile, q: &Quadrant) {
        for rule in &BAND_RULES {
            let pad = q.config.get(rule.pad_key).copied();
            let font = q.config.get(rule.font_key).copied();
            if pad.is_none() && font.is_none() {
                continue;
            }
            let (pad_px, font_px, band) = (rule.fields)(self);
            *pad_px = pad.unwrap_or(*pad_px);
            *font_px = font.unwrap_or(*font_px);
            let span = 2 * *pad_px + *font_px;
            *band = if rule.horizontal {
                units_x(profile, span)
            } else {
                units_y(profile, span)
            };
        }
    }
}

#[derive(Debug, Clone, Copy, Default)]
pub(super) struct Spot {
    pub x: i64,
    pub y: i64,
}

pub(super) struct QuadPlan<'a> {
    pub q: &'a Quadrant,
    pub profile: Profile,
    pub c: QuadConsts,
    pub cell: bool,
    font_family: bool,
    pub boxes: Vec<BoxSpec>,
    pub specs: Vec<LabelSpec>,
    pub texts: Vec<TextBox>,
    pub width: i64,
    pub height: i64,
    pub plot: Area,
    pub inner: [Area; TILE_COUNT],
    pub tiles: [Area; TILE_COUNT],
    pub centres: Vec<Spot>,
    pub radii: Vec<Spot>,
    pub point_boxes: Vec<Area>,
    pub taken: Vec<Area>,
    pub placed: Option<Placed>,
}

impl<'a> QuadPlan<'a> {
    fn new(
        q: &'a Quadrant,
        profile: Profile,
        font_family: bool,
    ) -> Result<QuadPlan<'a>, LayoutError> {
        let c = QuadConsts::load(profile, q)?;
        if q.points
            .iter()
            .any(|p| !(0..=SCALE).contains(&p.x) || !(0..=SCALE).contains(&p.y))
        {
            return Err(GeomError::Domain);
        }
        Ok(QuadPlan {
            q,
            profile,
            c,
            cell: profile == Profile::Cell,
            font_family,
            boxes: box_specs(q),
            specs: label_specs(q),
            texts: Vec::new(),
            width: 0,
            height: 0,
            plot: Area::default(),
            inner: [Area::default(); TILE_COUNT],
            tiles: [Area::default(); TILE_COUNT],
            centres: Vec::new(),
            radii: Vec::new(),
            point_boxes: Vec::new(),
            taken: Vec::new(),
            placed: None,
        })
    }

    pub(super) fn line_height(&self, role: Role, size: i32) -> i64 {
        if self.cell {
            return 1;
        }
        measure::round_half_up(
            i64::from(size) * UNITS_PER_PX * i64::from(role.line_height_px()),
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
                font_family: self.font_family,
            }
        }
    }

    pub(super) fn style_of(&self, spec: &LabelSpec) -> (Role, i32) {
        let px = |value: i64| i32::try_from(value).unwrap_or(i32::MAX);
        match spec.kind {
            LabelKind::Title => (Role::Title, px(self.c.title_font_px)),
            LabelKind::XLeft | LabelKind::XRight => (Role::Label, px(self.c.x_font_px)),
            LabelKind::YBottom | LabelKind::YTop => (Role::Label, px(self.c.y_font_px)),
            LabelKind::Tile => (Role::Label, px(self.c.label_font_px)),
            LabelKind::Point => (Role::Body, px(self.c.point_font_px)),
        }
    }

    pub(super) fn measure_at(&self, index: usize, target: i64) -> Result<TextBox, LayoutError> {
        let spec = &self.specs[index];
        let (role, size) = self.style_of(spec);
        let wrap = if target > 0 && target < i64::from(i32::MAX) {
            i32::try_from(target).unwrap_or(i32::MAX)
        } else {
            i32::MAX
        };
        let lines = measure::styled_lines(&spec.text, wrap, self.metric(role, size))?;
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
                    .map(|run| crate::scene::Run {
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

    pub(super) fn find(&self, kind: LabelKind) -> Option<usize> {
        self.specs.iter().position(|spec| spec.kind == kind)
    }

    pub(super) fn dump_boxes(&self) -> Vec<crate::scene::SceneBox> {
        dump_boxes(&self.boxes, self.placed.as_ref())
    }

    pub(super) fn dump_labels(&self) -> Vec<crate::scene::SceneLabel> {
        dump_labels(&self.specs, self.placed.as_ref())
    }

    pub(super) fn box_rect(&self, b: &BoxSpec) -> Area {
        match b.kind {
            BoxKind::Plot => self.plot,
            BoxKind::Tile => self.tiles[b.index],
            BoxKind::Point => self.point_boxes[b.index],
        }
    }
}

pub(crate) fn layout_quadrant(
    q: &Quadrant,
    options: &DumpOptions,
) -> Result<(Scene, bool), LayoutError> {
    let mut plan = QuadPlan::new(
        q,
        options.profile,
        crate::scene::has_font_family(&options.config),
    )?;
    plan.arrange()?;
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
    Ok((Scene::new(canvas, dump, groups), false))
}
