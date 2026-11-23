//! The cynefin plan: measured texts, the quadrant stacks, the confusion centre, the
//! routes, and the entry that returns the scene (`spec/layout/charts.md`).

use std::collections::BTreeMap;

use crate::geom::{Size, floor_div};
use crate::measure::Role;
use crate::scene::{Align, Direction, Dump, DumpOptions, Profile, Scene};

use super::cynefin_consts::{Consts, load_consts};
use super::cynefin_spec::{
    CONFUSION, Cynefin, KIND, RouteSpec, cynefin_routes, domain_title, normalized_domains,
};
use super::cynefin_stack::{CurvePoint, DomainPlan};
use super::cynefin_text::{TextBox, TextSpec, bottom, right};
use super::{Area, LayoutError, to_i32};

#[derive(Debug, Clone)]
pub(crate) struct PlacedLabel {
    pub at: Area,
    pub align: Align,
    pub text: TextBox,
}

pub(crate) struct CynefinPlan<'a> {
    pub chart: &'a Cynefin,
    pub profile: Profile,
    pub c: Consts,
    pub title: TextBox,
    pub title_at: Area,
    pub title_shown: bool,
    pub domains: Vec<DomainPlan>,
    pub routes: Vec<RouteSpec>,
    pub route_boxes: Vec<TextBox>,
    pub paths: Vec<Vec<CurvePoint>>,
    pub labels: BTreeMap<String, PlacedLabel>,
    pub extents: Vec<Area>,
    pub cx: i64,
    pub cy: i64,
    pub width: i64,
    pub height: i64,
}

impl<'a> CynefinPlan<'a> {
    pub(crate) fn new(chart: &'a Cynefin, profile: Profile) -> Result<Self, LayoutError> {
        let c = load_consts(profile, chart)?;
        let mut plan = CynefinPlan {
            chart,
            profile,
            c,
            title: TextBox::default(),
            title_at: Area::default(),
            title_shown: !chart.title.is_empty(),
            domains: Vec::new(),
            routes: cynefin_routes(chart),
            route_boxes: Vec::new(),
            paths: Vec::new(),
            labels: BTreeMap::new(),
            extents: Vec::new(),
            cx: floor_div(c.width, 2),
            cy: floor_div(c.height, 2),
            width: 0,
            height: 0,
        };
        plan.measure()?;
        Ok(plan)
    }

    fn spec(&self, role: Role) -> TextSpec {
        TextSpec { font_family: crate::scene::has_font_family(&self.chart.config), ..TextSpec::of_role(self.profile, role) }
    }

    fn measure(&mut self) -> Result<(), LayoutError> {
        if self.title_shown {
            self.title = self.spec(Role::Title).measure(&self.chart.title)?;
        }
        for d in normalized_domains(self.chart) {
            let title = self.spec(Role::Label).measure(&domain_title(&d.name))?;
            let mut items = Vec::with_capacity(d.items.len());
            for item in &d.items {
                items.push(self.spec(Role::Body).measure(item)?);
            }
            self.domains.push(DomainPlan::new(d.name, title, items));
        }
        for r in &self.routes {
            self.route_boxes
                .push(self.spec(Role::Body).measure(&r.label)?);
        }
        Ok(())
    }

    pub(crate) fn quadrant(&self, name: &str) -> Area {
        let (hw, hh) = (floor_div(self.c.width, 2), floor_div(self.c.height, 2));
        match name {
            "complex" => Area::new(0, 0, hw, hh),
            "complicated" => Area::new(hw, 0, self.c.width - hw, hh),
            "clear" => Area::new(hw, hh, self.c.width - hw, self.c.height - hh),
            _ => Area::new(0, hh, hw, self.c.height - hh),
        }
    }

    fn stack_origin(&self, d: &DomainPlan) -> (i64, i64) {
        let c = &self.c;
        if d.name == CONFUSION {
            return (self.cx, c.box_pad.max(self.cy - floor_div(d.height(c), 2)));
        }
        let q = self.quadrant(&d.name);
        let cx = q.x + floor_div(q.w, 2);
        let mut top = q.y + c.pad;
        if q.y == 0 && self.title_shown {
            top = q.y + 2 * c.pad + self.title.h;
        }
        (cx, top)
    }

    pub(crate) fn place(&mut self) {
        if self.title_shown {
            let half = floor_div(self.title.w, 2);
            self.title_at = Area::new(
                (self.cx - half).max(0),
                self.c.pad,
                self.title.w,
                self.title.h,
            );
        }
        for i in 0..self.domains.len() {
            let (lo, hi) = self.domains[i].span(&self.c);
            let (cx, top) = self.stack_origin(&self.domains[i]);
            let centre = lo.max(cx.min(self.c.width - hi));
            let consts = self.c;
            self.domains[i].place(&consts, centre, top);
        }
        self.place_labels();
        self.route();
        self.fit_canvas();
    }

    pub(crate) fn domain_index(&self, name: &str) -> usize {
        self.domains
            .iter()
            .position(|d| d.name == name)
            .unwrap_or(0)
    }

    fn fit_canvas(&mut self) {
        let (mut width, mut height) = (self.c.width, self.c.height);
        let mut grow = |area: Area| {
            width = width.max(right(area));
            height = height.max(bottom(area));
        };
        self.extents.iter().for_each(|area| grow(*area));
        self.domains.iter().for_each(|d| grow(d.bounds));
        for point in self.paths.iter().flatten() {
            grow(Area::new(point.x, point.y, 0, 0));
        }
        (self.width, self.height) = (width, height);
    }

    pub(crate) fn frame_area(&self) -> Area {
        Area::new(0, 0, self.width, self.height)
    }

    pub(crate) fn ellipse(&self) -> (i64, i64) {
        (
            floor_div(self.c.width * self.c.confusion, 1000),
            floor_div(self.c.height * self.c.confusion, 1000),
        )
    }
}

pub fn layout_cynefin(
    chart: &Cynefin,
    options: &DumpOptions,
) -> Result<(Scene, bool), LayoutError> {
    let mut plan = CynefinPlan::new(chart, options.profile)?;
    plan.place();
    let canvas = Size {
        w: to_i32(plan.width)?,
        h: to_i32(plan.height)?,
    };
    let mut dump_options = options.clone();
    dump_options.direction = Direction::Tb;
    let mut dump = Dump::new(KIND, dump_options);
    let frame = plan.dump_frame()?;
    (dump.boxes, dump.routes, dump.labels) = (frame.boxes, frame.routes, frame.labels);
    let groups = plan.groups()?;
    Ok((Scene::new(canvas, dump, groups), false))
}
