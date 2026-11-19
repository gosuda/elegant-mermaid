//! The venn plan: measured labels, circle geometry, label stacks, and the phase order of
//! the layout (`spec/layout/charts.md`). The kind is vector-only: its text output is the
//! braille raster of the vector scene.

mod geometry;
mod scene;

use std::collections::BTreeMap;

use crate::geom::{GeomError, Rect, Size, floor_div, isqrt};
use crate::measure::{self, Metric, Role};
use crate::scene::{
    BoxRole, Direction, Dump, DumpOptions, DumpValue, Profile, Run, Scene, SceneBox, SceneLabel,
};

use super::scale::clamp;
use super::xy_axis::check_magnitude;
use super::{Area, LayoutError, Skeleton, ZERO_RECT, constant, to_i32};

use geometry::{Circle, Steps};

const KIND: &str = "venn";
const ROOT_ID: &str = "venn";
const TITLE_ID: &str = "title";
const MAX_SETS: usize = 3;
const PIXEL_UNITS: i64 = 64;
const RADIUS_PARTS: i64 = 4;

#[derive(Debug, Clone, Default)]
pub(crate) struct VennSet {
    pub label: String,
    pub size: i64,
    pub texts: Vec<String>,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct VennOverlap {
    pub a: usize,
    pub b: usize,
    pub value: i64,
}

#[derive(Debug, Clone, Default)]
pub(crate) struct VennRegion {
    pub sets: Vec<usize>,
    pub label: String,
    pub texts: Vec<String>,
}

#[derive(Debug, Clone, Default)]
pub(crate) struct Payload {
    pub title: String,
    pub config: BTreeMap<String, DumpValue>,
    pub sets: Vec<VennSet>,
    pub overlaps: Vec<VennOverlap>,
    pub regions: Vec<VennRegion>,
}

impl Payload {
    fn integer(&self, key: &str) -> Option<i64> {
        match self.config.get(key) {
            Some(DumpValue::Integer(value)) => Some(*value),
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
struct Line {
    text: String,
    runs: Vec<Run>,
}

#[derive(Debug, Clone, Default)]
struct TextBox {
    lines: Vec<Line>,
    w: i64,
    h: i64,
}

#[derive(Debug, Clone)]
struct Item {
    id: String,
    owner: String,
    text: String,
    title: bool,
    text_box: TextBox,
    rect: Rect,
}

#[derive(Debug, Clone)]
struct VennBox {
    id: String,
    parent: String,
    set: Option<usize>,
    members: Vec<usize>,
    items: Vec<usize>,
    rect: Rect,
}

struct Plan<'a> {
    v: &'a Payload,
    radius: i64,
    steps: Steps,
    width: i64,
    height: i64,
    band: i64,
    items: Vec<Item>,
    boxes: Vec<VennBox>,
    circles: Vec<Circle>,
    laid_out: bool,
}

fn set_id(i: usize) -> String {
    format!("set{i}")
}

fn region_id(k: usize) -> String {
    format!("region{k}")
}

fn role_of(title: bool) -> Role {
    if title { Role::Title } else { Role::Label }
}

impl<'a> Plan<'a> {
    fn new(chart: &'a Payload) -> Result<Plan<'a>, LayoutError> {
        if chart.sets.len() > MAX_SETS {
            return Err(GeomError::Domain);
        }
        for set in &chart.sets {
            check_magnitude(&[set.size])?;
        }
        for overlap in &chart.overlaps {
            check_magnitude(&[overlap.value])?;
        }
        let mut plan = Plan {
            v: chart,
            radius: 0,
            steps: Steps {
                acos: 0,
                bisect: 0,
                sqrt3_half: 0,
            },
            width: 0,
            height: 0,
            band: 0,
            items: Vec::new(),
            boxes: Vec::new(),
            circles: Vec::new(),
            laid_out: false,
        };
        let mut root = blank_box(ROOT_ID, "", None);
        if !chart.title.is_empty() {
            root.items.push(plan.items.len());
            plan.items.push(Item {
                id: TITLE_ID.to_owned(),
                owner: ROOT_ID.to_owned(),
                text: chart.title.clone(),
                title: true,
                text_box: TextBox::default(),
                rect: ZERO_RECT,
            });
        }
        plan.boxes.push(root);
        for (i, set) in chart.sets.iter().enumerate() {
            let b = blank_box(&set_id(i), ROOT_ID, Some(i));
            plan.add_box(b, &set.label, &set.texts);
        }
        for (k, region) in chart.regions.iter().enumerate() {
            let mut b = blank_box(&region_id(k), ROOT_ID, None);
            b.members.clone_from(&region.sets);
            plan.add_box(b, &region.label, &region.texts);
        }
        Ok(plan)
    }

    fn add_box(&mut self, mut b: VennBox, label: &str, texts: &[String]) {
        if !label.is_empty() {
            b.items.push(self.items.len());
            self.items.push(Item {
                id: format!("{}.label", b.id),
                owner: b.id.clone(),
                text: label.to_owned(),
                title: false,
                text_box: TextBox::default(),
                rect: ZERO_RECT,
            });
        }
        for (j, text) in texts.iter().enumerate() {
            b.items.push(self.items.len());
            self.items.push(Item {
                id: format!("{}.t{j}", b.id),
                owner: b.id.clone(),
                text: text.clone(),
                title: false,
                text_box: TextBox::default(),
                rect: ZERO_RECT,
            });
        }
        self.boxes.push(b);
    }

    fn dump_boxes(&self) -> Vec<SceneBox> {
        self.boxes
            .iter()
            .map(|b| SceneBox {
                id: b.id.clone(),
                role: BoxRole::Node,
                rect: if self.laid_out { b.rect } else { ZERO_RECT },
                parent: b.parent.clone(),
                exclusive: false,
            })
            .collect()
    }

    fn dump_labels(&self) -> Vec<SceneLabel> {
        self.items
            .iter()
            .map(|it| SceneLabel {
                id: it.id.clone(),
                owner: it.owner.clone(),
                text: it.text.clone(),
                rect: if self.laid_out { it.rect } else { ZERO_RECT },
                lines: if self.laid_out {
                    it.text_box.lines.iter().map(|l| l.text.clone()).collect()
                } else {
                    Vec::new()
                },
            })
            .collect()
    }

    fn configure(&mut self) -> Result<(), LayoutError> {
        let get = |name: &str| constant(Profile::Vector, &format!("venn.{name}"));
        let mut width = get("width")?;
        let mut height = get("height")?;
        if let Some(n) = self.v.integer("width") {
            width = n * PIXEL_UNITS;
        }
        if let Some(n) = self.v.integer("height") {
            height = n * PIXEL_UNITS;
        }
        self.radius = floor_div(width.min(height), RADIUS_PARTS * PIXEL_UNITS) * PIXEL_UNITS;
        self.steps = Steps {
            acos: usize::try_from(get("acos_iterations")?).map_err(|_| GeomError::Domain)?,
            bisect: usize::try_from(get("bisect_iterations")?).map_err(|_| GeomError::Domain)?,
            sqrt3_half: get("sqrt3_half_q15")?,
        };
        Ok(())
    }

    fn measure_all(&mut self) -> Result<(), LayoutError> {
        let wrap = i32::try_from(self.width).unwrap_or(i32::MAX);
        for item in &mut self.items {
            let role = role_of(item.title);
            let lines = measure::styled_lines(&item.text, wrap, Metric::for_role(role))?;
            let widest = lines
                .iter()
                .map(|line| i64::from(line.width))
                .max()
                .unwrap_or(0);
            let count = i64::try_from(lines.len()).unwrap_or(i64::MAX);
            item.text_box = TextBox {
                w: widest,
                h: count * i64::from(role.line_height_px()) * PIXEL_UNITS,
                lines: lines
                    .iter()
                    .map(|line| Line {
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
                    .collect(),
            };
        }
        Ok(())
    }

    fn overlap(&self) -> i64 {
        self.v
            .overlaps
            .iter()
            .filter(|o| o.a == 0 && o.b == 1)
            .map(|o| o.value)
            .next_back()
            .unwrap_or(0)
    }

    fn arrange(&mut self) -> Result<(), LayoutError> {
        let sizes: Vec<i64> = self.v.sets.iter().map(|s| s.size).collect();
        let largest = geometry::largest(&sizes);
        let radii = geometry::radii(&sizes, largest, self.radius)?;
        let distance = match radii.as_slice() {
            [first, second] => geometry::distance(
                *first,
                *second,
                geometry::target(self.overlap(), largest, self.radius),
                self.steps,
            ),
            _ => 0,
        };
        self.circles = geometry::centres(&radii, self.radius, distance, self.steps);
        for circle in &mut self.circles {
            circle.y += self.band;
        }
        Ok(())
    }

    fn fit(&self, r: Area) -> Area {
        Area {
            x: clamp(r.x, 0, (self.width - r.w).max(0)),
            y: clamp(r.y, 0, (self.height - r.h).max(0)),
            ..r
        }
    }

    fn clear_earlier_labels(&self, mut r: Area, id: usize) -> Area {
        r.y = r.y.max(self.band);
        for _ in 0..id {
            let mut next = r.y;
            for earlier in &self.items[..id] {
                let b = earlier.rect;
                if r.w > 0
                    && r.h > 0
                    && b.w > 0
                    && b.h > 0
                    && r.x < i64::from(b.x) + i64::from(b.w)
                    && i64::from(b.x) < r.x + r.w
                    && r.y < i64::from(b.y) + i64::from(b.h)
                    && i64::from(b.y) < r.y + r.h
                {
                    next = next.max(i64::from(b.y) + i64::from(b.h));
                    break;
                }
            }
            if next == r.y {
                break;
            }
            r.y = next;
        }
        r
    }

    fn anchor(&self, b: &VennBox) -> Result<(i64, i64), LayoutError> {
        if let Some(set) = b.set {
            return self.set_anchor(set);
        }
        let (mut sx, mut sy) = (0i64, 0i64);
        for i in &b.members {
            sx += self.circles[*i].x;
            sy += self.circles[*i].y;
        }
        let n = i64::try_from(b.members.len()).unwrap_or(i64::MAX);
        Ok((floor_div(sx, n), floor_div(sy, n)))
    }

    fn set_anchor(&self, set: usize) -> Result<(i64, i64), LayoutError> {
        let c = self.circles[set];
        if self.circles.len() == 1 {
            return Ok((c.x, c.y));
        }
        let (mut sx, mut sy) = (0i64, 0i64);
        let others = self
            .circles
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != set)
            .map(|(_, o)| o);
        for o in others {
            sx += o.x;
            sy += o.y;
        }
        let n = i64::try_from(self.circles.len() - 1).unwrap_or(i64::MAX);
        let (dx, dy) = (c.x - floor_div(sx, n), c.y - floor_div(sy, n));
        let length = isqrt(dx * dx + dy * dy)?;
        if length == 0 {
            return Ok((c.x, c.y));
        }
        Ok((
            c.x + floor_div(dx * c.r, 2 * length),
            c.y + floor_div(dy * c.r, 2 * length),
        ))
    }

    fn stack(&mut self, b: usize) -> Result<Area, LayoutError> {
        let (ax, ay) = self.anchor(&self.boxes[b])?;
        let ids = self.boxes[b].items.clone();
        let total: i64 = ids.iter().map(|id| self.items[*id].text_box.h).sum();
        let mut top = ay - floor_div(total, 2);
        let (mut lo_x, mut lo_y, mut hi_x, mut hi_y) = (ax, ay, ax, ay);
        for id in ids {
            let (w, h) = (self.items[id].text_box.w, self.items[id].text_box.h);
            let r =
                self.clear_earlier_labels(self.fit(Area::new(ax - floor_div(w, 2), top, w, h)), id);
            self.items[id].rect = r.to_rect()?;
            top = r.y + h;
            lo_x = lo_x.min(r.x);
            lo_y = lo_y.min(r.y);
            hi_x = hi_x.max(r.x + r.w);
            hi_y = hi_y.max(r.y + r.h);
        }
        Ok(Area::new(lo_x, lo_y, hi_x - lo_x, hi_y - lo_y))
    }

    fn place_title(&mut self) -> Result<(), LayoutError> {
        let width = self.width;
        let Some(index) = self.items.iter().position(|it| it.title) else {
            return Ok(());
        };
        let (w, h) = (self.items[index].text_box.w, self.items[index].text_box.h);
        let r = self.fit(Area::new(floor_div(width - w, 2), 0, w, h));
        self.items[index].rect = r.to_rect()?;
        Ok(())
    }

    fn box_rect(&mut self, b: usize) -> Result<Area, LayoutError> {
        if self.boxes[b].id == ROOT_ID {
            return Ok(Area::new(0, 0, self.width, self.height));
        }
        let labels = self.stack(b)?;
        let Some(set) = self.boxes[b].set else {
            return Ok(labels);
        };
        let c = self.circles[set];
        Ok(Area::new(c.x - c.r, c.y - c.r, 2 * c.r, 2 * c.r))
    }

    fn place(&mut self) -> Result<(), LayoutError> {
        for item in &self.items {
            self.width = self.width.max(item.text_box.w);
        }
        self.place_title()?;
        for i in 0..self.boxes.len() {
            let r = self.box_rect(i)?;
            self.boxes[i].rect = r.to_rect()?;
        }
        for b in &self.boxes {
            self.width = self.width.max(i64::from(b.rect.x) + i64::from(b.rect.w));
            self.height = self.height.max(i64::from(b.rect.y) + i64::from(b.rect.h));
        }
        for item in &self.items {
            self.width = self
                .width
                .max(i64::from(item.rect.x) + i64::from(item.rect.w));
            self.height = self
                .height
                .max(i64::from(item.rect.y) + i64::from(item.rect.h));
        }
        self.boxes[0].rect = Area::new(0, 0, self.width, self.height).to_rect()?;
        self.laid_out = true;
        Ok(())
    }

    fn title_band(&self) -> i64 {
        self.items
            .iter()
            .find(|it| it.title)
            .map_or(0, |it| it.text_box.h)
    }
}

fn blank_box(id: &str, parent: &str, set: Option<usize>) -> VennBox {
    VennBox {
        id: id.to_owned(),
        parent: parent.to_owned(),
        set,
        members: Vec::new(),
        items: Vec::new(),
        rect: ZERO_RECT,
    }
}

pub(crate) fn layout_venn(
    chart: &Payload,
    options: &DumpOptions,
) -> Result<(Scene, bool), LayoutError> {
    let mut plan = Plan::new(chart)?;
    plan.configure()?;
    plan.width = 4 * plan.radius;
    plan.measure_all()?;
    plan.band = plan.title_band();
    plan.height = plan.width + plan.band;
    plan.arrange()?;
    plan.place()?;
    let canvas = Size {
        w: to_i32(plan.width)?,
        h: to_i32(plan.height)?,
    };
    let mut dump_options = options.clone();
    dump_options.profile = Profile::Vector;
    dump_options.direction = Direction::Tb;
    let mut dump = Dump::new(KIND, dump_options);
    dump.boxes = plan.dump_boxes();
    dump.labels = plan.dump_labels();
    let groups = plan.groups()?;
    Ok((Scene::new(canvas, dump, groups), false))
}

pub(crate) fn skeleton(chart: &Payload) -> Result<Skeleton, LayoutError> {
    let plan = Plan::new(chart)?;
    Ok(Skeleton {
        boxes: plan.dump_boxes(),
        labels: plan.dump_labels(),
    })
}
