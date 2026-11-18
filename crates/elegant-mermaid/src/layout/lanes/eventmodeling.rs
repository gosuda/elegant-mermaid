//! The eventmodeling planner of the lanes family (`spec/layout/lanes.md`, Event modeling).
//!
//! Swimlanes are entity-type bands sorted by lane index. Frames take columns in
//! declaration order and overlap by `box_overlap`; a frame in the same lane as an earlier
//! one starts after it. Relations are straight when no other frame is in the way and
//! otherwise run through the corridors between lanes.

use crate::geom::{self, COORD_LIMIT, Point, Rect, Size};
use crate::layout::layered::LayoutError;
use crate::scene::{Group, Profile};

use super::Text;
use super::eventmodeling_constants::{EventConstants, load_event_constants};

#[derive(Debug, Clone)]
pub(crate) struct EventLane {
    pub id: String,
    pub index: i64,
    pub label: Option<Text>,
}

#[derive(Debug, Clone)]
pub(crate) struct EventFrame {
    pub id: String,
    pub lane: usize,
    pub category: String,
    pub name: Text,
    pub data: Option<Text>,
}

#[derive(Debug, Clone)]
pub(crate) struct EventRelation {
    pub id: String,
    pub from: usize,
    pub to: usize,
}

#[derive(Debug, Clone, Default)]
pub(crate) struct EventModelingInput {
    pub lanes: Vec<EventLane>,
    pub frames: Vec<EventFrame>,
    pub relations: Vec<EventRelation>,
}

#[derive(Debug)]
pub(crate) struct EventModelingResult {
    pub canvas: Size,
    pub lanes: Vec<Rect>,
    pub lane_labels: Vec<Rect>,
    pub frames: Vec<Rect>,
    pub routes: Vec<Vec<Point>>,
    pub groups: Vec<Group>,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(super) struct EventPoint {
    pub x: i64,
    pub y: i64,
}

#[derive(Debug, Clone, Copy, Default)]
pub(super) struct EventBox {
    pub x: i64,
    pub y: i64,
    pub w: i64,
    pub h: i64,
}

impl EventBox {
    pub(super) fn bottom(self) -> i64 {
        self.y + self.h
    }
}

pub(super) struct EventPlanner<'a> {
    pub input: &'a EventModelingInput,
    pub c: EventConstants,
    pub profile: Profile,
    pub order: Vec<usize>,
    pub rank: Vec<usize>,
    pub frames: Vec<EventBox>,
    pub lane_y: Vec<i64>,
    pub lane_h: Vec<i64>,
    pub corridors: Vec<i64>,
    pub gutter: i64,
    pub max_r: i64,
    pub routes: Vec<Vec<EventPoint>>,
}

pub(crate) fn event_modeling(
    input: &EventModelingInput,
    profile: Profile,
) -> Result<EventModelingResult, LayoutError> {
    let mut planner = EventPlanner {
        input,
        c: load_event_constants(profile)?,
        profile,
        order: Vec::new(),
        rank: Vec::new(),
        frames: Vec::new(),
        lane_y: Vec::new(),
        lane_h: Vec::new(),
        corridors: Vec::new(),
        gutter: 0,
        max_r: 0,
        routes: Vec::new(),
    };
    planner.validate()?;
    planner.rank_lanes();
    planner.place_columns();
    planner.place_rows();
    planner.route_relations()?;
    planner.result()
}

fn fit_point(point: EventPoint) -> Result<Point, LayoutError> {
    if point.x.abs() > COORD_LIMIT || point.y.abs() > COORD_LIMIT {
        return Err(LayoutError::Overflow);
    }
    Ok(Point {
        x: i32::try_from(point.x).map_err(|_| LayoutError::Overflow)?,
        y: i32::try_from(point.y).map_err(|_| LayoutError::Overflow)?,
    })
}

impl EventPlanner<'_> {
    fn validate(&self) -> Result<(), LayoutError> {
        let lanes = self.input.lanes.len();
        let frames = self.input.frames.len();
        if self.input.frames.iter().any(|frame| frame.lane >= lanes) {
            return Err(LayoutError::Domain);
        }
        let outside = |at: usize| at >= frames;
        if self
            .input
            .relations
            .iter()
            .any(|relation| outside(relation.from) || outside(relation.to))
        {
            return Err(LayoutError::Domain);
        }
        Ok(())
    }

    fn rank_lanes(&mut self) {
        let lanes = &self.input.lanes;
        let mut order: Vec<usize> = (0..lanes.len()).collect();
        order.sort_by_key(|&lane| (lanes[lane].index, lane));
        let mut rank = vec![0; order.len()];
        for (position, &lane) in order.iter().enumerate() {
            rank[lane] = position;
        }
        self.order = order;
        self.rank = rank;
    }

    fn frame_size(&self, frame: &EventFrame) -> (i64, i64) {
        let c = &self.c;
        let mut text_w = i64::from(frame.name.w);
        let mut text_h = i64::from(frame.name.h);
        if let Some(data) = &frame.data {
            text_w = text_w.max(i64::from(data.w));
            text_h += c.line_height + i64::from(data.h);
        }
        let w = text_w.clamp(c.box_min_width, c.box_max_width) + 2 * c.box_padding;
        let h = text_h.clamp(c.box_min_height, c.box_max_height) + 2 * c.box_padding;
        (w, h)
    }

    fn place_columns(&mut self) {
        let c = self.c;
        self.gutter = c.content_start_x;
        for lane in &self.input.lanes {
            if let Some(label) = &lane.label {
                self.gutter = self.gutter.max(2 * c.label_inset() + i64::from(label.w));
            }
        }
        let mut reach = self.gutter + c.box_overlap - c.box_padding;
        let mut lane_reach = vec![0_i64; self.input.lanes.len()];
        let mut frames = Vec::with_capacity(self.input.frames.len());
        for frame in &self.input.frames {
            let (w, h) = self.frame_size(frame);
            let x = (reach - c.box_overlap + c.box_padding).max(lane_reach[frame.lane]);
            frames.push(EventBox { x, y: 0, w, h });
            reach = x + w + c.box_padding;
            lane_reach[frame.lane] = reach;
            self.max_r = self.max_r.max(reach);
        }
        self.frames = frames;
    }

    fn place_rows(&mut self) {
        let c = self.c;
        let lanes = self.input.lanes.len();
        let mut tallest = vec![c.lane_min_height; lanes];
        for (lane, slot) in tallest.iter_mut().enumerate() {
            if let Some(label) = &self.input.lanes[lane].label {
                *slot = (*slot).max(i64::from(label.h));
            }
        }
        for (frame, placed) in self.input.frames.iter().zip(&self.frames) {
            tallest[frame.lane] = tallest[frame.lane].max(placed.h);
        }
        self.lane_y = vec![0; lanes];
        self.lane_h = vec![0; lanes];
        self.corridors = vec![0; lanes + 1];
        self.corridors[0] = geom::floor_div(c.lane_padding, 2);
        let mut y = 0;
        for (position, &lane) in self.order.iter().enumerate() {
            self.lane_y[lane] = y;
            self.lane_h[lane] = tallest[lane] + 2 * c.lane_padding;
            self.corridors[position + 1] = y + self.lane_h[lane] + geom::floor_div(c.lane_gap, 2);
            y += self.lane_h[lane] + c.lane_gap;
        }
        for (frame, placed) in self.input.frames.iter().zip(self.frames.iter_mut()) {
            placed.y = self.lane_y[frame.lane] + c.lane_padding;
        }
    }

    fn route_relations(&mut self) -> Result<(), LayoutError> {
        let mut routes = Vec::with_capacity(self.input.relations.len());
        for relation in &self.input.relations {
            routes.push(self.route(relation)?);
        }
        self.routes = routes;
        Ok(())
    }

    fn ports(&self, relation: &EventRelation) -> Ports {
        let (from, to) = (self.frames[relation.from], self.frames[relation.to]);
        let rank_from = self.rank[self.input.frames[relation.from].lane];
        let rank_to = self.rank[self.input.frames[relation.to].lane];
        let mut start = EventPoint {
            x: from.x + geom::floor_div(2 * from.w, 3),
            y: 0,
        };
        let mut end = EventPoint {
            x: to.x + geom::floor_div(to.w, 3),
            y: 0,
        };
        let corridors = &self.corridors;
        let (from_corridor, to_corridor) = match rank_from.cmp(&rank_to) {
            std::cmp::Ordering::Less => {
                (start.y, end.y) = (from.bottom(), to.y);
                (corridors[rank_from + 1], corridors[rank_to])
            }
            std::cmp::Ordering::Greater => {
                (start.y, end.y) = (from.y, to.bottom());
                (corridors[rank_from], corridors[rank_to + 1])
            }
            std::cmp::Ordering::Equal => {
                (start.y, end.y) = (from.y, to.y);
                (corridors[rank_from], corridors[rank_to])
            }
        };
        Ports {
            from: start,
            to: end,
            from_corridor,
            to_corridor,
            lane_difference: rank_from != rank_to,
        }
    }

    fn route(&self, relation: &EventRelation) -> Result<Vec<EventPoint>, LayoutError> {
        let ports = self.ports(relation);
        if self.profile == Profile::Vector && ports.lane_difference {
            let straight = [ports.from, ports.to];
            if !self.hits(&straight, relation)? {
                return Ok(straight.to_vec());
            }
        }
        let column = self.crossing(&ports, relation)?;
        let at = |x, y| EventPoint { x, y };
        Ok(tidy(&[
            ports.from,
            at(ports.from.x, ports.from_corridor),
            at(column, ports.from_corridor),
            at(column, ports.to_corridor),
            at(ports.to.x, ports.to_corridor),
            ports.to,
        ]))
    }

    fn crossing(&self, ports: &Ports, relation: &EventRelation) -> Result<i64, LayoutError> {
        for column in [ports.from.x, ports.to.x] {
            let run = [
                EventPoint {
                    x: column,
                    y: ports.from_corridor,
                },
                EventPoint {
                    x: column,
                    y: ports.to_corridor,
                },
            ];
            if !self.hits(&run, relation)? {
                return Ok(column);
            }
        }
        Ok(self.max_r)
    }

    fn hits(&self, points: &[EventPoint], relation: &EventRelation) -> Result<bool, LayoutError> {
        let path = points
            .iter()
            .map(|&point| fit_point(point))
            .collect::<Result<Vec<_>, _>>()?;
        for (index, frame) in self.frames.iter().enumerate() {
            if index == relation.from || index == relation.to {
                continue;
            }
            if geom::polyline_hits_rect(&path, fit_rect(*frame)?)? {
                return Ok(true);
            }
        }
        Ok(false)
    }
}

struct Ports {
    from: EventPoint,
    to: EventPoint,
    from_corridor: i64,
    to_corridor: i64,
    lane_difference: bool,
}

fn fit_rect(area: EventBox) -> Result<Rect, LayoutError> {
    let widest = [
        area.x,
        area.y,
        area.w,
        area.h,
        area.x + area.w,
        area.bottom(),
    ]
    .into_iter()
    .map(i64::abs)
    .max()
    .unwrap_or(0);
    if widest > COORD_LIMIT {
        return Err(LayoutError::Overflow);
    }
    let narrow = |value: i64| i32::try_from(value).map_err(|_| LayoutError::Overflow);
    Ok(Rect {
        x: narrow(area.x)?,
        y: narrow(area.y)?,
        w: narrow(area.w)?,
        h: narrow(area.h)?,
    })
}

fn tidy(points: &[EventPoint]) -> Vec<EventPoint> {
    let mut out: Vec<EventPoint> = Vec::with_capacity(points.len());
    for &point in points {
        if out.last() == Some(&point) {
            continue;
        }
        while let [.., a, b] = out[..] {
            if !straight_through(a, b, point) {
                break;
            }
            out.pop();
        }
        out.push(point);
    }
    out
}

fn straight_through(a: EventPoint, b: EventPoint, c: EventPoint) -> bool {
    let cross = (b.x - a.x) * (c.y - b.y) - (b.y - a.y) * (c.x - b.x);
    let dot = (b.x - a.x) * (c.x - b.x) + (b.y - a.y) * (c.y - b.y);
    cross == 0 && dot > 0
}
