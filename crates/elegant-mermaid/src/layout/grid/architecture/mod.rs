//! The architecture entry of the grid family (`spec/layout/grid.md`, Architecture).
//!
//! Nodes occupy cells of an integer grid. Each group level is arranged on its own by a
//! breadth-first walk over the edges lifted to that level, and a placed group is one unit
//! whose frame is a rigid rectangle. Ports, gutter routes, and edge labels follow.

mod place;
mod route;

use crate::geom::{self, GeomError, Point, Rect, Size};
use crate::layout::input::RouteSide;

#[derive(Debug, Clone, Copy)]
pub(crate) struct ArchNode {
    pub parent: Option<usize>,
    pub junction: bool,
    pub icon: Size,
    pub label: Size,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct ArchGroup {
    pub parent: Option<usize>,
    pub title: Size,
    pub icon: bool,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct ArchEdge {
    pub from: usize,
    pub to: usize,
    pub from_side: RouteSide,
    pub to_side: RouteSide,
    pub label: Size,
}

#[derive(Debug, Clone)]
pub(crate) struct ArchAlign {
    pub column: bool,
    pub members: Vec<usize>,
}

#[derive(Debug, Clone, Default)]
pub(crate) struct ArchInput {
    pub nodes: Vec<ArchNode>,
    pub groups: Vec<ArchGroup>,
    pub edges: Vec<ArchEdge>,
    pub aligns: Vec<ArchAlign>,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct ArchParams {
    pub pitch_x: i32,
    pub pitch_y: i32,
    pub label_wrap: i32,
    pub icon_w: i32,
    pub icon_h: i32,
    pub padding: i32,
    pub line_height: i32,
    pub badge: i32,
    pub inset: i32,
    pub label_gap: i32,
    pub thickness: i32,
    pub margin: i32,
    pub gutter: i32,
    pub fuel: i32,
    pub ring_cap: i32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ArchLayout {
    pub boxes: Vec<Rect>,
    pub icons: Vec<Rect>,
    pub labels: Vec<Rect>,
    pub frames: Vec<Rect>,
    pub titles: Vec<Rect>,
    pub group_icons: Vec<Rect>,
    pub routes: Vec<Vec<Point>>,
    pub edge_labels: Vec<Rect>,
    pub canvas: Size,
    pub budget: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
struct Cell {
    x: i64,
    y: i64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Pt {
    x: i64,
    y: i64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
struct Area {
    x0: i64,
    y0: i64,
    x1: i64,
    y1: i64,
}

const IDENTITY: i64 = 1 << 60;

const EMPTY: Area = Area {
    x0: IDENTITY,
    y0: IDENTITY,
    x1: -IDENTITY,
    y1: -IDENTITY,
};

impl Area {
    fn overlaps(self, o: Area) -> bool {
        self.x0.max(o.x0) < self.x1.min(o.x1) && self.y0.max(o.y0) < self.y1.min(o.y1)
    }

    fn union(self, o: Area) -> Area {
        Area {
            x0: self.x0.min(o.x0),
            y0: self.y0.min(o.y0),
            x1: self.x1.max(o.x1),
            y1: self.y1.max(o.y1),
        }
    }

    fn strictly_inside(self, o: Area) -> bool {
        self.x0 > o.x0 && self.x1 < o.x1 && self.y0 > o.y0 && self.y1 < o.y1
    }

    fn inflate(self, d: i64) -> Area {
        Area {
            x0: self.x0 - d,
            y0: self.y0 - d,
            x1: self.x1 + d,
            y1: self.y1 + d,
        }
    }

    fn shift(self, dx: i64, dy: i64) -> Area {
        Area {
            x0: self.x0 + dx,
            y0: self.y0 + dy,
            x1: self.x1 + dx,
            y1: self.y1 + dy,
        }
    }
}

fn sized(x: i64, y: i64, s: Size) -> Area {
    Area {
        x0: x,
        y0: y,
        x1: x + i64::from(s.w),
        y1: y + i64::from(s.h),
    }
}

fn ceil_div(a: i64, d: i64) -> i64 {
    geom::floor_div(a + d - 1, d)
}

fn slot(parent: Option<usize>) -> usize {
    parent.map_or(0, |g| g + 1)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Unit {
    Node(usize),
    Group(usize),
}

#[derive(Debug, Clone, Copy)]
struct LiftedEdge {
    a: Unit,
    b: Unit,
    side_a: RouteSide,
    side_b: RouteSide,
}

struct Builder<'a> {
    input: &'a ArchInput,
    p: ArchParams,
    real: usize,
    total: usize,
    parent: Vec<Option<usize>>,
    px: i64,
    py: i64,
    top: i64,
    shift: i64,
    child_groups: Vec<Vec<usize>>,
    child_nodes: Vec<Vec<usize>>,
    first_node: Vec<usize>,
    aligns_of: Vec<Vec<usize>>,
    lifted: Vec<Vec<LiftedEdge>>,
    local: Vec<Cell>,
    local_group: Vec<Cell>,
    rel: Vec<Area>,
    pos: Vec<Cell>,
    frame: Vec<Area>,
    pops: i64,
    budget: bool,
    boxes: Vec<Area>,
    icons: Vec<Area>,
    labels: Vec<Area>,
    titles: Vec<Area>,
    badges: Vec<Area>,
    routes: Vec<Vec<Pt>>,
}

pub(crate) fn architecture(input: &ArchInput, params: ArchParams) -> Result<ArchLayout, GeomError> {
    let mut b = Builder::new(input, params);
    b.prepare()?;
    b.place();
    b.geometry();
    b.route();
    b.finish()
}

impl<'a> Builder<'a> {
    fn new(input: &'a ArchInput, p: ArchParams) -> Self {
        Self {
            input,
            p,
            real: 0,
            total: 0,
            parent: Vec::new(),
            px: 0,
            py: 0,
            top: 0,
            shift: 0,
            child_groups: Vec::new(),
            child_nodes: Vec::new(),
            first_node: Vec::new(),
            aligns_of: Vec::new(),
            lifted: Vec::new(),
            local: Vec::new(),
            local_group: Vec::new(),
            rel: Vec::new(),
            pos: Vec::new(),
            frame: Vec::new(),
            pops: 0,
            budget: false,
            boxes: Vec::new(),
            icons: Vec::new(),
            labels: Vec::new(),
            titles: Vec::new(),
            badges: Vec::new(),
            routes: Vec::new(),
        }
    }

    fn prepare(&mut self) -> Result<(), GeomError> {
        self.validate()?;
        self.virtualise();
        self.index();
        self.pitch();
        Ok(())
    }

    fn validate(&self) -> Result<(), GeomError> {
        let p = &self.p;
        let positive = [p.pitch_x, p.pitch_y, p.icon_w, p.icon_h];
        let non_negative = [
            p.padding,
            p.line_height,
            p.badge,
            p.inset,
            p.label_gap,
            p.thickness,
            p.margin,
            p.fuel,
            p.ring_cap,
        ];
        if positive.iter().any(|v| *v <= 0)
            || non_negative.iter().any(|v| *v < 0)
            || !(p.gutter == 0 || p.gutter == 1)
        {
            return Err(GeomError::Domain);
        }
        let input = self.input;
        let groups_ok = input.groups.iter().enumerate().all(|(i, g)| {
            g.parent.is_none_or(|parent| parent < i) && g.title.w >= 0 && g.title.h >= 0
        });
        let nodes_ok = input.nodes.iter().all(|n| {
            n.parent.is_none_or(|parent| parent < input.groups.len())
                && n.icon.w > 0
                && n.icon.h > 0
                && n.label.w >= 0
                && n.label.h >= 0
        });
        let count = input.nodes.len();
        let edges_ok = input
            .edges
            .iter()
            .all(|e| e.from < count && e.to < count && e.label.w >= 0 && e.label.h >= 0);
        let aligns_ok = input
            .aligns
            .iter()
            .all(|a| a.members.iter().all(|m| *m < count));
        if groups_ok && nodes_ok && edges_ok && aligns_ok {
            Ok(())
        } else {
            Err(GeomError::Domain)
        }
    }

    fn virtualise(&mut self) {
        let input = self.input;
        self.real = input.nodes.len();
        let mut used = vec![false; input.groups.len()];
        self.parent = input.nodes.iter().map(|n| n.parent).collect();
        for parent in input
            .nodes
            .iter()
            .map(|n| n.parent)
            .chain(input.groups.iter().map(|g| g.parent))
            .flatten()
        {
            used[parent] = true;
        }
        for (g, taken) in used.iter().enumerate() {
            if !taken {
                self.parent.push(Some(g));
            }
        }
        self.total = self.parent.len();
    }

    fn index(&mut self) {
        let input = self.input;
        let slots = input.groups.len() + 1;
        self.child_groups = vec![Vec::new(); slots];
        self.child_nodes = vec![Vec::new(); slots];
        for (g, entry) in input.groups.iter().enumerate() {
            self.child_groups[slot(entry.parent)].push(g);
        }
        for (v, parent) in self.parent.iter().enumerate() {
            self.child_nodes[slot(*parent)].push(v);
        }
        self.first_node = vec![0; input.groups.len()];
        for g in (0..input.groups.len()).rev() {
            let nodes = self.child_nodes[g + 1].iter().copied();
            let groups = self.child_groups[g + 1].iter().map(|s| self.first_node[*s]);
            self.first_node[g] = nodes.chain(groups).fold(self.total + g, usize::min);
        }
        self.aligns_of = vec![Vec::new(); self.total];
        for (i, a) in input.aligns.iter().enumerate() {
            for m in &a.members {
                self.aligns_of[*m].push(i);
            }
        }
    }

    fn pitch(&mut self) {
        let p = self.p;
        let (iw, ih) = (i64::from(p.icon_w), i64::from(p.icon_h));
        self.shift = i64::from(p.gutter);
        let mut label_w = 0i64;
        let mut label_h = 0i64;
        for n in &self.input.nodes {
            label_w = label_w.max(i64::from(n.label.w));
            label_h = label_h.max(i64::from(n.label.h));
        }
        let mut edge_w = 0i64;
        let mut edge_h = 0i64;
        for e in &self.input.edges {
            edge_w = edge_w.max(i64::from(e.label.w));
            edge_h = edge_h.max(i64::from(e.label.h));
        }
        let (pitch_x, pitch_y) = (i64::from(p.pitch_x), i64::from(p.pitch_y));
        let thickness = i64::from(p.thickness);
        let gap = i64::from(p.label_gap);
        let mut px = pitch_x
            .max(iw + self.shift)
            .max(label_w + pitch_x - i64::from(p.label_wrap));
        if edge_w > 0 {
            px = px.max(iw.max(label_w) + self.shift + 2 * (thickness + gap + edge_w));
        }
        let top0 = geom::floor_div(pitch_y - ih, 2).max(0);
        let mut top = top0;
        if edge_h > 0 {
            top = top.max(thickness + gap + edge_h);
        }
        let mut tail = (pitch_y - top0 - ih).max(0);
        if label_h > 0 {
            tail = label_h
                + thickness
                + self
                    .shift
                    .max((pitch_y - top0 - ih - i64::from(p.line_height)).max(0));
        }
        self.px = px;
        self.top = top;
        self.py = pitch_y.max(top + ih + tail);
    }

    fn frame_of(&self, g: usize, inner: Area) -> Area {
        let entry = self.input.groups[g];
        let pad = i64::from(self.p.padding);
        let inset = i64::from(self.p.inset);
        let line = i64::from(self.p.line_height);
        let badge = i64::from(self.p.badge);
        let mut head = i64::from(entry.title.h);
        let mut need = 0i64;
        if entry.title.w > 0 || entry.icon {
            need = 2 * inset + i64::from(entry.title.w);
        }
        if entry.icon {
            head = head.max(badge);
            need += badge + inset;
        }
        let mut f = Area {
            x0: inner.x0 - pad,
            y0: inner.y0 - (pad + line).max(2 * inset + head),
            x1: inner.x1 + pad,
            y1: inner.y1 + pad,
        };
        f.x1 = f.x1.max(f.x0 + need);
        f
    }
}

#[cfg(test)]
mod tests;
