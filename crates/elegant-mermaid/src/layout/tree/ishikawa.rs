//! The fishbone layout of the tree family (`spec/layout/tree.md`, ishikawa).
//!
//! Nodes arrive in pre-order with the effect first. Cause `k` of the effect
//! hangs above the spine when `k` is even and below it when `k` is odd. A rib
//! rises at the fixed integer slope `cos : sin`; bones of even depth run
//! horizontally and bones of odd depth run along parallel ribs. Pairs of ribs
//! attach to the spine from the head toward the tail and never overlap.

use super::{Layout, Node};
use crate::geom::{COORD_LIMIT, GeomError, Point, Rect, floor_div};

/// The deepest cause nesting; the effect is depth 0.
pub const MAX_DEPTH: usize = 64;

const LEAF_RIB_DIVISOR: i64 = 5;
const MIN_RIB_LENGTH: i32 = 5;
const MARGIN_SLACK: i64 = 3;

/// The ishikawa constants in profile units; `cos` and `sin` set the rib slope.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IshikawaParams {
    pub spine_base: i32,
    pub rib_min: i32,
    pub rib_pool: i32,
    pub min_spacing: i32,
    pub bone_stub: i32,
    pub bone_base: i32,
    pub bone_per_child: i32,
    pub inset: i32,
    pub cos: i32,
    pub sin: i32,
}

impl IshikawaParams {
    fn valid(&self) -> bool {
        self.spine_base >= MIN_RIB_LENGTH
            && self.rib_min >= MIN_RIB_LENGTH
            && self.rib_pool >= 1
            && self.min_spacing >= 1
            && self.bone_stub >= 1
            && self.bone_base >= 1
            && self.bone_per_child >= 0
            && self.inset >= 0
            && self.cos >= 0
            && self.sin >= 1
    }
}

/// The side of the spine a rib hangs on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Side {
    Above,
    Below,
}

impl Side {
    fn index(self) -> usize {
        match self {
            Self::Above => 0,
            Self::Below => 1,
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct Spot {
    x: i64,
    y: i64,
}

#[derive(Debug, Clone, Copy)]
struct RelBox {
    x: i64,
    y: i64,
    w: i64,
    h: i64,
}

struct Piece {
    node: usize,
    rect: RelBox,
    route: [Spot; 2],
}

/// One sub-cause of a rib: its node, the bone index of its parent, its depth.
struct Entry {
    node: usize,
    bone: usize,
    depth: usize,
}

struct Rib {
    cause: usize,
    side: Side,
    entries: Vec<Entry>,
    order: Vec<usize>,
    heights: i64,
    length: i64,
    pieces: Vec<Piece>,
}

#[derive(Debug, Clone, Copy, Default)]
struct Bone {
    x0: i64,
    t0: i64,
    x1: i64,
    t1: i64,
    count: i64,
    drawn: i64,
}

struct Fish<'a> {
    nodes: &'a [Node],
    p: IshikawaParams,
    children: Vec<Vec<usize>>,
    ribs: Vec<Rib>,
    spine_y: i64,
}

/// Lays out the fishbone. Node 0 is the effect. Box `i` and route `i` belong
/// to node `i`; route 0 is the spine, drawn from its tail to the effect.
pub fn ishikawa(nodes: &[Node], p: IshikawaParams) -> Result<Layout, GeomError> {
    if nodes.is_empty() {
        return Ok(Layout {
            boxes: Vec::new(),
            routes: Vec::new(),
        });
    }
    let mut fish = Fish::new(nodes, p)?;
    fish.size_ribs();
    let placed = fish
        .ribs
        .iter()
        .map(|rib| fish.rib_pieces(rib))
        .collect::<Result<Vec<_>, _>>()?;
    for (rib, pieces) in fish.ribs.iter_mut().zip(placed) {
        rib.pieces = pieces;
    }
    fish.assemble()
}

fn count(n: usize) -> i64 {
    i64::try_from(n).unwrap_or(i64::MAX)
}

fn child_lists(nodes: &[Node]) -> Result<(Vec<Vec<usize>>, Vec<usize>), GeomError> {
    let mut children = vec![Vec::new(); nodes.len()];
    let mut depth = vec![0usize; nodes.len()];
    let mut path: Vec<usize> = Vec::new();
    for (i, node) in nodes.iter().enumerate() {
        if node.width < 1 || node.height < 1 {
            return Err(GeomError::Domain);
        }
        if i == 0 {
            if node.parent.is_some() {
                return Err(GeomError::Domain);
            }
            path.push(0);
            continue;
        }
        let parent = node.parent.ok_or(GeomError::Domain)?;
        while path.last().is_some_and(|top| *top != parent) {
            path.pop();
        }
        if path.is_empty() {
            return Err(GeomError::Domain);
        }
        depth[i] = depth[parent] + 1;
        if depth[i] > MAX_DEPTH {
            return Err(GeomError::Domain);
        }
        path.push(i);
        children[parent].push(i);
    }
    Ok((children, depth))
}

impl<'a> Fish<'a> {
    fn new(nodes: &'a [Node], p: IshikawaParams) -> Result<Self, GeomError> {
        if !p.valid() {
            return Err(GeomError::Domain);
        }
        let (children, depth) = child_lists(nodes)?;
        let mut fish = Self {
            nodes,
            p,
            children,
            ribs: Vec::new(),
            spine_y: 0,
        };
        let causes = fish.children[0].clone();
        for (k, cause) in causes.into_iter().enumerate() {
            let side = if k % 2 == 0 { Side::Above } else { Side::Below };
            let rib = fish.new_rib(cause, side, &depth);
            fish.ribs.push(rib);
        }
        Ok(fish)
    }

    fn new_rib(&self, cause: usize, side: Side, depth: &[usize]) -> Rib {
        let mut rib = Rib {
            cause,
            side,
            entries: Vec::new(),
            order: Vec::new(),
            heights: 0,
            length: 0,
            pieces: Vec::new(),
        };
        self.flatten(&mut rib, &self.children[cause], 0, depth);
        for e in &rib.entries {
            rib.heights = rib.heights.max(i64::from(self.nodes[e.node].height));
        }
        rib
    }

    /// Appends the sub-causes in drawing order: the upper side reverses the
    /// siblings at every level. Even depths enter the slot order before their
    /// children and odd depths after them.
    fn flatten(&self, rib: &mut Rib, list: &[usize], bone: usize, depth: &[usize]) {
        let mut siblings = list.to_vec();
        if rib.side == Side::Above {
            siblings.reverse();
        }
        for child in siblings {
            let idx = rib.entries.len();
            rib.entries.push(Entry {
                node: child,
                bone,
                depth: depth[child],
            });
            let odd = !depth[child].is_multiple_of(2);
            if !odd {
                rib.order.push(idx);
            }
            self.flatten(rib, &self.children[child], idx + 1, depth);
            if odd {
                rib.order.push(idx);
            }
        }
    }

    fn side_lengths(&self) -> [i64; 2] {
        let mut totals = [0i64; 2];
        for rib in &self.ribs {
            totals[rib.side.index()] += count(rib.entries.len());
        }
        let base = i64::from(self.p.spine_base);
        let mut lengths = [base, base];
        let all = totals[0] + totals[1];
        if all > 0 {
            for (length, total) in lengths.iter_mut().zip(totals) {
                *length = i64::from(self.p.rib_min)
                    .max(floor_div(i64::from(self.p.rib_pool) * total, all));
            }
        }
        for rib in &self.ribs {
            let slot = &mut lengths[rib.side.index()];
            *slot = (*slot).max(rib.need(i64::from(self.p.min_spacing)));
        }
        lengths
    }

    fn size_ribs(&mut self) {
        let lengths = self.side_lengths();
        self.spine_y = lengths[0].max(i64::from(self.p.spine_base));
        let leaves: Vec<bool> = self
            .ribs
            .iter()
            .map(|rib| self.children[rib.cause].is_empty())
            .collect();
        for (rib, leaf) in self.ribs.iter_mut().zip(leaves) {
            let length = lengths[rib.side.index()];
            rib.length = if leaf {
                floor_div(length, LEAF_RIB_DIVISOR)
            } else {
                length
            };
        }
    }

    fn y(&self, side: Side, t: i64) -> i64 {
        match side {
            Side::Above => self.spine_y - t,
            Side::Below => self.spine_y + t,
        }
    }

    fn run(&self, rise: i64) -> i64 {
        floor_div(rise * i64::from(self.p.cos), i64::from(self.p.sin))
    }

    fn rib_pieces(&self, rib: &Rib) -> Result<Vec<Piece>, GeomError> {
        let end = Spot {
            x: -self.run(rib.length),
            y: self.y(rib.side, rib.length),
        };
        let spine = Spot {
            x: 0,
            y: self.spine_y,
        };
        let mut pieces = vec![Piece {
            node: rib.cause,
            rect: self.cause_box(rib, end),
            route: [spine, end],
        }];
        let mut bones = vec![Bone {
            x1: end.x,
            t1: rib.length,
            count: count(self.children[rib.cause].len()),
            ..Bone::default()
        }];
        let mut times = vec![0i64; rib.entries.len()];
        let slots = count(rib.entries.len()) + 1;
        for (position, idx) in rib.order.iter().enumerate() {
            times[*idx] = floor_div(rib.length * count(position + 1), slots);
        }
        let margin = self.run(rib.heights) + MARGIN_SLACK;
        for (e, t) in rib.entries.iter().zip(times) {
            let mut parent = bones[e.bone];
            let b = self.bone(&mut parent, e, t, margin)?;
            bones[e.bone] = parent;
            bones.push(b);
            pieces.push(self.entry_piece(rib, e, &b));
        }
        Ok(pieces)
    }

    fn cause_box(&self, rib: &Rib, end: Spot) -> RelBox {
        let node = self.nodes[rib.cause];
        let (w, h) = (i64::from(node.width), i64::from(node.height));
        let top = match rib.side {
            Side::Above => end.y - h,
            Side::Below => end.y,
        };
        RelBox {
            x: end.x - floor_div(w, 2),
            y: top,
            w,
            h,
        }
    }

    fn entry_piece(&self, rib: &Rib, e: &Entry, b: &Bone) -> Piece {
        let node = self.nodes[e.node];
        let (w, h) = (i64::from(node.width), i64::from(node.height));
        let y = self.y(rib.side, b.t1);
        Piece {
            node: e.node,
            rect: RelBox {
                x: b.x1 - w,
                y: y - floor_div(h, 2),
                w,
                h,
            },
            route: [
                Spot {
                    x: b.x0,
                    y: self.y(rib.side, b.t0),
                },
                Spot { x: b.x1, y },
            ],
        }
    }

    fn bone(&self, par: &mut Bone, e: &Entry, t: i64, margin: i64) -> Result<Bone, GeomError> {
        let children = count(self.children[e.node].len());
        if !e.depth.is_multiple_of(2) {
            return Ok(self.diagonal(par, t, children));
        }
        let den = par.t1 - par.t0;
        if den <= 0 {
            return Err(GeomError::Domain);
        }
        let x0 = par.x0 + floor_div((par.x1 - par.x0) * (t - par.t0), den);
        Ok(Bone {
            x0,
            t0: t,
            x1: x0 - self.bone_length(children, margin),
            t1: t,
            count: children,
            drawn: 0,
        })
    }

    fn diagonal(&self, par: &mut Bone, t: i64, children: i64) -> Bone {
        let k = par.drawn;
        par.drawn += 1;
        let x0 = par.x0 + floor_div((par.x1 - par.x0) * (par.count - k), par.count + 1);
        Bone {
            x0,
            t0: par.t0,
            x1: x0 - self.run(t - par.t0),
            t1: t,
            count: children,
            drawn: 0,
        }
    }

    fn bone_length(&self, children: i64, margin: i64) -> i64 {
        let planned = if children > 0 {
            i64::from(self.p.bone_base) + children * i64::from(self.p.bone_per_child)
        } else {
            i64::from(self.p.bone_stub)
        };
        planned.max((children + 1) * margin)
    }

    fn assemble(&self) -> Result<Layout, GeomError> {
        let empty = Rect {
            x: 0,
            y: 0,
            w: 0,
            h: 0,
        };
        let mut out = Layout {
            boxes: vec![empty; self.nodes.len()],
            routes: vec![Vec::new(); self.nodes.len()],
        };
        let head = self.nodes[0];
        let (hw, hh) = (i64::from(head.width), i64::from(head.height));
        out.boxes[0] = checked_rect(0, self.spine_y - floor_div(hh, 2), hw, hh)?;
        let mut ceiling = -i64::from(self.p.inset);
        let mut previous = 0i64;
        for pair in self.ribs.chunks(2) {
            let (left, reach) = pair_extent(pair);
            let attach = ceiling.min(previous - reach);
            for rib in pair {
                emit(&mut out, rib, attach)?;
            }
            previous = attach + left;
            ceiling = previous;
        }
        if !self.ribs.is_empty() {
            let tail = Spot {
                x: previous,
                y: self.spine_y,
            };
            let head = Spot {
                x: 0,
                y: self.spine_y,
            };
            out.routes[0] = checked_route([tail, head], 0)?;
        }
        Ok(out)
    }
}

impl Rib {
    /// The side length this rib needs: room for every sub-cause row.
    fn need(&self, spacing: i64) -> i64 {
        let n = count(self.entries.len());
        (n * spacing).max((n + 1) * self.heights)
    }

    /// The left edge and the right reach of the rib's pieces, relative to its
    /// attach point on the spine; the reach is at least 0.
    fn extent(&self) -> (i64, i64) {
        let mut left = self.pieces.first().map_or(0, |p| p.rect.x);
        let mut reach = 0i64;
        for p in &self.pieces {
            left = left.min(p.rect.x);
            reach = reach.max(p.rect.x + p.rect.w);
        }
        (left, reach)
    }
}

fn pair_extent(pair: &[Rib]) -> (i64, i64) {
    let mut left = pair.first().map_or(0, |rib| rib.extent().0);
    let mut reach = 0i64;
    for rib in pair {
        let (l, r) = rib.extent();
        left = left.min(l);
        reach = reach.max(r);
    }
    (left, reach)
}

fn emit(out: &mut Layout, rib: &Rib, attach: i64) -> Result<(), GeomError> {
    for p in &rib.pieces {
        let b = p.rect;
        out.boxes[p.node] = checked_rect(attach + b.x, b.y, b.w, b.h)?;
        out.routes[p.node] = checked_route(p.route, attach)?;
    }
    Ok(())
}

fn narrow(v: i64) -> Result<i32, GeomError> {
    i32::try_from(v).map_err(|_| GeomError::Overflow)
}

fn within_limit(v: i64) -> bool {
    (-COORD_LIMIT..=COORD_LIMIT).contains(&v)
}

fn checked_rect(x: i64, y: i64, w: i64, h: i64) -> Result<Rect, GeomError> {
    if ![x, y, x + w, y + h].into_iter().all(within_limit) {
        return Err(GeomError::Overflow);
    }
    Ok(Rect {
        x: narrow(x)?,
        y: narrow(y)?,
        w: narrow(w)?,
        h: narrow(h)?,
    })
}

fn checked_route(route: [Spot; 2], dx: i64) -> Result<Vec<Point>, GeomError> {
    route
        .iter()
        .map(|s| {
            let (x, y) = (s.x + dx, s.y);
            if !within_limit(x) || !within_limit(y) {
                return Err(GeomError::Overflow);
            }
            Ok(Point {
                x: narrow(x)?,
                y: narrow(y)?,
            })
        })
        .collect()
}

#[cfg(test)]
mod tests;
