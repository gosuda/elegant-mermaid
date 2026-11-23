use std::cmp::Reverse;
use std::collections::{BTreeMap, BinaryHeap};

use super::LayoutError;
use super::{Axis, Band, narrow};
use crate::geom::{Point, Rect};
use crate::scene::{self, GroupRole, Item, Profile};

#[derive(Clone, Copy)]
struct GridPoint {
    cross: i64,
    rank: i64,
}

impl Axis {
    fn other(self) -> Self {
        match self {
            Self::X => Self::Y,
            Self::Y => Self::X,
        }
    }
    fn at(self, cross: i32, rank: i32) -> Point {
        match self {
            Self::X => Point { x: cross, y: rank },
            Self::Y => Point { x: rank, y: cross },
        }
    }
    fn grid(self, p: Point) -> GridPoint {
        GridPoint {
            cross: i64::from(self.value(p)),
            rank: i64::from(self.other().value(p)),
        }
    }
}

#[derive(Clone, Copy)]
struct Obstacle {
    cross0: i64,
    cross1: i64,
    rank0: i64,
    rank1: i64,
}

impl Obstacle {
    fn new(axis: Axis, r: Rect) -> Self {
        let cross0 = i64::from(axis.start(r));
        let rank0 = i64::from(axis.other().start(r));
        Self {
            cross0,
            cross1: cross0 + i64::from(axis.len(r)),
            rank0,
            rank1: rank0 + i64::from(axis.other().len(r)),
        }
    }
    fn hits(&self, a: GridPoint, b: GridPoint) -> bool {
        (a.rank == b.rank
            && self.rank0 < a.rank
            && a.rank < self.rank1
            && a.cross.min(b.cross) < self.cross1
            && self.cross0 < a.cross.max(b.cross))
            || (a.cross == b.cross
                && self.cross0 < a.cross
                && a.cross < self.cross1
                && a.rank.min(b.rank) < self.rank1
                && self.rank0 < a.rank.max(b.rank))
    }
}

struct Grid<'a> {
    cross: Vec<i64>,
    rank: Vec<i64>,
    obstacles: &'a [Obstacle],
}

impl<'a> Grid<'a> {
    fn new(obstacles: &'a [Obstacle], inflate: i64, entry: GridPoint, exit: GridPoint) -> Self {
        let mut cross = vec![entry.cross, exit.cross];
        let mut rank = vec![entry.rank, exit.rank];
        for o in obstacles {
            cross.extend([o.cross0 - inflate, o.cross1 + inflate]);
            rank.extend([o.rank0 - inflate, o.rank1 + inflate]);
        }
        cross.sort();
        cross.dedup();
        rank.sort();
        rank.dedup();
        Self {
            cross,
            rank,
            obstacles,
        }
    }
    fn vertex(&self, p: GridPoint) -> usize {
        self.cross.partition_point(|&v| v < p.cross) * self.rank.len()
            + self.rank.partition_point(|&v| v < p.rank)
    }
    fn point(&self, v: usize) -> GridPoint {
        GridPoint {
            cross: self.cross[v / self.rank.len()],
            rank: self.rank[v % self.rank.len()],
        }
    }
    fn neighbour(&self, v: usize, movement: usize) -> Option<usize> {
        let i = v / self.rank.len();
        let j = v % self.rank.len();
        let (i, j) = match movement {
            0 => (i.checked_add(1)?, j),
            1 => (i.checked_sub(1)?, j),
            2 => (i, j.checked_add(1)?),
            _ => (i, j.checked_sub(1)?),
        };
        (i < self.cross.len() && j < self.rank.len()).then_some(i * self.rank.len() + j)
    }
    fn free(&self, a: GridPoint, b: GridPoint) -> bool {
        !self.obstacles.iter().any(|o| o.hits(a, b))
    }
}

struct Search<'a> {
    grid: &'a Grid<'a>,
    goal: usize,
    end_move: usize,
    bend: i64,
    dist: BTreeMap<usize, i64>,
    pred: BTreeMap<usize, usize>,
    queue: BinaryHeap<Reverse<(i64, usize)>>,
    best: Option<(i64, usize)>,
}

impl Search<'_> {
    fn turn(&self, from: usize, to: usize) -> i64 {
        if from == to { 0 } else { self.bend }
    }
    fn heuristic(&self, v: usize) -> i64 {
        let p = self.grid.point(v);
        let g = self.grid.point(self.goal);
        (p.cross - g.cross).abs() + (p.rank - g.rank).abs()
    }
    fn relax(&mut self, state: usize, cost: i64, movement: usize) {
        let v = state / 4;
        let last = state % 4;
        if movement == (last ^ 1) {
            return;
        }
        let Some(w) = self.grid.neighbour(v, movement) else {
            return;
        };
        let a = self.grid.point(v);
        let b = self.grid.point(w);
        if !self.grid.free(a, b) {
            return;
        }
        let next =
            cost + (b.cross - a.cross).abs() + (b.rank - a.rank).abs() + self.turn(last, movement);
        let target = w * 4 + movement;
        if self.dist.get(&target).is_some_and(|&known| known <= next) {
            return;
        }
        self.dist.insert(target, next);
        self.pred.insert(target, state);
        self.queue.push(Reverse((next + self.heuristic(w), target)));
    }
    fn run(mut self, start: usize, start_move: usize) -> Option<Vec<usize>> {
        let first = start * 4 + start_move;
        self.dist.insert(first, 0);
        self.queue.push(Reverse((self.heuristic(start), first)));
        while let Some(Reverse((priority, state))) = self.queue.pop() {
            if self.best.is_some_and(|(cost, _)| priority >= cost) {
                break;
            }
            let cost = priority - self.heuristic(state / 4);
            if self.dist.get(&state) != Some(&cost) {
                continue;
            }
            if state / 4 == self.goal {
                let total = cost + self.turn(state % 4, self.end_move);
                if self.best.is_none_or(|(best, _)| total < best) {
                    self.best = Some((total, state));
                }
            }
            for movement in 0..4 {
                self.relax(state, cost, movement);
            }
        }
        let (_, mut state) = self.best?;
        let mut path = Vec::new();
        loop {
            path.push(state / 4);
            match self.pred.get(&state) {
                Some(&previous) => state = previous,
                None => break,
            }
        }
        path.reverse();
        Some(path)
    }
}

struct Ends {
    source: Point,
    target: Point,
    entry: GridPoint,
    exit: GridPoint,
    start_move: usize,
    end_move: usize,
}

fn outward(axis: Axis, boxed: Rect, rank: i64) -> i64 {
    let start = i64::from(axis.other().start(boxed));
    if 2 * rank >= 2 * start + i64::from(axis.other().len(boxed)) {
        1
    } else {
        -1
    }
}

pub(super) struct Router {
    pub(super) axis: Axis,
    pub(super) slot: i64,
    pub(super) bend: i64,
}

impl Router {
    fn ends(
        &self,
        from: Rect,
        to: Rect,
        input: (&[Point], (i64, i64)),
    ) -> Result<Ends, LayoutError> {
        let (original, shifts) = input;
        let first = *original.first().ok_or(LayoutError::Domain)?;
        let last = *original.last().ok_or(LayoutError::Domain)?;
        let source = self
            .axis
            .with(first, narrow(i64::from(self.axis.value(first)) + shifts.0)?);
        let target = self
            .axis
            .with(last, narrow(i64::from(self.axis.value(last)) + shifts.1)?);
        let s = self.axis.grid(source);
        let t = self.axis.grid(target);
        let leave = outward(self.axis, from, s.rank);
        let enter = outward(self.axis, to, t.rank);
        Ok(Ends {
            source,
            target,
            entry: GridPoint {
                cross: s.cross,
                rank: s.rank + leave * self.slot,
            },
            exit: GridPoint {
                cross: t.cross,
                rank: t.rank + enter * self.slot,
            },
            start_move: if leave < 0 { 3 } else { 2 },
            end_move: if enter < 0 { 2 } else { 3 },
        })
    }

    fn points(
        &self,
        boxes: &[Obstacle],
        text: &[Obstacle],
        ends: &Ends,
    ) -> Result<Vec<Point>, LayoutError> {
        let obstacles: Vec<_> = boxes.iter().chain(text).copied().collect();
        for inflate in [self.slot, 0] {
            let grid = Grid::new(&obstacles, inflate, ends.entry, ends.exit);
            let search = Search {
                grid: &grid,
                goal: grid.vertex(ends.exit),
                end_move: ends.end_move,
                bend: self.bend,
                dist: BTreeMap::new(),
                pred: BTreeMap::new(),
                queue: BinaryHeap::new(),
                best: None,
            };
            let Some(path) = search.run(grid.vertex(ends.entry), ends.start_move) else {
                continue;
            };
            let points = polyline(self.axis, &grid, &path, ends)?;
            if points.windows(2).all(|pair| {
                !boxes
                    .iter()
                    .any(|obstacle| obstacle.hits(self.axis.grid(pair[0]), self.axis.grid(pair[1])))
            }) {
                return Ok(points);
            }
        }
        Err(LayoutError::Domain)
    }

    pub(super) fn run(
        &self,
        dump: &mut scene::Dump,
        items: &mut [scene::Group],
        input: (&[Band], &[Vec<Point>]),
    ) -> Result<(), LayoutError> {
        let (bands, original) = input;
        let text: Vec<_> = if dump.options.profile == Profile::Cell {
            text_obstacles(self.axis, items).collect()
        } else {
            Vec::new()
        };
        for (route, old) in dump.routes.iter_mut().zip(original) {
            let band = |id: &str| {
                bands
                    .iter()
                    .position(|b| b.id == id || b.members.iter().any(|m| m == id))
            };
            let (Some(from), Some(to)) = (band(&route.from), band(&route.to)) else {
                continue;
            };
            if from == to || old.len() < 2 {
                continue;
            }
            let Some(fb) = dump.boxes.iter().find(|b| b.id == route.from) else {
                continue;
            };
            let Some(tb) = dump.boxes.iter().find(|b| b.id == route.to) else {
                continue;
            };
            let ends = self.ends(
                fb.rect,
                tb.rect,
                (old, (bands[from].shift, bands[to].shift)),
            )?;
            let obstacles: Vec<Obstacle> = dump
                .boxes
                .iter()
                .filter(|b| b.exclusive && b.id != route.from && b.id != route.to)
                .map(|b| Obstacle::new(self.axis, b.rect))
                .collect();
            replace(items, route, self.points(&obstacles, &text, &ends)?);
        }
        Ok(())
    }
}

fn text_obstacles(axis: Axis, items: &[scene::Group]) -> impl Iterator<Item = Obstacle> {
    items
        .iter()
        .flat_map(|group| &group.items)
        .filter_map(move |item| {
            let Item::Text(text) = item else {
                return None;
            };
            if text.rect.w <= 0 || text.rect.h <= 0 {
                return None;
            }
            let mut bound = Obstacle::new(axis, text.rect);
            bound.cross0 -= 1;
            bound.cross1 += 1;
            bound.rank0 -= 1;
            bound.rank1 += 1;
            Some(bound)
        })
}

fn polyline(
    axis: Axis,
    grid: &Grid<'_>,
    path: &[usize],
    ends: &Ends,
) -> Result<Vec<Point>, LayoutError> {
    let mut raw = Vec::with_capacity(path.len() + 2);
    raw.push(ends.source);
    for &v in path {
        let p = grid.point(v);
        raw.push(axis.at(narrow(p.cross)?, narrow(p.rank)?));
    }
    raw.push(ends.target);
    let mut points: Vec<Point> = Vec::new();
    for p in raw {
        if points.last() == Some(&p) {
            continue;
        }
        while points.len() >= 2 {
            let Some([a, b]) = points.last_chunk::<2>() else {
                break;
            };
            if !((a.x == b.x && b.x == p.x) || (a.y == b.y && b.y == p.y)) {
                break;
            }
            points.pop();
        }
        points.push(p);
    }
    Ok(points)
}

fn replace(items: &mut [scene::Group], route: &mut scene::SceneRoute, points: Vec<Point>) {
    for group in items {
        if group.role != GroupRole::Edge || group.owner != route.id {
            continue;
        }
        for item in &mut group.items {
            match item {
                Item::Polyline(line) => line.points.clone_from(&points),
                Item::MarkerRef(marker) => {
                    if route.points.first() == Some(&marker.at) {
                        if let Some(&first) = points.first() {
                            marker.at = first;
                        }
                    } else if route.points.last() == Some(&marker.at)
                        && let Some(&last) = points.last()
                    {
                        marker.at = last;
                    }
                }
                _ => {}
            }
        }
    }
    route.points = points;
}
