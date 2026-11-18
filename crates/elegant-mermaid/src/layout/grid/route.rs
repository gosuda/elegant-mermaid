use std::cmp::Reverse;
use std::collections::BinaryHeap;

use super::{Builder, Edge, Kind, sorted_unique, to_i32};
use crate::geom::{GeomError, Point, Rect};

const MAX_LATTICE: usize = 1 << 20;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Side {
    Top,
    Bottom,
    Left,
    Right,
}

const SIDES: [Side; 4] = [Side::Top, Side::Bottom, Side::Left, Side::Right];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Direction {
    East,
    West,
    South,
    North,
}

const DIRECTIONS: [Direction; 4] = [
    Direction::East,
    Direction::West,
    Direction::South,
    Direction::North,
];

impl Direction {
    const fn index(self) -> usize {
        match self {
            Self::East => 0,
            Self::West => 1,
            Self::South => 2,
            Self::North => 3,
        }
    }

    const fn horizontal(self) -> bool {
        matches!(self, Self::East | Self::West)
    }

    const fn delta(self) -> (isize, isize) {
        match self {
            Self::East => (1, 0),
            Self::West => (-1, 0),
            Self::South => (0, 1),
            Self::North => (0, -1),
        }
    }
}

impl Side {
    const fn outward(self) -> Direction {
        match self {
            Self::Top => Direction::North,
            Self::Bottom => Direction::South,
            Self::Left => Direction::West,
            Self::Right => Direction::East,
        }
    }

    const fn inward(self) -> Direction {
        match self {
            Self::Top => Direction::South,
            Self::Bottom => Direction::North,
            Self::Left => Direction::East,
            Self::Right => Direction::West,
        }
    }
}

const STATES_PER_VERTEX: usize = 4;

struct Lattice {
    xs: Vec<i32>,
    ys: Vec<i32>,
    free_h: Vec<bool>,
    free_v: Vec<bool>,
}

impl Lattice {
    fn vertex(&self, p: Point) -> Option<usize> {
        let i = self.xs.binary_search(&p.x).ok()?;
        let j = self.ys.binary_search(&p.y).ok()?;
        Some(i * self.ys.len() + j)
    }

    fn point(&self, v: usize) -> Point {
        let ny = self.ys.len();
        Point {
            x: self.xs[v / ny],
            y: self.ys[v % ny],
        }
    }

    fn fill_horizontal(&mut self, boxes: &[Obstacle]) {
        let ny = self.ys.len();
        for (j, y) in self.ys.iter().enumerate() {
            let blocked = blocked_runs(boxes, *y, Obstacle::y_run, Obstacle::x_run);
            for (i, free) in free_runs(&self.xs, &blocked).into_iter().enumerate() {
                self.free_h[i * ny + j] = free;
            }
        }
    }

    fn fill_vertical(&mut self, boxes: &[Obstacle]) {
        let ny = self.ys.len();
        for (i, x) in self.xs.iter().enumerate() {
            let blocked = blocked_runs(boxes, *x, Obstacle::x_run, Obstacle::y_run);
            for (j, free) in free_runs(&self.ys, &blocked).into_iter().enumerate() {
                self.free_v[i * ny + j] = free;
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct Interval {
    start: i32,
    end: i32,
}

#[derive(Debug, Clone, Copy)]
struct Obstacle {
    x: Interval,
    y: Interval,
}

impl Obstacle {
    fn x_run(&self) -> Interval {
        self.x
    }

    fn y_run(&self) -> Interval {
        self.y
    }
}

fn blocked_runs(
    boxes: &[Obstacle],
    at: i32,
    across: fn(&Obstacle) -> Interval,
    along: fn(&Obstacle) -> Interval,
) -> Vec<Interval> {
    let mut runs: Vec<Interval> = boxes
        .iter()
        .filter(|o| {
            let span = across(o);
            span.start < at && at < span.end
        })
        .map(along)
        .collect();
    runs.sort_by_key(|run| (run.start, run.end));
    let mut merged: Vec<Interval> = Vec::new();
    for run in runs {
        match merged.last_mut() {
            Some(last) if run.start < last.end => last.end = last.end.max(run.end),
            _ => merged.push(run),
        }
    }
    merged
}

fn free_runs(coords: &[i32], blocked: &[Interval]) -> Vec<bool> {
    let mut free = vec![false; coords.len()];
    let mut m = 0;
    for (i, pair) in coords.windows(2).enumerate() {
        while m < blocked.len() && blocked[m].end <= pair[0] {
            m += 1;
        }
        free[i] = m >= blocked.len() || blocked[m].start >= pair[1];
    }
    free
}

#[derive(Debug, Clone, Copy)]
struct End {
    port: Point,
    vertex: usize,
    stub: i64,
}

#[derive(Debug, Clone, Copy)]
struct Arrival {
    cost: i64,
    state: usize,
    side: Side,
}

fn manhattan(a: Point, b: Point) -> i64 {
    (i64::from(a.x) - i64::from(b.x)).abs() + (i64::from(a.y) - i64::from(b.y)).abs()
}

fn point_of(x: i64, y: i64) -> Point {
    Point {
        x: to_i32(x),
        y: to_i32(y),
    }
}

fn collinear(a: Point, b: Point, c: Point) -> bool {
    (a.x == b.x && b.x == c.x) || (a.y == b.y && b.y == c.y)
}

fn simplify(points: Vec<Point>) -> Vec<Point> {
    let mut out: Vec<Point> = Vec::with_capacity(points.len());
    for p in points {
        if out.last() == Some(&p) {
            continue;
        }
        while out.len() >= 2 && collinear(out[out.len() - 2], out[out.len() - 1], p) {
            out.pop();
        }
        out.push(p);
    }
    out
}

struct Router<'a> {
    lattice: &'a Lattice,
    bend: i64,
    crowded: i64,
    edges: &'a [Edge],
    edge: usize,
    used_h: Vec<Vec<usize>>,
    used_v: Vec<Vec<usize>>,
    dist: Vec<i64>,
    stamp: Vec<u32>,
    prev: Vec<i64>,
    epoch: u32,
    heap: BinaryHeap<Reverse<(i64, usize)>>,
}

fn disjoint(a: &Edge, b: &Edge) -> bool {
    a.from != b.from && a.from != b.to && a.to != b.from && a.to != b.to
}

impl<'a> Router<'a> {
    fn new(lattice: &'a Lattice, bend: i32, edges: &'a [Edge]) -> Self {
        let cells = lattice.xs.len() * lattice.ys.len();
        let states = cells * STATES_PER_VERTEX;
        Self {
            lattice,
            bend: i64::from(bend),
            crowded: 4 * i64::from(bend),
            edges,
            edge: 0,
            used_h: vec![Vec::new(); cells],
            used_v: vec![Vec::new(); cells],
            dist: vec![0; states],
            stamp: vec![0; states],
            prev: vec![0; states],
            epoch: 0,
            heap: BinaryHeap::new(),
        }
    }

    fn neighbour(&self, v: usize, d: Direction) -> Option<usize> {
        let ny = self.lattice.ys.len();
        let (dx, dy) = d.delta();
        let i = isize::try_from(v / ny).ok()?.checked_add(dx)?;
        let j = isize::try_from(v % ny).ok()?.checked_add(dy)?;
        let i = usize::try_from(i)
            .ok()
            .filter(|i| *i < self.lattice.xs.len())?;
        let j = usize::try_from(j).ok().filter(|j| *j < ny)?;
        Some(i * ny + j)
    }

    fn free(&self, d: Direction) -> &[bool] {
        if d.horizontal() {
            &self.lattice.free_h
        } else {
            &self.lattice.free_v
        }
    }

    fn used(&self, d: Direction) -> &[Vec<usize>] {
        if d.horizontal() {
            &self.used_h
        } else {
            &self.used_v
        }
    }

    fn crowd(&self, v: usize, u: usize, d: Direction) -> i64 {
        let current = &self.edges[self.edge];
        let conflicts = self.used(d)[v.min(u)]
            .iter()
            .any(|o| disjoint(&self.edges[*o], current));
        if conflicts { self.crowded } else { 0 }
    }

    fn claim(&mut self, mut state: usize) {
        while let Ok(prev) = usize::try_from(self.prev[state]) {
            let d = DIRECTIONS[state % STATES_PER_VERTEX];
            let (v, u) = (prev / STATES_PER_VERTEX, state / STATES_PER_VERTEX);
            let edge = self.edge;
            let used = if d.horizontal() {
                &mut self.used_h
            } else {
                &mut self.used_v
            };
            used[v.min(u)].push(edge);
            state = prev;
        }
    }

    fn relax(&mut self, state: usize, cost: i64, from: i64) {
        if self.stamp[state] == self.epoch && self.dist[state] <= cost {
            return;
        }
        self.stamp[state] = self.epoch;
        self.dist[state] = cost;
        self.prev[state] = from;
        self.heap.push(Reverse((cost, state)));
    }

    fn step(&self, v: usize, d: Direction) -> Option<(usize, i64)> {
        let u = self.neighbour(v, d)?;
        if !self.free(d)[v.min(u)] {
            return None;
        }
        Some((u, manhattan(self.lattice.point(v), self.lattice.point(u))))
    }

    fn turn(&self, from: Direction, to: Direction) -> i64 {
        if from == to { 0 } else { self.bend }
    }

    fn search(&mut self, sources: &[End; 4], targets: &[End; 4]) -> Option<Vec<Point>> {
        self.epoch += 1;
        self.heap.clear();
        for (s, side) in SIDES.iter().enumerate() {
            let state = sources[s].vertex * STATES_PER_VERTEX + side.outward().index();
            let marker = -1 - i64::try_from(s).ok()?;
            self.relax(state, sources[s].stub, marker);
        }
        let mut best: Option<Arrival> = None;
        while let Some(Reverse((cost, state))) = self.heap.pop() {
            if best.is_some_and(|b| cost >= b.cost) {
                break;
            }
            if self.stale(cost, state) {
                continue;
            }
            best = self.arrive(cost, state, targets, best);
            self.expand(cost, state);
        }
        let best = best?;
        self.claim(best.state);
        let side = SIDES.iter().position(|s| *s == best.side)?;
        Some(self.assemble(best.state, sources, &targets[side]))
    }

    fn stale(&self, cost: i64, state: usize) -> bool {
        self.stamp[state] != self.epoch || self.dist[state] < cost
    }

    fn arrive(
        &self,
        cost: i64,
        state: usize,
        targets: &[End; 4],
        mut best: Option<Arrival>,
    ) -> Option<Arrival> {
        let v = state / STATES_PER_VERTEX;
        let d = DIRECTIONS[state % STATES_PER_VERTEX];
        for (s, side) in SIDES.iter().enumerate() {
            if targets[s].vertex != v {
                continue;
            }
            let total = cost + targets[s].stub + self.turn(d, side.inward());
            if best.is_none_or(|b| total < b.cost) {
                best = Some(Arrival {
                    cost: total,
                    state,
                    side: *side,
                });
            }
        }
        best
    }

    fn expand(&mut self, cost: i64, state: usize) {
        let v = state / STATES_PER_VERTEX;
        let d = DIRECTIONS[state % STATES_PER_VERTEX];
        let from = i64::try_from(state).unwrap_or(i64::MAX);
        for next in DIRECTIONS {
            if let Some((u, length)) = self.step(v, next) {
                let total = cost + length + self.turn(d, next) + self.crowd(v, u, next);
                self.relax(u * STATES_PER_VERTEX + next.index(), total, from);
            }
        }
    }

    fn assemble(&self, mut state: usize, sources: &[End; 4], target: &End) -> Vec<Point> {
        let mut points = vec![target.port];
        loop {
            points.push(self.lattice.point(state / STATES_PER_VERTEX));
            match usize::try_from(self.prev[state]) {
                Ok(prev) => state = prev,
                Err(_) => {
                    let source = usize::try_from(-1 - self.prev[state]).unwrap_or(0);
                    points.push(sources[source].port);
                    break;
                }
            }
        }
        points.reverse();
        simplify(points)
    }
}

impl Builder<'_> {
    fn port(&self, r: Rect, side: Side) -> (Point, Point) {
        let pad = i64::from(self.params.padding);
        let (x, y, w, h) = (
            i64::from(r.x),
            i64::from(r.y),
            i64::from(r.w),
            i64::from(r.h),
        );
        let (cx, cy) = (x + w / 2, y + h / 2);
        match side {
            Side::Top => (point_of(cx, y), point_of(cx, y - self.gap_y + pad)),
            Side::Bottom => (point_of(cx, y + h), point_of(cx, y + h + pad)),
            Side::Left => (point_of(x, cy), point_of(x - self.gap_x + pad, cy)),
            Side::Right => (point_of(x + w, cy), point_of(x + w + pad, cy)),
        }
    }

    fn lattice(&self) -> Result<Lattice, GeomError> {
        let mut xs = self.vlines.clone();
        let mut ys = self.hlines.clone();
        for edge in &self.input.edges {
            for end in [edge.from, edge.to] {
                let r = self.rects[end];
                xs.push(i64::from(r.x) + i64::from(r.w) / 2);
                ys.push(i64::from(r.y) + i64::from(r.h) / 2);
            }
        }
        let xs = sorted_unique(xs);
        let ys = sorted_unique(ys);
        if xs.len() * ys.len() > MAX_LATTICE {
            return Err(GeomError::Overflow);
        }
        let cells = xs.len() * ys.len();
        let mut lattice = Lattice {
            xs,
            ys,
            free_h: vec![false; cells],
            free_v: vec![false; cells],
        };
        let boxes: Vec<Obstacle> = self
            .input
            .blocks
            .iter()
            .zip(&self.rects)
            .filter(|(block, _)| block.kind == Kind::Leaf)
            .map(|(_, r)| Obstacle {
                x: Interval {
                    start: r.x,
                    end: r.x + r.w,
                },
                y: Interval {
                    start: r.y,
                    end: r.y + r.h,
                },
            })
            .collect();
        lattice.fill_horizontal(&boxes);
        lattice.fill_vertical(&boxes);
        Ok(lattice)
    }

    fn ends(&self, lattice: &Lattice, r: Rect) -> Result<[End; 4], GeomError> {
        let mut out = [End {
            port: Point { x: 0, y: 0 },
            vertex: 0,
            stub: 0,
        }; 4];
        for (slot, side) in out.iter_mut().zip(SIDES) {
            let (port, junction) = self.port(r, side);
            let vertex = lattice.vertex(junction).ok_or(GeomError::Domain)?;
            *slot = End {
                port,
                vertex,
                stub: manhattan(port, junction),
            };
        }
        Ok(out)
    }

    fn self_loop(&self, r: Rect) -> Vec<Point> {
        let (x, y, w, h) = (
            i64::from(r.x),
            i64::from(r.y),
            i64::from(r.w),
            i64::from(r.h),
        );
        let (edge, out) = (x + w, x + w + i64::from(self.params.padding));
        let (upper, lower) = (y + h / 3, y + 2 * h / 3);
        simplify(vec![
            point_of(edge, upper),
            point_of(out, upper),
            point_of(out, lower),
            point_of(edge, lower),
        ])
    }

    pub(super) fn route(&self) -> Result<Vec<Vec<Point>>, GeomError> {
        let edges = &self.input.edges;
        if edges.is_empty() {
            return Ok(Vec::new());
        }
        let lattice = self.lattice()?;
        let mut router = Router::new(&lattice, self.params.bend_cost, edges);
        let mut routes = Vec::with_capacity(edges.len());
        for (k, edge) in edges.iter().enumerate() {
            router.edge = k;
            if edge.from == edge.to {
                routes.push(self.self_loop(self.rects[edge.from]));
                continue;
            }
            let sources = self.ends(&lattice, self.rects[edge.from])?;
            let targets = self.ends(&lattice, self.rects[edge.to])?;
            routes.push(router.search(&sources, &targets).ok_or(GeomError::Domain)?);
        }
        Ok(routes)
    }
}
