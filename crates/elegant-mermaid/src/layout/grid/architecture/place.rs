//! Placement: each group level is arranged by a breadth-first walk over its lifted edges,
//! and the arranged levels resolve to absolute cells.

use super::{Area, Builder, Cell, EMPTY, LiftedEdge, Unit, ceil_div, slot};
use crate::geom::floor_div;
use crate::layout::input::RouteSide;

const SIDE_ORDER: [RouteSide; 4] = [
    RouteSide::Left,
    RouteSide::Right,
    RouteSide::Up,
    RouteSide::Down,
];

fn step(side: RouteSide) -> Cell {
    match side {
        RouteSide::Left => Cell { x: -1, y: 0 },
        RouteSide::Right => Cell { x: 1, y: 0 },
        RouteSide::Up => Cell { x: 0, y: -1 },
        RouteSide::Down => Cell { x: 0, y: 1 },
    }
}

struct LevelEdge {
    a: usize,
    b: usize,
    side_a: RouteSide,
    side_b: RouteSide,
}

struct Level {
    units: Vec<Unit>,
    rects: Vec<Area>,
    abs: Vec<Area>,
    at: Vec<Cell>,
    placed: Vec<bool>,
    edges: Vec<LevelEdge>,
    incident: Vec<Vec<usize>>,
    bounds: Area,
}

#[derive(Clone, Copy)]
enum Tier {
    Aligned,
    Clear,
}

impl Builder<'_> {
    pub(super) fn place(&mut self) {
        let groups = self.input.groups.len();
        self.local = vec![Cell::default(); self.total];
        self.local_group = vec![Cell::default(); groups];
        self.rel = vec![Area::default(); groups];
        self.lift();
        for g in (0..groups).rev() {
            self.arrange(Some(g));
        }
        self.arrange(None);
        self.resolve();
    }

    fn chain_of(&self, v: usize) -> Vec<Unit> {
        let mut chain = Vec::new();
        let mut g = self.parent[v];
        while let Some(group) = g {
            chain.push(Unit::Group(group));
            g = self.input.groups[group].parent;
        }
        chain.reverse();
        chain.push(Unit::Node(v));
        chain
    }

    fn lift(&mut self) {
        self.lifted = vec![Vec::new(); self.input.groups.len() + 1];
        for e in &self.input.edges {
            if e.from == e.to {
                continue;
            }
            let from = self.chain_of(e.from);
            let to = self.chain_of(e.to);
            let i = from.iter().zip(&to).take_while(|(a, b)| a == b).count();
            let parent = match i.checked_sub(1).map(|k| from[k]) {
                Some(Unit::Group(g)) => Some(g),
                _ => None,
            };
            self.lifted[slot(parent)].push(LiftedEdge {
                a: from[i],
                b: to[i],
                side_a: e.from_side,
                side_b: e.to_side,
            });
        }
    }

    fn key(&self, u: Unit) -> usize {
        match u {
            Unit::Group(g) => self.first_node[g],
            Unit::Node(v) => v,
        }
    }

    fn unit_rect(&self, u: Unit) -> Area {
        match u {
            Unit::Group(g) => self.rel[g],
            Unit::Node(_) => Area {
                x0: 0,
                y0: 0,
                x1: self.px,
                y1: self.py,
            },
        }
    }

    fn new_level(&self, parent: Option<usize>) -> Level {
        let s = slot(parent);
        let mut units: Vec<Unit> = self.child_nodes[s]
            .iter()
            .map(|w| Unit::Node(*w))
            .chain(self.child_groups[s].iter().map(|g| Unit::Group(*g)))
            .collect();
        units.sort_by_key(|u| self.key(*u));
        let n = units.len();
        let rects = units.iter().map(|u| self.unit_rect(*u)).collect();
        let mut level = Level {
            units,
            rects,
            abs: vec![Area::default(); n],
            at: vec![Cell::default(); n],
            placed: vec![false; n],
            edges: Vec::new(),
            incident: vec![Vec::new(); n],
            bounds: EMPTY,
        };
        for e in &self.lifted[s] {
            let a = level.units.iter().position(|u| *u == e.a).unwrap_or(0);
            let b = level.units.iter().position(|u| *u == e.b).unwrap_or(0);
            let k = level.edges.len();
            level.edges.push(LevelEdge {
                a,
                b,
                side_a: e.side_a,
                side_b: e.side_b,
            });
            level.incident[a].push(k);
            level.incident[b].push(k);
        }
        level
    }

    fn arrange(&mut self, parent: Option<usize>) {
        let mut lv = self.new_level(parent);
        for first in 0..lv.units.len() {
            if lv.placed[first] {
                continue;
            }
            let seed = self.seed_cell(&lv, first);
            self.put(&mut lv, first, seed);
            let mut queue = vec![first];
            let mut head = 0;
            while head < queue.len() {
                if self.pops >= i64::from(self.p.fuel) {
                    self.budget = true;
                    break;
                }
                self.pops += 1;
                self.expand(&mut lv, queue[head], &mut queue);
                head += 1;
            }
        }
        let mut content = EMPTY;
        for (i, u) in lv.units.iter().enumerate() {
            match u {
                Unit::Group(g) => self.local_group[*g] = lv.at[i],
                Unit::Node(v) => self.local[*v] = lv.at[i],
            }
            content = content.union(lv.abs[i]);
        }
        if let Some(p) = parent {
            self.rel[p] = self.frame_of(p, content);
        }
    }

    fn seed_cell(&self, lv: &Level, u: usize) -> Cell {
        if lv.bounds == EMPTY {
            return Cell::default();
        }
        Cell {
            x: ceil_div(lv.bounds.x1 - lv.rects[u].x0, self.px) + 1,
            y: 0,
        }
    }

    fn put(&self, lv: &mut Level, u: usize, c: Cell) {
        lv.placed[u] = true;
        lv.at[u] = c;
        lv.abs[u] = lv.rects[u].shift(c.x * self.px, c.y * self.py);
        lv.bounds = lv.bounds.union(lv.abs[u]);
    }

    fn expand(&self, lv: &mut Level, u: usize, queue: &mut Vec<usize>) {
        for incident in 0..lv.incident[u].len() {
            let k = lv.incident[u][incident];
            let (v, side) = {
                let e = &lv.edges[k];
                if e.b == u {
                    (e.a, e.side_b)
                } else {
                    (e.b, e.side_a)
                }
            };
            if lv.placed[v] {
                continue;
            }
            let c = self.choose(lv, v, u, side);
            self.put(lv, v, c);
            queue.push(v);
        }
    }

    fn reach(&self, lv: &Level, v: usize, u: usize, side: RouteSide) -> Cell {
        let (a, r, from) = (lv.abs[u], lv.rects[v], lv.at[u]);
        match side {
            RouteSide::Left => Cell {
                x: floor_div(a.x0 - r.x1, self.px).min(from.x - 1),
                y: from.y,
            },
            RouteSide::Right => Cell {
                x: ceil_div(a.x1 - r.x0, self.px).max(from.x + 1),
                y: from.y,
            },
            RouteSide::Up => Cell {
                x: from.x,
                y: floor_div(a.y0 - r.y1, self.py).min(from.y - 1),
            },
            RouteSide::Down => Cell {
                x: from.x,
                y: ceil_div(a.y1 - r.y0, self.py).max(from.y + 1),
            },
        }
    }

    fn choose(&self, lv: &Level, v: usize, u: usize, side: RouteSide) -> Cell {
        let mut sides = vec![side];
        sides.extend(SIDE_ORDER.iter().copied().filter(|s| *s != side));
        let mut candidates = Vec::with_capacity(8);
        for extra in 0..2i64 {
            for s in &sides {
                let (delta, c) = (step(*s), self.reach(lv, v, u, *s));
                candidates.push(Cell {
                    x: c.x + extra * delta.x,
                    y: c.y + extra * delta.y,
                });
            }
        }
        let tiers = [
            (Tier::Aligned, i64::from(self.p.ring_cap)),
            (Tier::Clear, self.sweep(lv, v)),
        ];
        for (tier, radius) in tiers {
            if let Some(c) = candidates
                .iter()
                .copied()
                .find(|c| self.accepts(tier, lv, v, *c))
            {
                return c;
            }
            if let Some(c) = self.ring(lv, v, lv.at[u], radius, tier) {
                return c;
            }
        }
        self.seed_cell(lv, v)
    }

    fn ring(&self, lv: &Level, v: usize, from: Cell, radius: i64, tier: Tier) -> Option<Cell> {
        for d in 1..=radius {
            for dy in -d..=d {
                let dx = d - dy.abs();
                for x in [from.x - dx, from.x + dx] {
                    let c = Cell { x, y: from.y + dy };
                    if self.accepts(tier, lv, v, c) {
                        return Some(c);
                    }
                }
            }
        }
        None
    }

    fn sweep(&self, lv: &Level, v: usize) -> i64 {
        let r = lv.rects[v];
        let width = ceil_div(lv.bounds.x1 - lv.bounds.x0 + r.x1 - r.x0, self.px);
        let height = ceil_div(lv.bounds.y1 - lv.bounds.y0 + r.y1 - r.y0, self.py);
        width + height + 2
    }

    fn accepts(&self, tier: Tier, lv: &Level, v: usize, c: Cell) -> bool {
        match tier {
            Tier::Aligned => self.clear(lv, v, c) && self.aligned(lv, v, c),
            Tier::Clear => self.clear(lv, v, c),
        }
    }

    fn clear(&self, lv: &Level, v: usize, c: Cell) -> bool {
        let r = lv.rects[v].shift(c.x * self.px, c.y * self.py);
        !lv.placed
            .iter()
            .zip(&lv.abs)
            .any(|(placed, abs)| *placed && r.overlaps(*abs))
    }

    fn aligned(&self, lv: &Level, v: usize, c: Cell) -> bool {
        let Unit::Node(node) = lv.units[v] else {
            return true;
        };
        for i in &self.aligns_of[node] {
            let a = &self.input.aligns[*i];
            let anchor = a.members.iter().find_map(|m| {
                let j = lv.units.iter().position(|u| *u == Unit::Node(*m))?;
                (*m != node && lv.placed[j]).then_some(j)
            });
            let Some(j) = anchor else { continue };
            let held = if a.column {
                lv.at[j].x == c.x
            } else {
                lv.at[j].y == c.y
            };
            if !held {
                return false;
            }
        }
        true
    }

    fn resolve(&mut self) {
        let groups = self.input.groups.len();
        let mut origins = vec![Cell::default(); groups];
        self.frame = vec![Area::default(); groups];
        for (g, entry) in self.input.groups.iter().enumerate() {
            let base = entry.parent.map_or(Cell::default(), |p| origins[p]);
            origins[g] = Cell {
                x: base.x + self.local_group[g].x,
                y: base.y + self.local_group[g].y,
            };
            self.frame[g] = self.rel[g].shift(origins[g].x * self.px, origins[g].y * self.py);
        }
        self.pos = (0..self.total)
            .map(|v| {
                let base = self.parent[v].map_or(Cell::default(), |p| origins[p]);
                Cell {
                    x: base.x + self.local[v].x,
                    y: base.y + self.local[v].y,
                }
            })
            .collect();
    }
}
