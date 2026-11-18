//! The tree layout family (`spec/layout/tree.md`): the mindmap tidy tree.
//!
//! Nodes arrive in pre-order. Each root child alternates sides, and each side is a
//! non-layered tidy tree. Later siblings sit below the union contour of the earlier ones,
//! where a box occupies its x-range widened by `level_gap` toward its parent (tree-10).

mod geometry;
mod ishikawa;

pub use geometry::normalize;
pub use ishikawa::{IshikawaParams, MAX_DEPTH as ISHIKAWA_MAX_DEPTH, ishikawa};

use crate::geom::{GeomError, Point, Rect, floor_div};

/// One node: its parent index and its box size in profile units.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Node {
    pub parent: Option<usize>,
    pub width: i32,
    pub height: i32,
}

/// The two gaps of the tree, in profile units.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Gaps {
    pub level: i32,
    pub sibling: i32,
}

/// Boxes in node order and one route per non-root node; the root route is empty.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Layout {
    pub boxes: Vec<Rect>,
    pub routes: Vec<Vec<Point>>,
}

#[derive(Debug, Clone, Copy)]
struct Offset {
    u: i64,
    y: i64,
}

#[derive(Debug, Clone, Copy)]
struct Contour {
    u0: i64,
    u1: i64,
    top: i64,
    bottom: i64,
}

impl Contour {
    fn overlaps(&self, other: &Contour) -> bool {
        self.u0 < other.u1 && other.u0 < self.u1
    }
}

pub(super) struct Placer<'a> {
    nodes: &'a [Node],
    gaps: Gaps,
    children: Vec<Vec<usize>>,
    rel: Vec<Vec<Offset>>,
    dy: Vec<i64>,
}

/// Lays out the tree. Nodes must be in pre-order with the root first.
pub fn mindmap(nodes: &[Node], gaps: Gaps) -> Result<Layout, GeomError> {
    if nodes.is_empty() {
        return Ok(Layout {
            boxes: Vec::new(),
            routes: Vec::new(),
        });
    }
    let mut placer = Placer::new(nodes, gaps)?;
    for v in (0..nodes.len()).rev() {
        placer.place(v);
    }
    placer.layout()
}

impl<'a> Placer<'a> {
    fn new(nodes: &'a [Node], gaps: Gaps) -> Result<Self, GeomError> {
        if gaps.level < 0 || gaps.sibling < 1 {
            return Err(GeomError::Domain);
        }
        let mut children = vec![Vec::new(); nodes.len()];
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
            path.push(i);
            children[parent].push(i);
        }
        Ok(Self {
            nodes,
            gaps,
            children,
            rel: vec![Vec::new(); nodes.len()],
            dy: vec![0; nodes.len()],
        })
    }

    fn place(&mut self, v: usize) {
        if v == 0 {
            let (right, left) = sides(&self.children[0]);
            self.stack(&right);
            self.stack(&left);
            return;
        }
        let list = self.children[v].clone();
        self.stack(&list);
        let step = i64::from(self.nodes[v].width) + i64::from(self.gaps.level);
        let mut rel = vec![Offset { u: 0, y: 0 }];
        for c in list {
            for o in std::mem::take(&mut self.rel[c]) {
                rel.push(Offset {
                    u: step + o.u,
                    y: self.dy[c] + o.y,
                });
            }
        }
        self.rel[v] = rel;
    }

    fn stack(&mut self, list: &[usize]) {
        let mut frame: Vec<Contour> = Vec::new();
        let mut ys: Vec<i64> = Vec::with_capacity(list.len());
        for (j, c) in list.iter().enumerate() {
            let y = if j == 0 {
                0
            } else {
                self.separation(&frame, *c)
            };
            self.extend(&mut frame, *c, y);
            ys.push(y);
        }
        let ends = ys.first().copied().unwrap_or(0) + ys.last().copied().unwrap_or(0);
        let centre = floor_div(ends, 2);
        for (c, y) in list.iter().zip(&ys) {
            self.dy[*c] = *y - centre;
        }
    }

    fn contour_box(&self, c: usize, k: usize, o: Offset) -> Contour {
        let node = self.nodes[c + k];
        let top = o.y - floor_div(i64::from(node.height), 2);
        Contour {
            u0: o.u - i64::from(self.gaps.level),
            u1: o.u + i64::from(node.width),
            top,
            bottom: top + i64::from(node.height),
        }
    }

    fn separation(&self, frame: &[Contour], c: usize) -> i64 {
        let mut best: Option<i64> = None;
        for (k, o) in self.rel[c].iter().enumerate() {
            let b = self.contour_box(c, k, *o);
            for a in frame.iter().filter(|a| a.overlaps(&b)) {
                let need = a.bottom - b.top + i64::from(self.gaps.sibling);
                best = Some(best.map_or(need, |current| current.max(need)));
            }
        }
        best.unwrap_or(0)
    }

    fn extend(&self, frame: &mut Vec<Contour>, c: usize, y: i64) {
        for (k, o) in self.rel[c].iter().enumerate() {
            let mut b = self.contour_box(c, k, *o);
            b.top += y;
            b.bottom += y;
            frame.push(b);
        }
    }
}

fn sides(children: &[usize]) -> (Vec<usize>, Vec<usize>) {
    let mut right = Vec::new();
    let mut left = Vec::new();
    for (i, c) in children.iter().enumerate() {
        if i % 2 == 0 {
            right.push(*c);
        } else {
            left.push(*c);
        }
    }
    (right, left)
}

#[cfg(test)]
mod tests;
