use std::cmp::Reverse;
use std::collections::{BTreeMap, BinaryHeap};

use super::*;

type Vertex = (usize, usize, u8);
type Cost = (i64, usize);

pub(super) struct EndpointRouting<'a> {
    pub graph: &'a Graph,
    pub input: &'a Input,
    pub boxes: &'a [Rect],
    pub labels: &'a [(usize, Rect)],
    pub regions: &'a super::super::regions::ComponentSets,
}

impl EndpointRouting<'_> {
    pub fn route(&self, edge: &Edge) -> Result<Vec<Point>, LayoutError> {
        let from = self.boxes[edge.tail];
        let to = self.boxes[edge.head];
        let mut obstacles = self.obstacles(edge);
        obstacles.extend(self.labels.iter().map(|(_, rect)| *rect));
        let starts = ports(from)?;
        let ends = ports(to)?;
        let grid = VisibilityGrid::new(&obstacles, &starts, &ends, self.region_frame(edge)?)?;
        grid.shortest(&starts, &ends)
    }

    fn region_frame(&self, edge: &Edge) -> Result<Option<Rect>, LayoutError> {
        let tail = self.region_ancestors(edge.tail)?;
        let head = self.region_ancestors(edge.head)?;
        let shared = tail.into_iter().find(|region| {
            head.contains(region)
                && self
                    .regions
                    .sets
                    .iter()
                    .any(|set| set.regions.contains(region))
        });
        let Some(region) = shared else {
            return Ok(None);
        };
        let group = self.regions.groups[region];
        let node = self
            .graph
            .nodes
            .iter()
            .position(|node| node.id == self.input.groups[group].id)
            .ok_or(LayoutError::Domain)?;
        Ok(Some(self.boxes[node]))
    }

    fn region_ancestors(&self, node: usize) -> Result<Vec<usize>, LayoutError> {
        let declaration =
            usize::try_from(self.graph.nodes[node].decl).map_err(|_| LayoutError::Domain)?;
        let item = self
            .input
            .boxes
            .get(declaration)
            .ok_or(LayoutError::Domain)?;
        let mut parent = self
            .regions
            .groups
            .iter()
            .position(|&group| self.input.groups[group].id == item.parent);
        let mut ancestors = Vec::new();
        while let Some(group) = parent {
            ancestors.push(group);
            parent = self.regions.parents[group];
        }
        Ok(ancestors)
    }

    fn obstacles(&self, edge: &Edge) -> Vec<Rect> {
        let mut ancestors =
            super::super::clusters::ancestors(self.input, &self.graph.nodes[edge.tail].id);
        ancestors.extend(super::super::clusters::ancestors(
            self.input,
            &self.graph.nodes[edge.head].id,
        ));
        self.graph
            .nodes
            .iter()
            .zip(self.boxes)
            .filter_map(|(node, rect)| {
                let declaration = usize::try_from(node.decl).ok()?;
                let semantic = self.input.boxes.get(declaration)?;
                (semantic.exclusive && !ancestors.contains(&declaration)).then_some(*rect)
            })
            .collect()
    }
}

fn ports(rect: Rect) -> Result<[Point; 4], LayoutError> {
    let right = narrow(i64::from(rect.x) + i64::from(rect.w))?;
    let bottom = narrow(i64::from(rect.y) + i64::from(rect.h))?;
    let x = narrow(i64::from(rect.x) + i64::from(rect.w) / 2)?;
    let y = narrow(i64::from(rect.y) + i64::from(rect.h) / 2)?;
    Ok([
        Point { x: rect.x, y },
        Point { x: right, y },
        Point { x, y: rect.y },
        Point { x, y: bottom },
    ])
}

struct VisibilityGrid<'a> {
    x: Vec<i32>,
    y: Vec<i32>,
    obstacles: &'a [Rect],
    bound: Option<Rect>,
}

impl<'a> VisibilityGrid<'a> {
    fn new(
        obstacles: &'a [Rect],
        starts: &[Point],
        ends: &[Point],
        bound: Option<Rect>,
    ) -> Result<Self, LayoutError> {
        let mut x = Vec::new();
        let mut y = Vec::new();
        for rect in obstacles {
            let right = narrow(i64::from(rect.x) + i64::from(rect.w))?;
            let bottom = narrow(i64::from(rect.y) + i64::from(rect.h))?;
            x.extend([
                narrow(i64::from(rect.x) - 1)?,
                right.checked_add(1).ok_or(LayoutError::Overflow)?,
            ]);
            y.extend([
                narrow(i64::from(rect.y) - 1)?,
                bottom.checked_add(1).ok_or(LayoutError::Overflow)?,
            ]);
        }
        for point in starts.iter().chain(ends) {
            x.push(point.x);
            y.push(point.y);
        }
        if let Some(frame) = bound {
            let right = narrow(i64::from(frame.x) + i64::from(frame.w))?;
            let bottom = narrow(i64::from(frame.y) + i64::from(frame.h))?;
            x.extend([frame.x, right]);
            y.extend([frame.y, bottom]);
            x.retain(|&value| frame.x <= value && value <= right);
            y.retain(|&value| frame.y <= value && value <= bottom);
        }
        x.sort();
        x.dedup();
        y.sort();
        y.dedup();
        Ok(Self {
            x,
            y,
            obstacles,
            bound,
        })
    }

    fn point(&self, vertex: Vertex) -> Point {
        Point {
            x: self.x[vertex.0],
            y: self.y[vertex.1],
        }
    }

    fn vertex(&self, point: Point) -> Result<Vertex, LayoutError> {
        Ok((
            self.x
                .binary_search(&point.x)
                .map_err(|_| LayoutError::Domain)?,
            self.y
                .binary_search(&point.y)
                .map_err(|_| LayoutError::Domain)?,
            2,
        ))
    }

    fn shortest(&self, starts: &[Point], ends: &[Point]) -> Result<Vec<Point>, LayoutError> {
        let mut frontier = BinaryHeap::new();
        let mut distances = BTreeMap::new();
        let mut previous = BTreeMap::new();
        for &point in starts {
            if !self.inside(point) {
                continue;
            }
            let vertex = self.vertex(point)?;
            frontier.push(Reverse(((0_i64, 0_usize), vertex)));
            distances.insert(vertex, (0, 0));
        }
        while let Some(Reverse((cost, vertex))) = frontier.pop() {
            if distances.get(&vertex) != Some(&cost) {
                continue;
            }
            if ends.contains(&self.point(vertex)) {
                return Ok(self.reconstruct(vertex, &previous));
            }
            for next in self.neighbours(vertex) {
                if !self.clear(self.point(vertex), self.point(next)) {
                    continue;
                }
                let candidate = self.cost(vertex, next, cost)?;
                if distances.get(&next).is_some_and(|&old| old <= candidate) {
                    continue;
                }
                distances.insert(next, candidate);
                previous.insert(next, vertex);
                frontier.push(Reverse((candidate, next)));
            }
        }
        Err(LayoutError::Domain)
    }

    fn neighbours(&self, (x, y, _): Vertex) -> impl Iterator<Item = Vertex> {
        [
            x.checked_sub(1).map(|x| (x, y, 0)),
            (x + 1 < self.x.len()).then_some((x + 1, y, 0)),
            y.checked_sub(1).map(|y| (x, y, 1)),
            (y + 1 < self.y.len()).then_some((x, y + 1, 1)),
        ]
        .into_iter()
        .flatten()
    }

    fn cost(&self, from: Vertex, to: Vertex, cost: Cost) -> Result<Cost, LayoutError> {
        let a = self.point(from);
        let b = self.point(to);
        let distance =
            (i64::from(a.x) - i64::from(b.x)).abs() + (i64::from(a.y) - i64::from(b.y)).abs();
        Ok((
            cost.0.checked_add(distance).ok_or(LayoutError::Overflow)?,
            cost.1 + usize::from(from.2 != 2 && from.2 != to.2),
        ))
    }

    fn clear(&self, a: Point, b: Point) -> bool {
        self.inside(a) && self.inside(b) && !self.obstacles.iter().any(|rect| hits(a, b, *rect))
    }

    fn inside(&self, point: Point) -> bool {
        self.bound.is_none_or(|frame| {
            frame.x <= point.x
                && i64::from(point.x) <= i64::from(frame.x) + i64::from(frame.w)
                && frame.y <= point.y
                && i64::from(point.y) <= i64::from(frame.y) + i64::from(frame.h)
        })
    }

    fn reconstruct(&self, mut vertex: Vertex, previous: &BTreeMap<Vertex, Vertex>) -> Vec<Point> {
        let mut points = vec![self.point(vertex)];
        while let Some(&parent) = previous.get(&vertex) {
            points.push(self.point(parent));
            vertex = parent;
        }
        points.reverse();
        let mut result: Vec<Point> = Vec::new();
        for point in points {
            if result.len() >= 2
                && result
                    .last()
                    .is_some_and(|&last| collinear(result[result.len() - 2], last, point))
            {
                result.pop();
            }
            result.push(point);
        }
        result
    }
}

fn collinear(a: Point, b: Point, c: Point) -> bool {
    (a.x == b.x && b.x == c.x) || (a.y == b.y && b.y == c.y)
}

fn hits(a: Point, b: Point, rect: Rect) -> bool {
    if rect.w == 0 || rect.h == 0 {
        return false;
    }
    let right = i64::from(rect.x) + i64::from(rect.w);
    let bottom = i64::from(rect.y) + i64::from(rect.h);
    if a.y == b.y {
        return rect.y < a.y
            && i64::from(a.y) < bottom
            && i64::from(a.x.min(b.x)) < right
            && rect.x < a.x.max(b.x);
    }
    rect.x < a.x
        && i64::from(a.x) < right
        && i64::from(a.y.min(b.y)) < bottom
        && rect.y < a.y.max(b.y)
}
