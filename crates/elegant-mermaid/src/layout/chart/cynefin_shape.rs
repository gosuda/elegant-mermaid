//! The wavy fold boundary (one xorshift32 stream per diagram) and the S-shaped cliff.

use crate::geom::{Point, floor_div};
use crate::scene::{Item, PathCommand, PathItem, Shape, ShapeStyle};

use super::LayoutError;
use super::cynefin_stack::CurvePoint;
use super::cynefin_text::point_of;

pub(crate) const FOLD_POINTS: usize = 8;
const FOLD_DRAWS: usize = 15;
const FOLD_WHOLE: i64 = 1 << 32;
const CLIFF_AMPLITUDE: i64 = 3;

struct Xorshift32(u32);

impl Xorshift32 {
    fn next(&mut self) -> u32 {
        let mut v = self.0;
        v ^= v << 13;
        v ^= v >> 17;
        v ^= v << 5;
        self.0 = v;
        v
    }
}

pub(crate) struct FoldCurve {
    pub points: [CurvePoint; FOLD_POINTS],
    pub offset: [i64; FOLD_POINTS - 1],
}

pub(crate) fn new_fold(seed: u32, cx: i64, height: i64, amplitude: i64, waves: i64) -> FoldCurve {
    let mut gen_ = Xorshift32(seed);
    let mut draws = [0_i64; FOLD_DRAWS];
    for draw in &mut draws {
        *draw = i64::from(gen_.next());
    }
    let mut points = [CurvePoint { x: 0, y: 0 }; FOLD_POINTS];
    for (i, point) in points.iter_mut().enumerate() {
        let index = i64::try_from(i).unwrap_or(0);
        *point = CurvePoint {
            x: cx + floor_div(draws[i] * 2 * amplitude, FOLD_WHOLE) - amplitude,
            y: floor_div(index * height, waves),
        };
    }
    let mut offset = [0_i64; FOLD_POINTS - 1];
    for (i, off) in offset.iter_mut().enumerate() {
        let dir = if i % 2 == 1 { -1 } else { 1 };
        *off = dir * floor_div(3 * amplitude * draws[FOLD_POINTS + i], FOLD_WHOLE * 2);
    }
    FoldCurve { points, offset }
}

fn rule() -> Shape {
    Shape::plain(ShapeStyle::Rule)
}

impl FoldCurve {
    pub(crate) fn path(&self) -> Result<Item, LayoutError> {
        let start = point_of(self.points[0].x, self.points[0].y)?;
        let mut commands = vec![PathCommand::Move(start)];
        for (i, off) in self.offset.iter().enumerate() {
            let (p0, p1) = (self.points[i], self.points[i + 1]);
            let mid = floor_div(p0.y + p1.y, 2);
            commands.push(PathCommand::Curve {
                c1: point_of(p0.x + off, mid)?,
                c2: point_of(p1.x - off, mid)?,
                to: point_of(p1.x, p1.y)?,
            });
        }
        Ok(Item::Path(PathItem {
            shape: rule(),
            commands,
        }))
    }

    pub(crate) fn line_path(&self) -> Result<Item, LayoutError> {
        let start = point_of(self.points[0].x, self.points[0].y)?;
        let mut commands = vec![PathCommand::Move(start)];
        for p in &self.points[1..] {
            commands.push(PathCommand::Line(point_of(p.x, p.y)?));
        }
        Ok(Item::Path(PathItem {
            shape: rule(),
            commands,
        }))
    }
}

pub(crate) fn cliff_path(width: i64, height: i64, cx: i64, cy: i64) -> Result<Item, LayoutError> {
    let a = floor_div(width * CLIFF_AMPLITUDE, 100);
    let dh = height - cy;
    let at = |dx: i64, percent: i64| CurvePoint {
        x: cx + dx,
        y: cy + floor_div(dh * percent, 100),
    };
    let nodes = [
        CurvePoint { x: cx, y: cy },
        at(a, 20),
        at(-floor_div(3 * a, 2), 55),
        at(floor_div(a, 2), 75),
        at(-a, 85),
        at(floor_div(3 * a, 10), 95),
        CurvePoint { x: cx, y: height },
    ];
    let mut points: Vec<Point> = Vec::with_capacity(nodes.len());
    for node in nodes {
        points.push(point_of(node.x, node.y)?);
    }
    let curve = |c1: usize, c2: usize, to: usize| PathCommand::Curve {
        c1: points[c1],
        c2: points[c2],
        to: points[to],
    };
    Ok(Item::Path(PathItem {
        shape: rule(),
        commands: vec![PathCommand::Move(points[0]), curve(1, 2, 3), curve(4, 5, 6)],
    }))
}
