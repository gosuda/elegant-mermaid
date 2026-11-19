use super::{Point, Rect, geometry};
use crate::geom::floor_div;
use crate::scene::PathCommand;

const MULTIPLIER: u32 = 2_654_435_761;

pub(super) struct Generator(u32);

pub(super) struct Pass {
    start: (i64, i64),
    control: (i64, i64),
    end: (i64, i64),
}

impl Pass {
    pub(super) fn data(&self) -> String {
        format!(
            "M {} {} Q {} {} {} {}",
            geometry::number(self.start.0),
            geometry::number(self.start.1),
            geometry::number(self.control.0),
            geometry::number(self.control.1),
            geometry::number(self.end.0),
            geometry::number(self.end.1)
        )
    }
}

impl Generator {
    pub(super) fn new(seed: u32, index: usize) -> Generator {
        let n = u64::try_from(index).unwrap_or(u64::MAX).wrapping_add(1) & 0xffff_ffff;
        let factor = u32::try_from(n).unwrap_or(0);
        let mixed = seed ^ factor.wrapping_mul(MULTIPLIER);
        Generator(if mixed == 0 { 1 } else { mixed })
    }

    fn next(&mut self) -> u32 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 17;
        x ^= x << 5;
        self.0 = x;
        x
    }

    fn offset(&mut self) -> i64 {
        i64::from(self.next() % 129) - 64
    }

    pub(super) fn segment(&mut self, from: Point, to: Point) -> [Pass; 2] {
        let first = self.pass(from, to);
        let second = self.pass(from, to);
        [first, second]
    }

    fn pass(&mut self, from: Point, to: Point) -> Pass {
        let bow = self.offset();
        let start = (
            i64::from(from.x) + self.offset(),
            i64::from(from.y) + self.offset(),
        );
        let end = (
            i64::from(to.x) + self.offset(),
            i64::from(to.y) + self.offset(),
        );
        Pass {
            start,
            control: control(start, end, bow),
            end,
        }
    }
}

fn control(start: (i64, i64), end: (i64, i64), bow: i64) -> (i64, i64) {
    let midpoint = (floor_div(start.0 + end.0, 2), floor_div(start.1 + end.1, 2));
    let (dx, dy) = (end.0 - start.0, end.1 - start.1);
    let length = dx.abs().max(dy.abs());
    if length == 0 {
        return midpoint;
    }
    (
        midpoint.0 + round_half_up(bow * -dy, length),
        midpoint.1 + round_half_up(bow * dx, length),
    )
}

fn round_half_up(a: i64, b: i64) -> i64 {
    floor_div(2 * a + b, 2 * b)
}

pub(super) type Segments = Vec<(Point, Point)>;

pub(super) fn path_segments(commands: &[PathCommand]) -> Option<Segments> {
    let mut segments = Vec::new();
    let mut start = None;
    let mut current = None;
    for command in commands {
        match *command {
            PathCommand::Move(p) => {
                start = Some(p);
                current = Some(p);
            }
            PathCommand::Line(p) => {
                segments.push((current?, p));
                current = Some(p);
            }
            PathCommand::Close => {
                let (from, to) = (current?, start?);
                if from != to {
                    segments.push((from, to));
                }
                current = Some(to);
            }
            PathCommand::Curve { .. } | PathCommand::Arc { .. } => return None,
        }
    }
    Some(segments)
}

pub(super) fn polygon_segments(points: &[Point]) -> Segments {
    let mut segments = polyline_segments(points);
    if let (Some(&first), Some(&last)) = (points.first(), points.last())
        && points.len() > 2
        && first != last
    {
        segments.push((last, first));
    }
    segments
}

pub(super) fn polyline_segments(points: &[Point]) -> Segments {
    points.windows(2).map(|w| (w[0], w[1])).collect()
}

pub(super) fn rect_segments(rect: Rect) -> Segments {
    let right = rect.x.saturating_add(rect.w);
    let bottom = rect.y.saturating_add(rect.h);
    polygon_segments(&[
        Point {
            x: rect.x,
            y: rect.y,
        },
        Point {
            x: right,
            y: rect.y,
        },
        Point {
            x: right,
            y: bottom,
        },
        Point {
            x: rect.x,
            y: bottom,
        },
    ])
}

#[cfg(test)]
mod tests {
    use super::*;

    fn point(x: i32, y: i32) -> Point {
        Point { x, y }
    }

    fn data(seed: u32, index: usize, from: Point, to: Point) -> Vec<String> {
        Generator::new(seed, index)
            .segment(from, to)
            .iter()
            .map(Pass::data)
            .collect()
    }

    #[test]
    fn passes_follow_the_specified_stream() {
        assert_eq!(
            data(7, 0, point(0, 0), point(640, 0)),
            [
                "M -0.89 -0.47 Q 4.52 0.53 10.02 0.25",
                "M -0.02 0.55 Q 4.77 -0.5 9.64 -0.05"
            ]
        );
        assert_eq!(
            data(0, 3, point(64, 64), point(64, 640)),
            [
                "M 1.36 0.11 Q 1.19 5.23 1.14 10.38",
                "M 0.11 1.05 Q 0.67 5 1.13 9"
            ]
        );
        assert_eq!(
            data(u32::MAX, 0, point(0, 0), point(0, 0)),
            [
                "M 0.64 -0.33 Q -0.69 -0.69 -0.52 0.69",
                "M 0.39 0.31 Q 0.03 -0.36 -0.69 -0.56"
            ]
        );
    }

    #[test]
    fn zero_mixed_seed_becomes_one_and_seed_zero_stays_nonzero() {
        assert_eq!(Generator::new(MULTIPLIER, 0).0, 1);
        assert_eq!(Generator::new(0, 0).0, MULTIPLIER);
        assert_ne!(Generator::new(0, 1).0, 0);
    }

    #[test]
    fn a_degenerate_pass_keeps_its_midpoint() {
        assert_eq!(control((10, 20), (10, 20), 5), (10, 20));
        assert_eq!(control((0, 0), (64, 0), 0), (32, 0));
        assert_eq!(control((0, 0), (64, 0), 8), (32, 8));
        assert_eq!(control((0, 0), (0, 64), 8), (-8, 32));
    }

    #[test]
    fn straight_primitives_expose_their_segments() {
        let rect = Rect {
            x: 0,
            y: 0,
            w: 64,
            h: 32,
        };
        assert_eq!(
            rect_segments(rect),
            [
                (point(0, 0), point(64, 0)),
                (point(64, 0), point(64, 32)),
                (point(64, 32), point(0, 32)),
                (point(0, 32), point(0, 0)),
            ]
        );
        let commands = [
            PathCommand::Move(point(0, 0)),
            PathCommand::Line(point(10, 0)),
            PathCommand::Line(point(10, 10)),
            PathCommand::Close,
            PathCommand::Move(point(50, 50)),
            PathCommand::Line(point(60, 50)),
        ];
        assert_eq!(
            path_segments(&commands),
            Some(vec![
                (point(0, 0), point(10, 0)),
                (point(10, 0), point(10, 10)),
                (point(10, 10), point(0, 0)),
                (point(50, 50), point(60, 50)),
            ])
        );
        let curve = PathCommand::Curve {
            c1: point(0, 0),
            c2: point(0, 0),
            to: point(0, 0),
        };
        assert_eq!(
            path_segments(&[PathCommand::Move(point(0, 0)), curve]),
            None
        );
        assert_eq!(polyline_segments(&[point(0, 0)]), Vec::new());
        assert_eq!(polygon_segments(&[point(0, 0), point(1, 0)]).len(), 1);
    }
}
