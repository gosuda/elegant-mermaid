use super::place::Layouter;
use super::size::Shape;
use super::tree::{Kind, Pt, fit};
use crate::geom::{GeomError, Point, floor_div};
use crate::scene::{Item, PathCommand, PathItem, PolylineItem, Shape as SceneShape, ShapeStyle};

const QUARTER_TURN: i32 = 16384;

const RAIL_SHAPE: SceneShape = SceneShape::plain(ShapeStyle::Edge);

pub(super) fn point_of(p: Pt) -> Result<Point, GeomError> {
    Ok(Point {
        x: fit(p.x)?,
        y: fit(p.y)?,
    })
}

fn translate(points: &[Pt], dx: i64, dy: i64) -> Vec<Pt> {
    points
        .iter()
        .map(|p| Pt {
            x: p.x + dx,
            y: p.y + dy,
        })
        .collect()
}

fn compact(points: &[Pt]) -> Vec<Pt> {
    let mut out = Vec::with_capacity(points.len());
    for p in points {
        if out.last() != Some(p) {
            out.push(*p);
        }
    }
    out
}

fn sign(v: i64) -> i64 {
    v.signum()
}

fn unit(from: Pt, to: Pt) -> Pt {
    Pt {
        x: sign(to.x - from.x),
        y: sign(to.y - from.y),
    }
}

fn leg_length(from: Pt, to: Pt) -> i64 {
    (to.x - from.x).abs() + (to.y - from.y).abs()
}

fn quarter_angle(v: Pt) -> i32 {
    if v.x > 0 {
        0
    } else if v.y > 0 {
        QUARTER_TURN
    } else if v.x < 0 {
        2 * QUARTER_TURN
    } else {
        3 * QUARTER_TURN
    }
}

impl Layouter {
    pub(super) fn right_start(&self, kid: &Shape<'_>, x: i64) -> i64 {
        if self.p.is_cell() && kid.node.kind.leaf() {
            x - 1
        } else {
            x
        }
    }

    pub(super) fn rails(&self, s: &Shape<'_>, x: i64, y: i64) -> Result<Vec<Item>, GeomError> {
        let polylines = match s.node.kind {
            Kind::Choice => self.choice_rails(s),
            Kind::Optional => {
                let mut out = self.forward_rails(s);
                out.push(self.bypass_rail(s));
                out
            }
            Kind::ZeroOrMore => {
                let mut out = self.forward_rails(s);
                out.push(self.loop_rail(s));
                out.push(self.bypass_rail(s));
                out
            }
            Kind::OneOrMore => {
                let mut out = self.forward_rails(s);
                out.push(self.loop_rail(s));
                out
            }
            Kind::Terminal | Kind::NonTerminal | Kind::Special | Kind::Sequence => Vec::new(),
        };
        polylines
            .iter()
            .map(|polyline| self.rail(&translate(polyline, x, y)))
            .collect()
    }

    fn choice_rails(&self, s: &Shape<'_>) -> Vec<Vec<Pt>> {
        let r = self.k.arc_radius;
        let cy = s.centre();
        let mut out = Vec::new();
        for (kid, off) in s.kids.iter().zip(&s.offsets) {
            let ecy = off.y + kid.up;
            let mut left = vec![Pt { x: 0, y: cy }];
            let mut right = vec![Pt {
                x: self.right_start(kid, off.x + kid.w),
                y: ecy,
            }];
            if ecy != cy {
                left.push(Pt { x: r, y: cy });
                left.push(Pt { x: r, y: ecy });
                right.push(Pt { x: s.w - r, y: ecy });
                right.push(Pt { x: s.w - r, y: cy });
            }
            left.push(Pt { x: off.x, y: ecy });
            right.push(Pt { x: s.w, y: cy });
            out.push(left);
            out.push(right);
        }
        out
    }

    fn forward_rails(&self, s: &Shape<'_>) -> Vec<Vec<Pt>> {
        let kid = &s.kids[0];
        let cy = s.centre();
        let r = self.k.arc_radius;
        vec![
            vec![Pt { x: 0, y: cy }, Pt { x: 2 * r, y: cy }],
            vec![
                Pt {
                    x: self.right_start(kid, 2 * r + kid.w),
                    y: cy,
                },
                Pt { x: s.w, y: cy },
            ],
        ]
    }

    fn bypass_rail(&self, s: &Shape<'_>) -> Vec<Pt> {
        let cy = s.centre();
        let r = self.k.arc_radius;
        vec![
            Pt { x: 0, y: cy },
            Pt { x: r, y: cy },
            Pt { x: r, y: 0 },
            Pt { x: s.w - r, y: 0 },
            Pt { x: s.w - r, y: cy },
            Pt { x: s.w, y: cy },
        ]
    }

    fn loop_rail(&self, s: &Shape<'_>) -> Vec<Pt> {
        let kid = &s.kids[0];
        let cy = s.centre();
        let r = self.k.arc_radius;
        let mut bottom = s.height();
        if self.p.is_cell() {
            bottom -= 1;
        }
        let end = 2 * r + kid.w;
        vec![
            Pt {
                x: self.right_start(kid, end),
                y: cy,
            },
            Pt { x: end + r, y: cy },
            Pt {
                x: end + r,
                y: bottom,
            },
            Pt { x: r, y: bottom },
            Pt { x: r, y: cy },
            Pt { x: 2 * r, y: cy },
        ]
    }

    pub(super) fn rail(&self, points: &[Pt]) -> Result<Item, GeomError> {
        let points = compact(points);
        if self.p.is_cell() {
            let out = points
                .iter()
                .map(|p| point_of(*p))
                .collect::<Result<Vec<_>, _>>()?;
            return Ok(Item::Polyline(PolylineItem {
                shape: RAIL_SHAPE,
                points: out,
                corner: 0,
            }));
        }
        Ok(Item::Path(PathItem {
            shape: RAIL_SHAPE,
            commands: self.rounded(&points)?,
        }))
    }

    fn corner_radius(&self, points: &[Pt], k: usize) -> i64 {
        let last = points.len() - 1;
        let mut incoming = leg_length(points[k - 1], points[k]);
        let mut outgoing = leg_length(points[k], points[k + 1]);
        if k - 1 > 0 {
            incoming = floor_div(incoming, 2);
        }
        if k + 1 < last {
            outgoing = floor_div(outgoing, 2);
        }
        self.k.arc_radius.min(incoming).min(outgoing)
    }

    fn rounded(&self, points: &[Pt]) -> Result<Vec<PathCommand>, GeomError> {
        let (Some(first), Some(end)) = (points.first(), points.last()) else {
            return Err(GeomError::Domain);
        };
        let mut commands = vec![PathCommand::Move(point_of(*first)?)];
        for k in 1..points.len().saturating_sub(1) {
            let incoming = unit(points[k - 1], points[k]);
            let outgoing = unit(points[k], points[k + 1]);
            let turn = incoming.x * outgoing.y - incoming.y * outgoing.x;
            let radius = self.corner_radius(points, k);
            if turn == 0 || radius == 0 {
                commands.push(PathCommand::Line(point_of(points[k])?));
                continue;
            }
            let start = Pt {
                x: points[k].x - radius * incoming.x,
                y: points[k].y - radius * incoming.y,
            };
            let centre = Pt {
                x: start.x + radius * outgoing.x,
                y: start.y + radius * outgoing.y,
            };
            let sweep = if turn < 0 {
                -QUARTER_TURN
            } else {
                QUARTER_TURN
            };
            commands.push(PathCommand::Line(point_of(start)?));
            commands.push(PathCommand::Arc {
                centre: point_of(centre)?,
                r: fit(radius)?,
                start: quarter_angle(Pt {
                    x: -outgoing.x,
                    y: -outgoing.y,
                }),
                sweep,
            });
        }
        commands.push(PathCommand::Line(point_of(*end)?));
        Ok(commands)
    }
}
