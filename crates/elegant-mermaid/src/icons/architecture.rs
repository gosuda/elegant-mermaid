//! The five drawn built-in icons: shapes on an 80 by 80 design grid, scaled into the 24 px
//! icon box. Coordinates are decimal texts, read by the same fixed-point rule as icon paths.

use super::BOX;
use super::path::{Pair, SCALE, convert_with, fixed};
use crate::geom::{Point, Rect};
use crate::scene::{
    EllipseItem, Item, PathItem, PolylineItem, RoundRectItem, Shape, ShapeStyle, Width,
};

const VIEW_BOX: i64 = 80;
const CYLINDER_RIM: &str = "c0,3.94,8.95,7.14,20,7.14s20-3.2,20-7.14";
const CLOUD: &str = "m65,47.5c0,2.76-2.24,5-5,5H20c-2.76,0-5-2.24-5-5,0-1.87,1.03-3.51,2.56-4.36-.04-.21-.06-.42-.06-.64,0-2.6,2.48-4.74,5.65-4.97,1.65-4.51,6.34-7.76,11.85-7.76.86,0,1.69.08,2.5.23,2.09-1.57,4.69-2.5,7.5-2.5,6.1,0,11.19,4.38,12.28,10.17,2.14.56,3.72,2.51,3.72,4.83,0,.03,0,.07-.01.1,2.29.46,4.01,2.48,4.01,4.9Z";
const DISK_TOOTH: &str = "m37.51,42.52l-4.83,13.22c-.26.71-1.1,1.02-1.76.64l-4.18-2.42c-.66-.38-.81-1.26-.33-1.84l9.01-10.8c.88-1.05,2.56-.08,2.09,1.2Z";

#[derive(Clone, Copy)]
enum Kind {
    Rect,
    Ellipse,
    FilledEllipse,
    Line,
    Stroke,
    Fill,
}

pub(super) struct Piece {
    kind: Kind,
    args: Vec<String>,
}

fn piece(kind: Kind, args: &[&str]) -> Piece {
    Piece {
        kind,
        args: args.iter().map(|text| (*text).to_owned()).collect(),
    }
}

fn rect(x: &str, y: &str, w: &str, h: &str, r: &str) -> Piece {
    piece(Kind::Rect, &[x, y, w, h, r])
}

fn ellipse(cx: &str, cy: &str, rx: &str, ry: &str) -> Piece {
    piece(Kind::Ellipse, &[cx, cy, rx, ry])
}

fn disc(cx: &str, cy: &str, rx: &str, ry: &str) -> Vec<Piece> {
    vec![
        piece(Kind::FilledEllipse, &[cx, cy, rx, ry]),
        ellipse(cx, cy, rx, ry),
    ]
}

fn dot(cx: &str, cy: &str, r: &str) -> Piece {
    piece(Kind::FilledEllipse, &[cx, cy, r, r])
}

fn line(x1: &str, y1: &str, x2: &str, y2: &str) -> Piece {
    piece(Kind::Line, &[x1, y1, x2, y2])
}

fn stroke(d: &str) -> Piece {
    piece(Kind::Stroke, &[d])
}

fn fill(d: &str) -> Piece {
    piece(Kind::Fill, &[d])
}

fn server_row(y: &str) -> Vec<Piece> {
    let d = format!(
        "m56.25,{y}c0,.27-.45.5-1,.5h-10.5c-.55,0-1-.23-1-.5s.45-.5,1-.5h10.5c.55,0,1,.23,1,.5Z"
    );
    vec![
        fill(&d),
        stroke(&d),
        dot("32.5", y, ".75"),
        dot("27.5", y, ".75"),
        dot("22.5", y, ".75"),
    ]
}

fn disk_screw(cx: &str, cy: &str) -> Piece {
    ellipse(cx, cy, ".8", ".83")
}

fn database() -> Vec<Piece> {
    vec![
        stroke(&format!("m20,57.86{CYLINDER_RIM}")),
        stroke(&format!("m20,45.95{CYLINDER_RIM}")),
        stroke(&format!("m20,34.05{CYLINDER_RIM}")),
        ellipse("40", "22.14", "20", "7.14"),
        line("20", "57.86", "20", "22.14"),
        line("60", "57.86", "60", "22.14"),
    ]
}

fn server() -> Vec<Piece> {
    let mut out = vec![
        rect("17.5", "17.5", "45", "45", "2"),
        line("17.5", "32.5", "62.5", "32.5"),
        line("17.5", "47.5", "62.5", "47.5"),
    ];
    for y in ["25", "40", "55"] {
        out.extend(server_row(y));
    }
    out
}

fn disk() -> Vec<Piece> {
    let mut out = vec![
        rect("20", "15", "40", "50", "1"),
        disk_screw("24", "19.17"),
        disk_screw("56", "19.17"),
        disk_screw("24", "60.83"),
        disk_screw("56", "60.83"),
        ellipse("40", "33.75", "14", "14.58"),
    ];
    out.extend(disc("40", "33.75", "4", "4.17"));
    out.push(fill(DISK_TOOTH));
    out
}

fn internet() -> Vec<Piece> {
    vec![
        ellipse("40", "40", "22.5", "22.5"),
        line("40", "17.5", "40", "62.5"),
        line("17.5", "40", "62.5", "40"),
        stroke("m39.99,17.51c-15.28,11.1-15.28,33.88,0,44.98"),
        stroke("m40.01,17.51c15.28,11.1,15.28,33.88,0,44.98"),
        line("19.75", "30.1", "60.25", "30.1"),
        line("19.75", "49.9", "60.25", "49.9"),
    ]
}

/// The drawn shapes of a built-in icon name, or none for every other name.
pub(super) fn shapes(name: &str) -> Option<Vec<Piece>> {
    match name {
        "database" => Some(database()),
        "server" => Some(server()),
        "disk" => Some(disk()),
        "internet" => Some(internet()),
        "cloud" => Some(vec![stroke(CLOUD)]),
        _ => None,
    }
}

struct Grid {
    origin: Point,
}

impl Grid {
    fn unit(value: i64) -> i64 {
        let d = VIEW_BOX * SCALE;
        (2 * value * i64::from(BOX) + d).div_euclid(2 * d)
    }

    fn point(&self, p: Pair) -> Option<Point> {
        Some(Point {
            x: i32::try_from(i64::from(self.origin.x) + Self::unit(p.0)).ok()?,
            y: i32::try_from(i64::from(self.origin.y) + Self::unit(p.1)).ok()?,
        })
    }

    fn length(value: i64) -> Option<i32> {
        i32::try_from(Self::unit(value)).ok()
    }

    fn at(&self, piece: &Piece, first: usize) -> Option<Point> {
        self.point((number(piece, first)?, number(piece, first + 1)?))
    }

    fn item(&self, piece: &Piece) -> Option<Item> {
        let stroked = Shape::plain(ShapeStyle::InkLine).with_width(Width::Emphasis);
        let filled = Shape::plain(ShapeStyle::Ink);
        match piece.kind {
            Kind::Rect => self.rect(piece, stroked),
            Kind::Ellipse => self.ellipse(piece, stroked),
            Kind::FilledEllipse => self.ellipse(piece, filled),
            Kind::Line => Some(Item::Polyline(PolylineItem {
                shape: stroked,
                points: vec![self.at(piece, 0)?, self.at(piece, 2)?],
                corner: 0,
            })),
            Kind::Stroke => self.path(piece, stroked),
            Kind::Fill => self.path(piece, filled),
        }
    }

    fn rect(&self, piece: &Piece, shape: Shape) -> Option<Item> {
        let (x, y) = (number(piece, 0)?, number(piece, 1)?);
        let (w, h) = (number(piece, 2)?, number(piece, 3)?);
        let (a, b) = (self.point((x, y))?, self.point((x + w, y + h))?);
        Some(Item::RoundRect(RoundRectItem {
            shape,
            rect: Rect {
                x: a.x,
                y: a.y,
                w: b.x.checked_sub(a.x)?,
                h: b.y.checked_sub(a.y)?,
            },
            r: Self::length(number(piece, 4)?)?,
        }))
    }

    fn ellipse(&self, piece: &Piece, shape: Shape) -> Option<Item> {
        let centre = self.at(piece, 0)?;
        Some(Item::Ellipse(EllipseItem {
            shape,
            cx: centre.x,
            cy: centre.y,
            rx: Self::length(number(piece, 2)?)?,
            ry: Self::length(number(piece, 3)?)?,
        }))
    }

    fn path(&self, piece: &Piece, shape: Shape) -> Option<Item> {
        let commands = convert_with(piece.args.first()?, |p| self.point(p))?;
        Some(Item::Path(PathItem { shape, commands }))
    }
}

fn number(piece: &Piece, index: usize) -> Option<i64> {
    fixed(piece.args.get(index)?)
}

/// The drawn items of one built-in icon with its design-grid origin at `at`, or none when a
/// coordinate leaves the int32 range.
pub(super) fn draw(pieces: &[Piece], at: Point) -> Option<Vec<Item>> {
    let grid = Grid { origin: at };
    pieces.iter().map(|piece| grid.item(piece)).collect()
}
