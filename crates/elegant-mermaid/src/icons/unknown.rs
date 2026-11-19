use super::path::quad_to_cubic;
use super::{BOX, Item};
use crate::geom::Point;
use crate::scene::{PathCommand, PathItem, Shape, ShapeStyle};

const UNITS_PER_EM: i64 = 2048;

#[derive(Clone, Copy)]
enum Op {
    Move,
    Line,
    Quad,
}

type Glyph = (Op, i32, i32, i32, i32);

const QUESTION_MARK: [Glyph; 34] = [
    (Op::Move, 383, 449, 0, 0),
    (Op::Line, 383, 460, 0, 0),
    (Op::Quad, 383, 597, 409, 671),
    (Op::Quad, 436, 746, 486, 789),
    (Op::Quad, 536, 833, 605, 874),
    (Op::Quad, 671, 914, 716, 975),
    (Op::Quad, 761, 1037, 761, 1124),
    (Op::Quad, 761, 1228, 690, 1289),
    (Op::Quad, 619, 1351, 518, 1351),
    (Op::Quad, 430, 1351, 355, 1295),
    (Op::Quad, 280, 1240, 272, 1115),
    (Op::Line, 82, 1115, 0, 0),
    (Op::Quad, 87, 1241, 146, 1329),
    (Op::Quad, 206, 1417, 303, 1463),
    (Op::Quad, 400, 1510, 518, 1510),
    (Op::Quad, 648, 1510, 743, 1459),
    (Op::Quad, 839, 1409, 892, 1320),
    (Op::Quad, 945, 1231, 945, 1117),
    (Op::Quad, 945, 996, 892, 910),
    (Op::Quad, 839, 824, 742, 765),
    (Op::Quad, 678, 726, 638, 689),
    (Op::Quad, 599, 653, 581, 601),
    (Op::Quad, 564, 549, 564, 460),
    (Op::Line, 564, 449, 0, 0),
    (Op::Line, 383, 449, 0, 0),
    (Op::Move, 476, -13, 0, 0),
    (Op::Quad, 420, -13, 380, 26),
    (Op::Quad, 341, 66, 341, 121),
    (Op::Quad, 341, 177, 380, 216),
    (Op::Quad, 420, 256, 476, 256),
    (Op::Quad, 532, 256, 571, 216),
    (Op::Quad, 610, 177, 610, 121),
    (Op::Quad, 610, 66, 571, 26),
    (Op::Quad, 532, -13, 476, -13),
];

fn scale(value: i32) -> i64 {
    (2 * i64::from(value) * i64::from(BOX) + UNITS_PER_EM).div_euclid(2 * UNITS_PER_EM)
}

fn points(glyph: &Glyph) -> Vec<(i64, i64)> {
    let (op, x1, y1, x2, y2) = *glyph;
    let mut out = vec![(scale(x1), -scale(y1))];
    if matches!(op, Op::Quad) {
        out.push((scale(x2), -scale(y2)));
    }
    out
}

fn shift(origin: Point, glyphs: &[Glyph]) -> (i64, i64) {
    let all: Vec<(i64, i64)> = glyphs.iter().flat_map(points).collect();
    let min_x = all.iter().map(|p| p.0).min().unwrap_or(0);
    let max_x = all.iter().map(|p| p.0).max().unwrap_or(0);
    let min_y = all.iter().map(|p| p.1).min().unwrap_or(0);
    let max_y = all.iter().map(|p| p.1).max().unwrap_or(0);
    let box_size = i64::from(BOX);
    (
        i64::from(origin.x) + (box_size - (max_x - min_x)).div_euclid(2) - min_x,
        i64::from(origin.y) + (box_size - (max_y - min_y)).div_euclid(2) - min_y,
    )
}

fn point(p: (i64, i64), by: (i64, i64)) -> Point {
    Point {
        x: i32::try_from(p.0 + by.0).unwrap_or(0),
        y: i32::try_from(p.1 + by.1).unwrap_or(0),
    }
}

pub(super) fn glyph(origin: Point) -> Vec<Item> {
    let by = shift(origin, &QUESTION_MARK);
    let mut commands = Vec::new();
    let mut current = Point { x: 0, y: 0 };
    for entry in &QUESTION_MARK {
        let mapped: Vec<Point> = points(entry).into_iter().map(|p| point(p, by)).collect();
        match (entry.0, mapped.as_slice()) {
            (Op::Move, [to]) => {
                if !commands.is_empty() {
                    commands.push(PathCommand::Close);
                }
                commands.push(PathCommand::Move(*to));
            }
            (Op::Line, [to]) => commands.push(PathCommand::Line(*to)),
            (Op::Quad, [control, to]) => commands.push(quad_to_cubic(current, *control, *to)),
            _ => {}
        }
        if let Some(last) = mapped.last() {
            current = *last;
        }
    }
    commands.push(PathCommand::Close);
    vec![Item::Path(PathItem {
        shape: Shape::plain(ShapeStyle::Ink),
        commands,
    })]
}
