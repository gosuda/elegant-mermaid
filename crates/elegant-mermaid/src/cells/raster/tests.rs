use super::*;
use crate::cells::{Charset, ColorMode, braille::dot_bit};
use crate::geom::{Point, Rect, Size, cos_q15, sin_q15};
use crate::scene::{
    Align, Dump, DumpOptions, Group, GroupRole, MarkerName, PathCommand, PolylineItem, RectItem,
    Run, SymbolName, SymbolRefItem, TextStyle,
};
use std::collections::BTreeSet;

type Dots = BTreeSet<(i64, i64)>;

fn scene(profile: Profile, w: i32, h: i32, items: Vec<Item>) -> Scene {
    Scene::new(
        Size { w, h },
        Dump::new(
            "xychart",
            DumpOptions {
                profile,
                ..DumpOptions::default()
            },
        ),
        vec![Group::new(GroupRole::Node, "").with_items(items)],
    )
}

fn vector(w: i32, h: i32, items: Vec<Item>) -> Scene {
    scene(Profile::Vector, w, h, items)
}

fn text_of(scene: &Scene, charset: Charset) -> (String, usize) {
    let options = Options {
        charset,
        color: ColorMode::None,
        theme: String::new(),
    };
    let result = crate::cells::render(scene, &options).unwrap();
    (result.text, result.refused_clusters)
}

fn add_cell_dots(out: &mut Dots, col: usize, row: usize, bits: u8) {
    let (col, row) = (i64::try_from(col).unwrap(), i64::try_from(row).unwrap());
    for dx in 0..2i32 {
        for dy in 0..4i32 {
            if bits & dot_bit(dx, dy) != 0 {
                out.insert((2 * col + i64::from(dx), 4 * row + i64::from(dy)));
            }
        }
    }
}

fn dots_of(text: &str) -> Dots {
    let mut out = Dots::new();
    for (row, line) in text.lines().enumerate() {
        for (col, glyph) in line.chars().enumerate() {
            let code = u32::from(glyph);
            if (0x2800..0x2900).contains(&code) {
                add_cell_dots(&mut out, col, row, u8::try_from(code - 0x2800).unwrap());
            }
        }
    }
    out
}

fn inside(ring: &[Point], px: i64, py: i64) -> bool {
    let mut count = 0;
    for (i, a) in ring.iter().enumerate() {
        let b = ring[(i + 1) % ring.len()];
        let (ay, by) = (i64::from(a.y), i64::from(b.y));
        if !((ay <= py && py < by) || (by <= py && py < ay)) {
            continue;
        }
        let lhs = (i64::from(b.x) - i64::from(a.x)) * (py - ay) + (i64::from(a.x) - px) * (by - ay);
        if lhs * (by - ay) > 0 {
            count += 1;
        }
    }
    count % 2 == 1
}

fn oracle_fill(ring: &[Point], columns: i64, rows: i64) -> Dots {
    let mut out = Dots::new();
    for j in 0..rows * 4 {
        for i in 0..columns * 2 {
            if inside(ring, 256 * i + 128, 256 * j + 128) {
                out.insert((i, j));
            }
        }
    }
    out
}

fn oracle_line(a: (i64, i64), b: (i64, i64), out: &mut Dots) {
    let (mut x, mut y) = a;
    let dx = (b.0 - x).abs();
    let dy = -(b.1 - y).abs();
    let sx = if x < b.0 { 1 } else { -1 };
    let sy = if y < b.1 { 1 } else { -1 };
    let mut err = dx + dy;
    loop {
        out.insert((x, y));
        if (x, y) == b {
            return;
        }
        let e2 = 2 * err;
        if e2 >= dy {
            err += dy;
            x += sx;
        }
        if e2 <= dx {
            err += dx;
            y += sy;
        }
    }
}

fn oracle_stroke_open(points: &[Point], out: &mut Dots) {
    for pair in points.windows(2) {
        let (a, b) = (pair[0], pair[1]);
        oracle_line(
            (i64::from(a.x) >> 8, i64::from(a.y) >> 8),
            (i64::from(b.x) >> 8, i64::from(b.y) >> 8),
            out,
        );
    }
}

fn oracle_stroke_closed(points: &[Point], out: &mut Dots) {
    let ring: Vec<Point> = points.iter().chain(points.first()).copied().collect();
    oracle_stroke_open(&ring, out);
}

fn rect_item(style: ShapeStyle, rect: Rect) -> Item {
    Item::Rect(RectItem {
        shape: Shape::plain(style),
        rect,
    })
}

fn polyline(points: &[(i32, i32)]) -> Item {
    Item::Polyline(PolylineItem {
        shape: Shape::plain(ShapeStyle::Edge),
        corner: 0,
        points: points.iter().map(|&(x, y)| Point { x, y }).collect(),
    })
}

fn label(x: i32, y: i32, w: i32, align: Align, role: TextRole, lines: &[&str]) -> Item {
    Item::Text(TextItem {
        rect: Rect {
            x,
            y,
            w,
            h: i32::try_from(lines.len()).unwrap() * 1280,
        },
        role,
        size: 14,
        align,
        style: TextStyle::Text,
        series: 0,
        lines: lines.iter().map(|l| vec![Run::plain(*l)]).collect(),
    })
}

fn pt(x: i32, y: i32) -> Point {
    Point { x, y }
}

#[test]
fn circle_fill_matches_spec_oracle() {
    let (cx, cy, rx, ry) = (5 * 512, 3 * 1024, 4 * 512, 3 * 1024);
    let ring: Vec<Point> = (0..64)
        .map(|j| {
            let a = j * 1024;
            pt(
                cx + i32::try_from((i64::from(rx) * i64::from(cos_q15(a))).div_euclid(32768))
                    .unwrap(),
                cy - i32::try_from((i64::from(ry) * i64::from(sin_q15(a))).div_euclid(32768))
                    .unwrap(),
            )
        })
        .collect();
    let item = Item::Ellipse(EllipseItem {
        shape: Shape::plain(ShapeStyle::Ink),
        cx,
        cy,
        rx,
        ry,
    });
    let (text, _) = text_of(&vector(10 * 512, 6 * 1024, vec![item]), Charset::Unicode);
    let want = oracle_fill(&ring, 10, 6);
    assert!(want.len() > 100);
    assert_eq!(dots_of(&text), want);
}

#[test]
fn series_rect_fills_then_outlines() {
    let ring = [pt(300, 500), pt(2000, 500), pt(2000, 2000), pt(300, 2000)];
    let item = rect_item(
        ShapeStyle::Series,
        Rect {
            x: 300,
            y: 500,
            w: 1700,
            h: 1500,
        },
    );
    let (text, _) = text_of(&vector(4 * 512, 3 * 1024, vec![item]), Charset::Unicode);
    let mut want = oracle_fill(&ring, 4, 3);
    oracle_stroke_closed(&ring, &mut want);
    assert_eq!(dots_of(&text), want);
}

#[test]
fn diagonal_stroke_matches_spec_oracle() {
    let (a, b) = (pt(130, 70), pt(2900, 3700));
    let item = polyline(&[(a.x, a.y), (b.x, b.y)]);
    let (text, _) = text_of(&vector(6 * 512, 4 * 1024, vec![item]), Charset::Unicode);
    let mut want = Dots::new();
    oracle_stroke_open(&[a, b], &mut want);
    let got = dots_of(&text);
    assert!(got.contains(&(0, 0)) && got.contains(&(11, 14)));
    assert_eq!(got, want);
}

#[test]
fn style_cell_column_selects_the_parts() {
    let ring = [pt(256, 256), pt(1792, 256), pt(1792, 1792), pt(256, 1792)];
    let fill_only = oracle_fill(&ring, 4, 2);
    let mut outline_only = Dots::new();
    oracle_stroke_closed(&ring, &mut outline_only);
    let cases = [
        (ShapeStyle::Ink, fill_only),
        (ShapeStyle::Node, outline_only.clone()),
        (ShapeStyle::SeriesTint, outline_only),
        (ShapeStyle::Band, Dots::new()),
    ];
    for (style, want) in cases {
        let item = rect_item(
            style,
            Rect {
                x: 256,
                y: 256,
                w: 1536,
                h: 1536,
            },
        );
        let (text, _) = text_of(&vector(4 * 512, 2 * 1024, vec![item]), Charset::Unicode);
        assert_eq!(dots_of(&text), want, "{style:?}");
    }
}

#[test]
fn arc_slice_path_fills_the_polygon_of_centre_and_arc() {
    let centre = pt(2048, 2048);
    let start = pt(2048, 2048 - 1536);
    let item = Item::Path(PathItem {
        shape: Shape::plain(ShapeStyle::Series).with_series(1),
        commands: vec![
            PathCommand::Move(centre),
            PathCommand::Line(start),
            PathCommand::Arc {
                centre,
                r: 1536,
                start: -16384,
                sweep: 16384,
            },
            PathCommand::Close,
        ],
    });
    let (text, _) = text_of(&vector(8 * 512, 4 * 1024, vec![item]), Charset::Unicode);
    let mut ring = vec![centre, start];
    ring.extend(braille::arc(centre, 1536, -16384, 16384).unwrap());
    let mut want = oracle_fill(&ring, 8, 4);
    oracle_stroke_closed(&ring, &mut want);
    let got = dots_of(&text);
    assert!(got.contains(&(8, 4)));
    assert_eq!(got, want);
}

#[test]
fn cubic_path_is_sixteen_straight_segments() {
    let p = [pt(0, 1500), pt(1500, 1500), pt(1500, 300), pt(3000, 300)];
    let item = Item::Path(PathItem {
        shape: Shape::plain(ShapeStyle::SeriesFlow).with_series(2),
        commands: vec![
            PathCommand::Move(p[0]),
            PathCommand::Curve {
                c1: p[1],
                c2: p[2],
                to: p[3],
            },
        ],
    });
    let (text, _) = text_of(&vector(6 * 512, 2 * 1024, vec![item]), Charset::Unicode);
    let axis = |v: [i32; 4], k: i64| {
        let t = 16 - k;
        let sum = t * t * t * i64::from(v[0])
            + 3 * k * t * t * i64::from(v[1])
            + 3 * k * k * t * i64::from(v[2])
            + k * k * k * i64::from(v[3])
            + 2048;
        i32::try_from(sum.div_euclid(4096)).unwrap()
    };
    let pts: Vec<Point> = (0..17)
        .map(|k| {
            pt(
                axis([p[0].x, p[1].x, p[2].x, p[3].x], k),
                axis([p[0].y, p[1].y, p[2].y, p[3].y], k),
            )
        })
        .collect();
    let mut want = Dots::new();
    oracle_stroke_open(&pts, &mut want);
    assert_eq!(dots_of(&text), want);
}

#[test]
fn canvas_size_is_ceil_of_columns_and_rows() {
    let cases = [
        (0, 0, 0),
        (1, 1, 1),
        (512, 1024, 1),
        (513, 1025, 2),
        (5120, 2048, 2),
    ];
    for (w, h, rows) in cases {
        let item = rect_item(ShapeStyle::Ink, Rect { x: 0, y: 0, w, h });
        let (text, _) = text_of(&vector(w, h, vec![item]), Charset::Unicode);
        assert_eq!(text.matches('\n').count(), rows, "{w}x{h}");
    }
}

#[test]
fn glyphs_in_both_charsets() {
    let item = rect_item(
        ShapeStyle::Ink,
        Rect {
            x: 0,
            y: 0,
            w: 512,
            h: 1024,
        },
    );
    let s = vector(1024, 1024, vec![item]);
    assert_eq!(text_of(&s, Charset::Unicode).0, "\u{28ff}\n");
    assert_eq!(text_of(&s, Charset::Ascii).0, "#\n");
}

#[test]
fn label_placement_rows_columns_and_refusal() {
    use Align::{End, Middle, Start};
    use TextRole::{Label, Title};
    let cases = [
        (
            3,
            label(1024, 1024, 2048, Start, Label, &["ab"]),
            "\n  ab\n\n",
            0,
        ),
        (
            3,
            label(0, 0, 5 * 512, Middle, Label, &["ab"]),
            " ab\n\n\n",
            0,
        ),
        (
            3,
            label(0, 0, 5 * 512, End, Label, &["ab"]),
            "   ab\n\n\n",
            0,
        ),
        (
            3,
            label(512, 0, 512, Middle, Label, &["abcd"]),
            "bcd\n\n\n",
            1,
        ),
        (
            3,
            label(0, 700, 2048, Start, Label, &["x", "y"]),
            "x\ny\n\n",
            0,
        ),
        (
            3,
            label(0, 0, 2048, Start, Label, &["x", "y", "z"]),
            "x\ny\nz\n",
            0,
        ),
        (
            4,
            label(0, 0, 2048, Start, Title, &["x", "y", "z"]),
            "x\ny\n\nz\n",
            0,
        ),
        (
            3,
            label(0, 3 * 1024, 2048, Start, Label, &["x"]),
            "\n\n\n",
            1,
        ),
    ];
    for (rows, item, want, refused) in cases {
        let s = vector(7 * 512, rows * 1024, vec![item]);
        assert_eq!(text_of(&s, Charset::Unicode), (want.to_owned(), refused));
    }
}

#[test]
fn label_overwrites_dots_but_not_another_label() {
    let full = rect_item(
        ShapeStyle::Ink,
        Rect {
            x: 0,
            y: 0,
            w: 4 * 512,
            h: 1024,
        },
    );
    let first = label(0, 0, 4 * 512, Align::Start, TextRole::Label, &["hi"]);
    let second = label(512, 0, 1024, Align::Start, TextRole::Label, &["xyz"]);
    let s = vector(4 * 512, 1024, vec![full, first, second]);
    assert_eq!(text_of(&s, Charset::Unicode), ("hiyz\n".to_owned(), 1));
    let off = vector(
        512,
        1024,
        vec![label(-2048, 0, 512, Align::Start, TextRole::Label, &["ab"])],
    );
    assert_eq!(text_of(&off, Charset::Unicode), ("\n".to_owned(), 2));
}

#[test]
fn markers_symbols_and_profiles() {
    let marker = Item::MarkerRef(MarkerRefItem {
        marker: MarkerName::new("point").unwrap(),
        at: pt(2048, 1024),
        axis: MarkerAxis::PlusX,
    });
    let (text, _) = text_of(&vector(5 * 512, 2 * 1024, vec![marker]), Charset::Unicode);
    assert!(!dots_of(&text).is_empty());
    let symbol = Item::SymbolRef(SymbolRefItem {
        symbol: SymbolName::new("disc").unwrap(),
        at: pt(0, 0),
        style: ShapeStyle::Ink,
    });
    let options = Options::default();
    assert!(matches!(
        crate::cells::render(&vector(512, 1024, vec![symbol]), &options),
        Err(RenderError::Geometry(GeomError::Domain))
    ));
    let cell = scene(Profile::Cell, 2, 2, Vec::new());
    assert!(matches!(
        render_braille(&cell, &options),
        Err(RenderError::Profile(ProfileError {
            want: Profile::Vector,
            got: Profile::Cell
        }))
    ));
}

fn canvas_dots(canvas: &Canvas, columns: i32, rows: i32) -> Dots {
    let mut out = Dots::new();
    for (x, y) in (0..rows * 4).flat_map(|y| (0..columns * 2).map(move |x| (x, y))) {
        let cell = canvas.cell(x / 2, y / 4).unwrap();
        if cell.dots & dot_bit(x, y) != 0 {
            out.insert((i64::from(x), i64::from(y)));
        }
    }
    out
}

#[test]
fn fill_window_equals_full_scan() {
    let mut state = 7u32;
    let mut next = |n: u32| {
        state ^= state << 13;
        state ^= state >> 17;
        state ^= state << 5;
        i32::try_from(state % n).unwrap()
    };
    for _ in 0..200 {
        let count = 3 + usize::try_from(next(5)).unwrap();
        let ring: Vec<Point> = (0..count)
            .map(|_| pt(next(5000) - 600, next(3500) - 300))
            .collect();
        let mut canvas = Canvas::new_braille(4 * 512, 3 * 1024).unwrap();
        canvas.fill(&ring, Token::Foreground).unwrap();
        assert_eq!(canvas_dots(&canvas, 4, 3), oracle_fill(&ring, 4, 3));
    }
}
