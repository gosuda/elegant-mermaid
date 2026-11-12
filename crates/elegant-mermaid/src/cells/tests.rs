use super::*;
use crate::geom::{GeomError, Point};
fn p(x: i32, y: i32) -> Point {
    Point { x, y }
}
fn rectangle(c: &mut Canvas, s: Style) {
    for (a, b) in [
        (p(0, 0), p(4, 0)),
        (p(4, 0), p(4, 2)),
        (p(4, 2), p(0, 2)),
        (p(0, 2), p(0, 0)),
    ] {
        c.put_segment(a, b, s, Token::Line)
    }
}
#[test]
fn rectangles_and_labels() {
    for (s, u, a) in [
        (
            Style::Light,
            "┌───┐\n│   │\n└───┘\n",
            "+---+\n|   |\n+---+\n",
        ),
        (
            Style::Rounded,
            "╭───╮\n│   │\n╰───╯\n",
            "+---+\n|   |\n+---+\n",
        ),
        (
            Style::Heavy,
            "┏━━━┓\n┃   ┃\n┗━━━┛\n",
            "+---+\n|   |\n+---+\n",
        ),
        (
            Style::Double,
            "╔═══╗\n║   ║\n╚═══╝\n",
            "+---+\n|   |\n+---+\n",
        ),
        (
            Style::Dotted,
            "┌┄┄┄┐\n┆   ┆\n└┄┄┄┘\n",
            "+...+\n:   :\n+...+\n",
        ),
    ] {
        let mut c = Canvas::new(5, 3).unwrap();
        rectangle(&mut c, s);
        assert_eq!(
            c.serialise(Charset::Unicode, ColorMode::None, |_| Rgb {
                r: 0,
                g: 0,
                b: 0
            }),
            u
        );
        assert_eq!(
            c.serialise(Charset::Ascii, ColorMode::None, |_| Rgb {
                r: 0,
                g: 0,
                b: 0
            }),
            a
        );
        assert!(c.put_label(1, 1, "界", 2, Token::Foreground));
        assert!(!c.put_label(0, 1, "x", 1, Token::Foreground));
        assert!(!c.put_label(2, 1, "x", 1, Token::Foreground));
    }
}
fn dots(c: &Canvas) -> Vec<Point> {
    let mut out = Vec::new();
    for y in 0..c.height() * 4 {
        for x in 0..c.width() * 2 {
            if c.cell(x / 2, y / 4).unwrap().dots & braille::dot_bit(x, y) != 0 {
                out.push(p(x, y))
            }
        }
    }
    out
}
#[test]
fn braille_stroke() {
    let expected = vec![
        p(0, 0),
        p(1, 0),
        p(2, 1),
        p(3, 1),
        p(4, 2),
        p(5, 2),
        p(6, 3),
        p(7, 3),
    ];
    for (a, b) in [(p(0, 0), p(7, 3)), (p(7, 3), p(0, 0))] {
        let mut c = Canvas::new(4, 1).unwrap();
        c.stroke_dots(a, b, Token::Line).unwrap();
        assert_eq!(dots(&c), expected)
    }
}
#[test]
fn vertices_and_overflow() {
    let e = braille::ellipse(p(0, 0), 10, 20).unwrap();
    assert_eq!(e.len(), 64);
    assert_eq!(e[0], p(10, 0));
    assert_eq!(e[16], p(0, -20));
    let a = braille::arc(p(0, 0), 10, 0, 16384).unwrap();
    assert_eq!(a.len(), 17);
    assert_eq!(a[16], p(0, 10));
    let c = braille::cubic([p(0, 0), p(16, 0), p(16, 16), p(0, 16)]).unwrap();
    assert_eq!(c.len(), 17);
    assert_eq!(c[16], p(0, 16));
    assert_eq!(braille::cell_dot(p(i32::MAX, 0)), Err(GeomError::Overflow));
    let polygon = [
        p(i32::MIN, i32::MIN),
        p(i32::MAX, i32::MAX),
        p(i32::MAX, i32::MIN),
    ];
    assert_eq!(
        braille::polygon_inside(&polygon, 128, 128),
        Err(GeomError::Overflow)
    );
}
#[test]
fn colour_goldens() {
    let mut c = Canvas::new(8, 1).unwrap();
    c.attach(0, 0, 5, Style::Light, Token::Border);
    c.attach(7, 0, 5, Style::Light, Token::Border);
    c.put_label(3, 0, "H", 1, Token::Foreground);
    c.put_label(4, 0, "i", 1, Token::Foreground);
    for (mode, want) in [
        (
            ColorMode::None,
            include_str!("../../../../internal/cells/testdata/colour/none.txt"),
        ),
        (
            ColorMode::Ansi16,
            include_str!("../../../../internal/cells/testdata/colour/ansi16.txt"),
        ),
        (
            ColorMode::Ansi256,
            include_str!("../../../../internal/cells/testdata/colour/ansi256.txt"),
        ),
        (
            ColorMode::Truecolor,
            include_str!("../../../../internal/cells/testdata/colour/truecolor.txt"),
        ),
    ] {
        assert_eq!(
            c.serialise(Charset::Unicode, mode, |_| Rgb {
                r: 139,
                g: 141,
                b: 152
            }),
            want
        )
    }
}
#[test]
fn fill_matches_ray_oracle() {
    let polygon = [p(0, 0), p(1024, 0), p(1024, 1024), p(0, 1024)];
    let mut c = Canvas::new(3, 2).unwrap();
    c.fill(&polygon, Token::Line).unwrap();
    for y in 0..8 {
        for x in 0..6 {
            let expected = x < 4 && y < 4;
            assert_eq!(
                c.cell(x / 2, y / 4).unwrap().dots & braille::dot_bit(x, y) != 0,
                expected
            )
        }
    }
}
#[test]
fn seeded_merge_permutations() {
    let mut seed = 1u32;
    for _ in 0..2000 {
        seed ^= seed << 13;
        seed ^= seed >> 17;
        seed ^= seed << 5;
        let mut a = Cell::empty();
        a.mask = (seed & 15) as u8;
        a.dots = (seed & 255) as u8;
        a.symbol = seed % 2000;
        let mut b = Cell::empty();
        b.mask = ((seed >> 4) & 15) as u8;
        b.dots = ((seed >> 8) & 255) as u8;
        assert_eq!(merge_cell(&a, &b), merge_cell(&b, &a));
        assert_eq!(merge_cell(&a, &a), a)
    }
}

#[test]
fn stroke_connectivity() {
    let mut seed = 1u32;
    for _ in 0..2000 {
        seed ^= seed << 13;
        seed ^= seed >> 17;
        seed ^= seed << 5;
        let a = p((seed % 16) as i32, ((seed >> 4) % 16) as i32);
        let b = p(((seed >> 8) % 16) as i32, ((seed >> 12) % 16) as i32);
        let mut c = Canvas::new(8, 4).unwrap();
        c.stroke_dots(a, b, Token::Line).unwrap();
        let all = dots(&c);
        let mut seen = vec![a];
        let mut cursor = 0;
        while cursor < seen.len() {
            let v = seen[cursor];
            cursor += 1;
            for q in &all {
                if (q.x - v.x).abs() <= 1 && (q.y - v.y).abs() <= 1 && !seen.contains(q) {
                    seen.push(*q);
                }
            }
        }
        assert!(seen.contains(&b));
        assert_eq!(seen.len(), all.len());
    }
}

#[test]
fn triangular_fill_independent_oracle() {
    let polygon = [p(0, 0), p(1024, 0), p(1024, 1024)];
    let mut c = Canvas::new(3, 2).unwrap();
    c.fill(&polygon, Token::Line).unwrap();
    for y in 0..8 {
        for x in 0..6 {
            let px = 256 * x + 128;
            let py = 256 * y + 128;
            let expected = px < 1024 && py <= px;
            assert_eq!(
                c.cell(x / 2, y / 4).unwrap().dots & braille::dot_bit(x, y) != 0,
                expected
            );
        }
    }
}

#[test]
fn junctions_and_bounds() {
    let mut c = Canvas::new(5, 3).unwrap();
    c.put_segment(p(0, 1), p(4, 1), Style::Light, Token::Line);
    c.put_segment(p(2, 0), p(2, 2), Style::Light, Token::Line);
    assert_eq!(c.cell(2, 1).unwrap().mask, 15);
    assert_eq!(join::glyph(Charset::Unicode, Style::Light, 15), '┼');
    assert_eq!(Canvas::new(-1, 1), Err(GeomError::Domain));
    assert_eq!(Canvas::new_braille(-1, 1), Err(GeomError::Domain));
    assert_eq!(
        Canvas::new(2, 0)
            .unwrap()
            .serialise(Charset::Unicode, ColorMode::None, |_| Rgb {
                r: 0,
                g: 0,
                b: 0
            }),
        ""
    );
    assert!(!c.put_label(4, 1, "界", 2, Token::Foreground));
}

#[test]
fn merge_order_permutations() {
    let mut writes = [Cell::empty(), Cell::empty(), Cell::empty(), Cell::empty()];
    for (i, c) in writes.iter_mut().enumerate() {
        c.mask = 1 << i;
        c.dots = 1 << (2 * i);
        c.symbol = u32::try_from(i + 63).unwrap();
        c.token = Some(Token::ALL[7 + i]);
    }
    let want = writes.iter().fold(Cell::empty(), |a, b| merge_cell(&a, b));
    let mut seed = 1u32;
    for _ in 0..200 {
        for i in (1..writes.len()).rev() {
            seed ^= seed << 13;
            seed ^= seed >> 17;
            seed ^= seed << 5;
            writes.swap(i, usize::try_from(seed).unwrap() % (i + 1));
        }
        assert_eq!(
            writes.iter().fold(Cell::empty(), |a, b| merge_cell(&a, b)),
            want
        );
    }
}

#[test]
fn stripping_sgr_preserves_text() {
    let mut c = Canvas::new(8, 1).unwrap();
    c.attach(0, 0, 5, Style::Light, Token::Border);
    c.put_label(2, 0, "界", 2, Token::Foreground);
    let lookup = |_| Rgb {
        r: 139,
        g: 141,
        b: 152,
    };
    let plain = c.serialise(Charset::Unicode, ColorMode::None, lookup);
    for mode in [ColorMode::Ansi16, ColorMode::Ansi256, ColorMode::Truecolor] {
        let coloured = c.serialise(Charset::Unicode, mode, lookup);
        let mut chars = coloured.chars();
        let mut stripped = String::new();
        while let Some(ch) = chars.next() {
            if ch == '\x1b' {
                for c in chars.by_ref() {
                    if c == 'm' {
                        break;
                    }
                }
            } else {
                stripped.push(ch)
            }
        }
        assert_eq!(stripped, plain);
    }
}
