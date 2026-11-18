use super::*;
use crate::geom::Size;
fn scene(w: i32, h: i32, items: Vec<Item>) -> Scene {
    Scene::new(
        Size { w, h },
        Dump::new(
            "flowchart",
            DumpOptions {
                profile: Profile::Cell,
                ..DumpOptions::default()
            },
        ),
        vec![Group::new(GroupRole::Node, "").with_items(items)],
    )
}
fn edge(points: &[(i32, i32)]) -> Item {
    Item::Polyline(PolylineItem {
        shape: Shape::plain(ShapeStyle::Edge),
        points: points.iter().map(|&(x, y)| Point { x, y }).collect(),
        corner: 0,
    })
}
fn label(x: i32, y: i32, w: i32, text: &str) -> Item {
    Item::Text(TextItem {
        rect: Rect { x, y, w, h: 1 },
        role: TextRole::Label,
        size: 14,
        align: Align::Middle,
        style: TextStyle::Text,
        series: 0,
        lines: vec![vec![Run::plain(text)]],
    })
}
fn box_item(x: i32, w: i32) -> Item {
    Item::Rect(RectItem {
        shape: Shape::plain(ShapeStyle::Node),
        rect: Rect { x, y: 0, w, h: 3 },
    })
}
#[test]
fn cells_render_hand_oracles() {
    let cases = [
        (
            scene(7, 3, vec![box_item(0, 7), label(0, 1, 7, "Hi")]),
            "┌─────┐\n│ Hi  │\n└─────┘\n",
        ),
        (
            scene(5, 4, vec![edge(&[(0, 0), (3, 0), (3, 2)])]),
            "╶──┐\n   │\n   ╵\n\n",
        ),
        (
            scene(5, 3, vec![edge(&[(0, 0), (4, 0)]), edge(&[(2, 0), (2, 2)])]),
            "╶─┬─╴\n  │\n  ╵\n",
        ),
        (
            scene(5, 3, vec![edge(&[(0, 1), (4, 1)]), edge(&[(2, 0), (2, 2)])]),
            "  ╷\n╶─┼─╴\n  ╵\n",
        ),
        (
            scene(10, 3, vec![box_item(0, 10), label(0, 1, 10, "日本語")]),
            "┌────────┐\n│ 日本語 │\n└────────┘\n",
        ),
        (
            scene(
                7,
                3,
                vec![Item::RoundRect(RoundRectItem {
                    shape: Shape::plain(ShapeStyle::Node),
                    rect: Rect {
                        x: 0,
                        y: 0,
                        w: 7,
                        h: 3,
                    },
                    r: 0,
                })],
            ),
            "╭─────╮\n│     │\n╰─────╯\n",
        ),
    ];
    for (s, want) in cases {
        let got = render(&s, &Options::default()).unwrap();
        assert_eq!(got.text, want);
        assert_eq!(got.refused_clusters, 0);
    }
}
#[test]
fn cells_render_marker_directions() {
    let unicode = ["╶─▶\n", "◀─╴\n", "╷\n│\n▼\n", "▲\n│\n╵\n"];
    let ascii = ["-->\n", "<--\n", "|\n|\nv\n", "^\n|\n|\n"];
    for (i, axis) in [
        MarkerAxis::PlusX,
        MarkerAxis::MinusX,
        MarkerAxis::PlusY,
        MarkerAxis::MinusY,
    ]
    .into_iter()
    .enumerate()
    {
        let (w, h, points, at) = if i < 2 {
            (
                3,
                1,
                vec![(0, 0), (2, 0)],
                Point {
                    x: if i == 0 { 2 } else { 0 },
                    y: 0,
                },
            )
        } else {
            (
                1,
                3,
                vec![(0, 0), (0, 2)],
                Point {
                    x: 0,
                    y: if i == 2 { 2 } else { 0 },
                },
            )
        };
        let s = scene(
            w,
            h,
            vec![
                edge(&points),
                Item::MarkerRef(MarkerRefItem {
                    marker: MarkerName::new("point").unwrap(),
                    at,
                    axis,
                }),
            ],
        );
        for (charset, want) in [(Charset::Unicode, unicode[i]), (Charset::Ascii, ascii[i])] {
            assert_eq!(
                render(
                    &s,
                    &Options {
                        charset,
                        ..Options::default()
                    }
                )
                .unwrap()
                .text,
                want
            );
        }
    }
}
#[test]
fn cells_render_label_guard() {
    let got = render(
        &scene(3, 1, vec![edge(&[(0, 0), (2, 0)]), label(0, 0, 3, "abc")]),
        &Options::default(),
    )
    .unwrap();
    assert_eq!(got.refused_clusters, 3);
    assert_eq!(got.text, "╶─╴\n");
}
#[test]
fn cells_render_demo() {
    let mut items = Vec::new();
    for (x, w, text) in [(0, 9, "Start"), (12, 10, "Choice"), (25, 8, "Done")] {
        items.push(box_item(x, w));
        items.push(label(x, 1, w, text));
    }
    items.push(edge(&[(8, 1), (12, 1)]));
    items.push(edge(&[(21, 1), (25, 1)]));
    for x in [12, 25] {
        items.push(Item::MarkerRef(MarkerRefItem {
            marker: MarkerName::new("point").unwrap(),
            at: Point { x, y: 1 },
            axis: MarkerAxis::PlusX,
        }));
    }
    assert_eq!(
        render(&scene(33, 3, items), &Options::default())
            .unwrap()
            .text,
        include_str!("../../../../../internal/cells/testdata/render/demo.txt")
    );
}
#[test]
fn cells_render_dotted_precedes_heavy() {
    let mut item = edge(&[(0, 0), (4, 0)]);
    if let Item::Polyline(line) = &mut item {
        line.shape.line = Line::Dashed;
        line.shape.width = Width::Emphasis;
    }
    let s = scene(5, 1, vec![item]);
    for (charset, want) in [(Charset::Unicode, "╶┄┄┄╴\n"), (Charset::Ascii, ".....\n")] {
        assert_eq!(
            render(
                &s,
                &Options {
                    charset,
                    ..Options::default()
                }
            )
            .unwrap()
            .text,
            want
        );
    }
}
#[test]
fn cells_render_dispatches_vector_to_the_braille_raster() {
    let s = Scene::new(
        Size { w: 1024, h: 1024 },
        Dump::new("pie", DumpOptions::default()),
        vec![],
    );
    assert_eq!(render(&s, &Options::default()).unwrap().text, "\n");
}

#[test]
fn cells_marker_symbol_widths() {
    let glyphs = crate::r#gen::markers::MARKERS
        .iter()
        .flat_map(|m| m.cell.iter().copied())
        .chain(
            crate::r#gen::cellsymbols::CELL_SYMBOLS
                .iter()
                .map(|s| s.unicode),
        )
        .chain(['┄' as u32, '┆' as u32, '⣿' as u32]);
    for code in glyphs {
        assert_eq!(
            crate::measure::cell_width(&char::from_u32(code).unwrap().to_string()).unwrap(),
            1
        );
    }
}
#[test]
fn cells_render_properties() {
    for seed in 1u32..=100 {
        let mut state = seed;
        state ^= state << 13;
        state ^= state >> 17;
        state ^= state << 5;
        let n = i32::try_from(state % 8 + 2).unwrap();
        let mut items = Vec::new();
        for x in 0..n {
            items.push(box_item(x * 6, 5));
            items.push(label(x * 6, 1, 5, "A"));
        }
        let got = render(
            &scene(n * 6, 4, items),
            &Options {
                charset: Charset::Ascii,
                ..Options::default()
            },
        )
        .unwrap();
        assert!(
            got.text.is_ascii(),
            "cells render properties: contract got.text.is_ascii() failed; observed text={:?}, got.text={:?}",
            got.text,
            got.text
        );
        assert_eq!(got.text.lines().count(), 4);
        assert!(
            got.text.lines().all(|line| !line.ends_with(' ')),
            "cells render properties: contract got.text.lines().all(|line| !line.ends_with(' ')) failed; observed text={:?}, lines={:?}, got.text={:?}",
            got.text,
            got.text.lines().collect::<Vec<_>>(),
            got.text
        );
    }
}
#[test]
fn cells_placement_alignment_and_occupancy() {
    let mut canvas = Canvas::new(7, 2).unwrap();
    canvas.put_symbol(0, 0, u32::from('●'));
    let mut t = match label(0, 0, 7, "界AB") {
        Item::Text(t) => t,
        _ => unreachable!(
            "label(0, 0, 7, \"界AB\") must construct Item::Text; observed a non-Text variant"
        ),
    };
    t.align = Align::Start;
    let theme = theme::resolve("").unwrap();
    assert_eq!(canvas.place_all(&[&t], &theme).unwrap(), 1);
    assert_eq!(
        canvas.serialise(Charset::Unicode, ColorMode::None, |token| theme
            .colour(token)),
        "● AB\n\n"
    );
    assert_eq!(
        super::super::place::line_start(Align::Middle, 0, 1, 4).unwrap(),
        -2
    );
    assert_eq!(
        super::super::place::line_start(Align::End, 0, 1, 4).unwrap(),
        -3
    );
    t.rect.y = 1;
    t.align = Align::End;
    assert_eq!(canvas.place_all(&[&t, &t], &theme).unwrap(), 3);
}
#[test]
fn cells_shapes_use_dots_and_symbols() {
    let shape = Shape::plain(ShapeStyle::Ink);
    let items = vec![
        Item::Rect(RectItem {
            shape,
            rect: Rect {
                x: 0,
                y: 0,
                w: 3,
                h: 1,
            },
        }),
        Item::Ellipse(EllipseItem {
            shape,
            cx: 4,
            cy: 0,
            rx: 1,
            ry: 1,
        }),
        Item::Polygon(PolygonItem {
            shape,
            points: vec![
                Point { x: 6, y: 0 },
                Point { x: 7, y: 0 },
                Point { x: 6, y: 1 },
            ],
        }),
        Item::SymbolRef(SymbolRefItem {
            symbol: SymbolName::new("cloud").unwrap(),
            at: Point { x: 8, y: 0 },
            style: ShapeStyle::InkLine,
        }),
    ];
    for (charset, want) in [
        (Charset::Unicode, "⣿⣿⣿ ● ◆ ☁\n\n"),
        (Charset::Ascii, "### * * ~\n\n"),
    ] {
        assert_eq!(
            render(
                &scene(9, 2, items.clone()),
                &Options {
                    charset,
                    ..Options::default()
                }
            )
            .unwrap()
            .text,
            want
        );
    }
}
#[test]
fn cells_mixed_polyline_is_entirely_dots() {
    let item = edge(&[(0, 0), (3, 0), (4, 2)]);
    let got = render(&scene(6, 4, vec![item]), &Options::default()).unwrap();
    let mut expected = Canvas::new(6, 4).unwrap();
    let dots = [
        Point { x: 0, y: 2 },
        Point { x: 6, y: 2 },
        Point { x: 8, y: 10 },
    ];
    for pair in dots.windows(2) {
        expected.stroke_dots(pair[0], pair[1], Token::Line).unwrap();
    }
    assert_eq!(
        got.text,
        expected.serialise(Charset::Unicode, ColorMode::None, |_| {
            theme::Colour::default()
        })
    );
}
#[test]
fn cells_path_commands_match_dot_geometry() {
    let shape = Shape::plain(ShapeStyle::Edge);
    let p = |x, y| Point { x, y };
    let commands = vec![
        PathCommand::Move(p(1, 1)),
        PathCommand::Line(p(4, 1)),
        PathCommand::Curve {
            c1: p(5, 1),
            c2: p(5, 3),
            to: p(4, 3),
        },
        PathCommand::Close,
        PathCommand::Move(p(3, 2)),
        PathCommand::Arc {
            centre: p(2, 2),
            r: 1,
            start: 0,
            sweep: 16384,
        },
    ];
    let got = render(
        &scene(8, 6, vec![Item::Path(PathItem { shape, commands })]),
        &Options::default(),
    )
    .unwrap();
    assert!(
        got.text.contains('⠤'),
        "cells path commands match dot geometry: contract got.text.contains('⠤') failed; observed text={:?}, got.text={:?}",
        got.text,
        got.text
    );
    assert_eq!(got.text.lines().count(), 6);
}

#[test]
fn cells_sloped_hand_oracle() {
    assert_eq!(
        render(
            &scene(2, 2, vec![edge(&[(0, 0), (1, 1)])]),
            &Options::default()
        )
        .unwrap()
        .text,
        "⢄\n⠈⠆\n"
    );
}
#[test]
fn cells_large_ellipse_and_invisible_styles() {
    let ellipse = EllipseItem {
        shape: Shape::plain(ShapeStyle::Edge),
        cx: 3,
        cy: 2,
        rx: 2,
        ry: 2,
    };
    let got = render(
        &scene(7, 5, vec![Item::Ellipse(ellipse)]),
        &Options::default(),
    )
    .unwrap();
    let mut expected = Canvas::new(7, 5).unwrap();
    let mut points = braille::ellipse(Point { x: 6, y: 10 }, 4, 8).unwrap();
    points.push(points[0]);
    for pair in points.windows(2) {
        expected.stroke_dots(pair[0], pair[1], Token::Line).unwrap();
    }
    assert_eq!(
        got.text,
        expected.serialise(Charset::Unicode, ColorMode::None, |_| {
            theme::Colour::default()
        })
    );
    let mut hidden = ellipse;
    hidden.shape = Shape::plain(ShapeStyle::Band);
    assert_eq!(
        render(
            &scene(7, 5, vec![Item::Ellipse(hidden)]),
            &Options::default()
        )
        .unwrap()
        .text,
        "\n\n\n\n\n"
    );
}
