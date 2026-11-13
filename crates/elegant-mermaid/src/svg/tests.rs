#![expect(
    clippy::unwrap_used,
    reason = "fixed oracle fixtures must render successfully"
)]
use super::*;
use crate::geom::Size;
fn sample() -> Scene {
    let node = Shape::plain(ShapeStyle::Node);
    let text = |x, label: &str| {
        Item::Text(TextItem {
            rect: Rect {
                x,
                y: 640,
                w: 3840,
                h: 2560,
            },
            role: TextRole::Label,
            size: 14,
            align: Align::Middle,
            style: TextStyle::Text,
            series: 0,
            lines: vec![vec![Run::plain(label)]],
        })
    };
    Scene::new(
        Size { w: 12800, h: 3840 },
        Dump::new("flowchart", DumpOptions::default()),
        vec![
            Group::new(GroupRole::Edge, "").with_items(vec![
                Item::Polyline(PolylineItem {
                    shape: Shape::plain(ShapeStyle::Edge),
                    corner: 512,
                    points: vec![Point { x: 4480, y: 1920 }, Point { x: 8320, y: 1920 }],
                }),
                Item::MarkerRef(MarkerRefItem {
                    marker: MarkerName::new("point").unwrap(),
                    at: Point { x: 8320, y: 1920 },
                    axis: MarkerAxis::PlusX,
                }),
            ]),
            Group::new(GroupRole::Node, "").with_items(vec![
                Item::Rect(RectItem {
                    shape: node,
                    rect: Rect {
                        x: 640,
                        y: 640,
                        w: 3840,
                        h: 2560,
                    },
                }),
                text(640, "A"),
            ]),
            Group::new(GroupRole::Node, "").with_items(vec![
                Item::RoundRect(RoundRectItem {
                    shape: node,
                    rect: Rect {
                        x: 8320,
                        y: 640,
                        w: 3840,
                        h: 2560,
                    },
                    r: 512,
                }),
                text(8320, "B"),
            ]),
        ],
    )
}
fn output(s: &Scene, o: &Options<'_>) -> String {
    let mut out = String::new();
    write(&mut out, s, o).unwrap();
    balance(&out);
    out
}
fn balance(s: &str) {
    let mut stack = Vec::new();
    for part in s.split('<').skip(1) {
        let tag = part.split('>').next().unwrap();
        if let Some(close) = tag.strip_prefix('/') {
            assert_eq!(stack.pop(), Some(close));
        } else if !tag.ends_with('/') {
            stack.push(tag.split_whitespace().next().unwrap());
        }
    }
    assert!(
        stack.is_empty(),
        "balance: contract stack.is_empty() failed; observed stack={:?}",
        stack
    );
}
#[test]
fn svg_golden() {
    assert_eq!(
        output(
            &sample(),
            &Options {
                kind: "flowchart",
                ..Options::default()
            }
        ),
        include_str!("../../../../internal/svg/testdata/two-box.svg")
    );
}
#[test]
fn svg_number() {
    for (v, want) in [
        (0, "0"),
        (128, "2"),
        (32, "0.5"),
        (1, "0.02"),
        (-96, "-1.5"),
        (8, "0.13"),
        (-8, "-0.13"),
        (2147483647, "33554431.98"),
    ] {
        assert_eq!(geometry::number(v), want);
    }
}
#[test]
fn svg_corners() {
    for (x, want) in [
        (1280, "M 0 0 L 12 0 A 8 8 0 0 1 20 8 L 20 20"),
        (384, "M 0 0 L 3 0 A 3 3 0 0 1 6 3 L 6 20"),
    ] {
        assert_eq!(
            geometry::rounded(
                &[
                    Point { x: 0, y: 0 },
                    Point { x, y: 0 },
                    Point { x, y: 1280 }
                ],
                512
            ),
            want
        );
    }
    assert_eq!(
        geometry::rounded(
            &[
                Point { x: 0, y: 0 },
                Point { x: 640, y: 0 },
                Point { x: 1280, y: 0 }
            ],
            512
        ),
        "M 0 0 L 10 0 L 20 0"
    );
}
#[test]
fn svg_markers() {
    for (axis, want) in [
        (MarkerAxis::PlusX, "10,10 2,14 2,6"),
        (MarkerAxis::MinusX, "10,10 18,6 18,14"),
        (MarkerAxis::PlusY, "10,10 6,2 14,2"),
        (MarkerAxis::MinusY, "10,10 14,18 6,18"),
    ] {
        let mut r = Renderer {
            theme: theme::resolve("").unwrap(),
            used: BTreeSet::new(),
        };
        assert!(
            r.marker(&MarkerRefItem {
                marker: MarkerName::new("point").unwrap(),
                at: Point { x: 640, y: 640 },
                axis
            })
            .unwrap()
            .contains(want),
            "svg markers: contract r.marker(&MarkerRefItem {{ marker: MarkerName::new(\"point\").unwrap(), at: Point {{ x: 640, y: 640 }}, axis }}) .unwrap() .contains(want) failed; observed predicate=false"
        );
    }
}
#[test]
fn svg_escaping_theme() {
    let s = sample();
    let o = Options {
        title: "<&\"' >\u{1}",
        description: "a&b",
        ..Options::default()
    };
    let a = output(&s, &o);
    assert!(
        a.contains("&lt;&amp;&quot;&apos; &gt;�"),
        "svg escaping theme: contract a.contains(\"&lt;&amp;&quot;&apos; &gt;�\") failed; observed predicate=false"
    );
    let b = output(
        &s,
        &Options {
            theme: "elegant-dark",
            ..o
        },
    );
    fn strip(s: &str) -> String {
        let mut out = String::new();
        let mut it = s.chars();
        while let Some(c) = it.next() {
            if c == '#' {
                out.push_str("COLOUR");
                for _ in 0..6 {
                    it.next();
                }
            } else {
                out.push(c);
            }
        }
        out
    }
    assert_eq!(strip(&a), strip(&b));
    assert_ne!(a, b);
}
#[test]
fn svg_invalid() {
    for o in [
        Options {
            text: TextMode::Paths,
            ..Options::default()
        },
        Options {
            id_prefix: "1bad",
            ..Options::default()
        },
        Options {
            theme: "absent",
            ..Options::default()
        },
        Options {
            background: "red",
            ..Options::default()
        },
    ] {
        assert!(
            write(&mut String::new(), &sample(), &o).is_err(),
            "svg invalid: contract write(&mut String::new(), &sample(), &o).is_err() failed; observed predicate=false"
        );
    }
}
