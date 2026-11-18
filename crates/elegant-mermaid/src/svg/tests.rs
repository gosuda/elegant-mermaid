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
fn svg_two_boxes_preserve_geometry_text_and_accessibility() {
    let svg = output(
        &sample(),
        &Options {
            kind: "flowchart",
            ..Options::default()
        },
    );
    let tags: Vec<_> = svg
        .split('<')
        .skip(1)
        .filter_map(|part| part.split_once('>').map(|(tag, _)| tag))
        .collect();
    assert_svg_canvas(&tags);
    assert_svg_accessibility(&svg, &tags);
    assert_svg_node_geometry(&tags);
    assert_svg_node_text(&svg, &tags);
}

fn assert_svg_canvas(tags: &[&str]) {
    let root = tags.iter().find(|tag| tag.starts_with("svg ")).unwrap();
    assert_eq!(attribute(root, "xmlns"), Some("http://www.w3.org/2000/svg"));
    assert_eq!(attribute(root, "viewBox"), Some("0 0 200 60"));
    assert_eq!(attribute(root, "width"), Some("200"));
    assert_eq!(attribute(root, "height"), Some("60"));
}

fn assert_svg_accessibility(svg: &str, tags: &[&str]) {
    let root = tags.iter().find(|tag| tag.starts_with("svg ")).unwrap();
    assert_eq!(attribute(root, "role"), Some("graphics-document document"));
    assert_eq!(attribute(root, "aria-roledescription"), Some("diagram"));
    let title_id = attribute(root, "aria-labelledby").unwrap();
    let title = tags.iter().find(|tag| tag.starts_with("title ")).unwrap();
    assert_eq!(attribute(title, "id"), Some(title_id));
    assert!(
        svg.contains(">Mermaid flowchart diagram</title>"),
        "SVG must include the default accessible flowchart title; SVG: {svg}"
    );
}

fn assert_svg_node_geometry(tags: &[&str]) {
    let boxes: Vec<_> = tags
        .iter()
        .filter(|tag| tag.starts_with("rect ") && attribute(tag, "class") == Some("emd-s-node"))
        .collect();
    assert_eq!(boxes.len(), 2);
    for (tag, x) in boxes.iter().zip(["10", "130"]) {
        assert_eq!(attribute(tag, "x"), Some(x));
        assert_eq!(attribute(tag, "y"), Some("10"));
        assert_eq!(attribute(tag, "width"), Some("60"));
        assert_eq!(attribute(tag, "height"), Some("40"));
    }
    assert_eq!(attribute(boxes[1], "rx"), Some("8"));
    assert_eq!(attribute(boxes[1], "ry"), Some("8"));
    assert_eq!(
        tags.iter()
            .filter(|tag| attribute(tag, "class") == Some("emd-node"))
            .count(),
        2
    );
}

fn assert_svg_node_text(svg: &str, tags: &[&str]) {
    let labels: Vec<_> = tags.iter().filter(|tag| tag.starts_with("text ")).collect();
    assert_eq!(labels.len(), 2);
    for (tag, x) in labels.iter().zip(["40", "160"]) {
        assert_eq!(attribute(tag, "x"), Some(x));
        assert_eq!(attribute(tag, "text-anchor"), Some("middle"));
        assert_eq!(attribute(tag, "font-size"), Some("14"));
    }
    let lines: Vec<_> = tags
        .iter()
        .filter(|tag| tag.starts_with("tspan "))
        .collect();
    assert_eq!(lines.len(), 2);
    for line in lines {
        assert_eq!(attribute(line, "y"), Some("24.89"));
    }
    assert!(
        svg.contains(">A</tspan>"),
        "first node label must preserve A in a tspan; SVG: {svg}"
    );
    assert!(
        svg.contains(">B</tspan>"),
        "second node label must preserve B in a tspan; SVG: {svg}"
    );
}

fn attribute<'a>(tag: &'a str, name: &str) -> Option<&'a str> {
    let start = tag.find(&format!(" {name}="))? + name.len() + 2;
    let value = &tag[start..];
    let quote = value.chars().next()?;
    if quote != '\'' && quote != '"' {
        return None;
    }
    value[1..].split_once(quote).map(|(value, _)| value)
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
        let mut r = Renderer::new(theme::resolve("").unwrap(), Look::default());
        assert!(
            r.marker(
                &MarkerRefItem {
                    marker: MarkerName::new("point").unwrap(),
                    at: Point { x: 640, y: 640 },
                    axis
                },
                0
            )
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

#[test]
fn corpus_svg_titles() -> Result<(), Box<dyn std::error::Error>> {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let inventory = std::process::Command::new("python3")
        .args([
            "-c",
            "import json\nv=json.load(open('corpus/verdicts.json'))\nfor p in sorted(v): print(p)",
        ])
        .current_dir(&root)
        .output()?;
    assert!(
        inventory.status.success(),
        "{}",
        String::from_utf8_lossy(&inventory.stderr)
    );
    let paths = String::from_utf8(inventory.stdout)?;
    assert!(!paths.is_empty(), "no corpus fixtures");
    let mut accepted = 0;
    let mut failures = Vec::new();
    for path in paths.lines() {
        let source = std::fs::read(root.join(path))?;
        let document = crate::parse_bytes(&source);
        if document.has_errors() {
            continue;
        }
        accepted += 1;
        let svg = match crate::render_svg(&document, &crate::SvgOptions::default()) {
            Ok(svg) => svg,
            Err(error) => {
                failures.push(format!("{path}: {error}"));
                continue;
            }
        };
        let root_tag = svg.split('<').find_map(|part| {
            part.strip_prefix("svg ")
                .and_then(|tag| tag.split_once('>').map(|(tag, _)| tag))
        });
        let labelled_by = root_tag.and_then(|tag| attribute(tag, "aria-labelledby"));
        let has_title = svg.split('<').any(|part| {
            let Some((tag, content)) = part.split_once('>') else {
                return false;
            };
            tag.starts_with("title ")
                && labelled_by.is_some_and(|id| !id.is_empty() && attribute(tag, "id") == Some(id))
                && !content.trim().is_empty()
        });
        if !has_title {
            failures.push(format!(
                "{path}: SVG has no non-empty title referenced by aria-labelledby"
            ));
        }
    }
    assert!(accepted > 0, "no accepted corpus fixtures");
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    Ok(())
}
