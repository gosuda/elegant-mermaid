use elegant_mermaid::{layout, model, scene, syntax};

fn demo_input(profile: scene::Profile) -> layout::input::Input {
    let source = "flowchart LR\n  A[Start] --> B{Choice}\n  B -->|yes| C[Done]\n  B -->|no| A\n";
    let parsed = syntax::flowchart::parse(source, &[]);
    let (model, _) = model::flowchart::resolve(source, &parsed.document);
    layout::flowchart::from_flowchart(&model, profile, scene::DumpOptions::default())
}

#[test]
fn pipeline_demo_geometry_equations() -> Result<(), Box<dyn std::error::Error>> {
    for (profile, widths, minimum_height, margin, rank_gap) in [
        (scene::Profile::Vector, [3622, 4577, 3807], 2304, 1024, 3072),
        (scene::Profile::Cell, [9, 10, 8], 3, 1, 3),
    ] {
        let input = demo_input(profile);
        let rendered = layout::families::layout(&input)?.0;
        assert!(rendered.check()?);
        assert_eq!(
            rendered
                .boxes()
                .iter()
                .map(|b| b.id.as_str())
                .collect::<Vec<_>>(),
            ["A", "B", "C"]
        );
        for (node, width) in rendered.boxes().iter().zip(widths) {
            assert_eq!(node.rect.w, width);
            assert_eq!(node.rect.h, minimum_height);
        }
        let boxes = rendered.boxes();
        assert_eq!(boxes[0].rect.x, margin);
        assert!(boxes[1].rect.x >= boxes[0].rect.x + boxes[0].rect.w + rank_gap);
        assert!(boxes[2].rect.x >= boxes[1].rect.x + boxes[1].rect.w + 2 * rank_gap);
        assert!(rendered.canvas().w >= boxes[2].rect.x + boxes[2].rect.w + margin);
        assert_eq!(rendered.dump(), layout::families::layout(&input)?.0.dump());
    }
    Ok(())
}

#[test]
fn pipeline_demo_preserves_node_and_route_text() -> Result<(), Box<dyn std::error::Error>> {
    for profile in [scene::Profile::Vector, scene::Profile::Cell] {
        let input = demo_input(profile);
        let rendered = layout::families::layout(&input)?.0;
        assert_eq!(
            rendered
                .labels()
                .iter()
                .map(|label| (label.id.as_str(), label.owner.as_str(), label.text.as_str()))
                .collect::<Vec<_>>(),
            [("e1.label", "e1", "yes"), ("e2.label", "e2", "no")]
        );
        let node_text = rendered
            .items()
            .iter()
            .filter(|group| ["A", "B", "C"].contains(&group.owner.as_str()))
            .flat_map(|group| {
                group.items.iter().filter_map(|item| match item {
                    scene::Item::Text(text) => Some((
                        group.owner.as_str(),
                        text.lines
                            .iter()
                            .map(|line| {
                                line.iter().map(|run| run.text.as_str()).collect::<String>()
                            })
                            .collect::<Vec<_>>()
                            .join("\n"),
                    )),
                    _ => None,
                })
            })
            .collect::<Vec<_>>();
        assert_eq!(
            node_text,
            [
                ("A", "Start".into()),
                ("B", "Choice".into()),
                ("C", "Done".into())
            ]
        );
    }
    Ok(())
}

#[test]
fn pipeline_demo_routes_join_boundaries_and_clear_nodes() -> Result<(), Box<dyn std::error::Error>>
{
    for profile in [scene::Profile::Vector, scene::Profile::Cell] {
        let input = demo_input(profile);
        let rendered = layout::families::layout(&input)?.0;
        let boxes = rendered.boxes();
        for (route, (from, to)) in rendered.routes().iter().zip([(0, 1), (1, 2), (1, 0)]) {
            let first = route.points.first().ok_or("missing route start")?;
            let last = route.points.last().ok_or("missing route end")?;
            assert_eq!(
                first.x,
                boxes[from].rect.x + if from < to { boxes[from].rect.w } else { 0 }
            );
            assert_eq!(
                last.x,
                boxes[to].rect.x + if from < to { 0 } else { boxes[to].rect.w }
            );
            assert!(
                route
                    .points
                    .windows(2)
                    .all(|p| p[0].x == p[1].x || p[0].y == p[1].y)
            );
        }
        let reversed = &rendered.routes()[2].points;
        assert_eq!(reversed.len(), 6);
        assert_eq!(reversed[2].y, reversed[3].y);
        assert!(
            reversed[2].y
                > boxes
                    .iter()
                    .map(|b| b.rect.y + b.rect.h)
                    .max()
                    .ok_or("missing boxes")?
        );
        assert!(rendered.canvas().h > reversed[2].y);
    }
    Ok(())
}

fn edge_input() -> layout::input::Input {
    let source = "flowchart LR\nA --> B\n";
    let parsed = syntax::flowchart::parse(source, &[]);
    let (model, _) = model::flowchart::resolve(source, &parsed.document);
    layout::flowchart::from_flowchart(
        &model,
        scene::Profile::Vector,
        scene::DumpOptions::default(),
    )
}

#[test]
fn pipeline_flowchart_edge_scene() -> Result<(), Box<dyn std::error::Error>> {
    for (start, end, stroke, names, line, width) in [
        (
            "none",
            "none",
            "normal",
            vec![],
            scene::Line::Solid,
            scene::Width::Normal,
        ),
        (
            "point",
            "point",
            "normal",
            vec!["point", "point"],
            scene::Line::Solid,
            scene::Width::Normal,
        ),
        (
            "circle",
            "circle",
            "normal",
            vec!["circle", "circle"],
            scene::Line::Solid,
            scene::Width::Normal,
        ),
        (
            "cross",
            "cross",
            "normal",
            vec!["cross", "cross"],
            scene::Line::Solid,
            scene::Width::Normal,
        ),
        (
            "none",
            "point",
            "dotted",
            vec!["point"],
            scene::Line::Dotted,
            scene::Width::Normal,
        ),
        (
            "none",
            "point",
            "thick",
            vec!["point"],
            scene::Line::Solid,
            scene::Width::Emphasis,
        ),
        (
            "none",
            "point",
            "dashed",
            vec!["point"],
            scene::Line::Dashed,
            scene::Width::Normal,
        ),
    ] {
        let mut input = edge_input();
        let edge = &mut input.routes[0];
        edge.marker_start = start.into();
        edge.marker_end = end.into();
        edge.line = stroke.into();
        let s = layout::families::layout(&input)?.0;
        let items = &s.items()[0].items;
        assert_eq!(items.len(), 1 + names.len());
        let scene::Item::Polyline(polyline) = &items[0] else {
            return Err("missing edge polyline".into());
        };
        assert_eq!((polyline.shape.line, polyline.shape.width), (line, width));
        let points = &s.routes()[0].points;
        for (i, name) in names.iter().enumerate() {
            let scene::Item::MarkerRef(marker) = &items[i + 1] else {
                return Err("missing edge marker".into());
            };
            assert_eq!(marker.marker.as_str(), *name);
            let expected = if names.len() == 2 && i == 0 {
                (points[0], scene::MarkerAxis::MinusX)
            } else {
                (points[points.len() - 1], scene::MarkerAxis::PlusX)
            };
            assert_eq!((marker.at, marker.axis), expected);
        }
    }
    let mut invisible = edge_input();
    invisible.routes[0].line = "invisible".into();
    let s = layout::families::layout(&invisible)?.0;
    assert_eq!(s.routes().len(), 1);
    assert!(s.items()[0].items.is_empty());
    Ok(())
}

#[test]
fn pipeline_flowchart_extra_dash_rank() -> Result<(), Box<dyn std::error::Error>> {
    let input = edge_input();
    let mut edges = [layout::layered::pipeline::EdgeOptions {
        marker_start: None,
        marker_end: None,
        stroke: "normal",
        min_length: 1,
    }];
    let short = layout::layered::pipeline::layout_family(&input, &edges)?.0;
    edges[0].min_length = 2;
    let long = layout::layered::pipeline::layout_family(&input, &edges)?.0;
    assert_eq!(long.boxes()[1].rect.x - short.boxes()[1].rect.x, 3072);
    Ok(())
}

#[test]
fn pipeline_reversed_edge_markers() -> Result<(), Box<dyn std::error::Error>> {
    let mut input = edge_input();
    let mut reversed = input.routes[0].clone();
    reversed.id = "e1".into();
    reversed.from = "B".into();
    reversed.to = "A".into();
    reversed.marker_start = "circle".into();
    reversed.marker_end = "circle".into();
    reversed.min_length = 1;
    input.routes.push(reversed);
    let s = layout::families::layout(&input)?.0;
    let points = &s.routes()[1].points;
    let scene::Item::MarkerRef(start) = &s.items()[1].items[1] else {
        return Err("missing source marker".into());
    };
    let scene::Item::MarkerRef(end) = &s.items()[1].items[2] else {
        return Err("missing target marker".into());
    };
    assert_eq!(
        (start.at, start.axis),
        (points[0], scene::MarkerAxis::PlusX)
    );
    assert_eq!(
        (end.at, end.axis),
        (points[points.len() - 1], scene::MarkerAxis::MinusX)
    );
    Ok(())
}

#[test]
fn step14_ranks_follow_labels_not_stroke_count() -> Result<(), Box<dyn std::error::Error>> {
    let mut unlabelled_gap = None;
    for edge in ["A --> B", "A ---> B"] {
        let source = format!("flowchart LR\n{edge}\n");
        let parsed = syntax::flowchart::parse(&source, &[]);
        assert!(
            parsed.diagnostics.is_empty(),
            "{edge}: {:?}",
            parsed.diagnostics
        );
        let (model, diagnostics) = model::flowchart::resolve(&source, &parsed.document);
        assert!(diagnostics.is_empty());
        let input = layout::flowchart::from_flowchart(
            &model,
            scene::Profile::Vector,
            scene::DumpOptions::default(),
        );
        assert!(input.labels.is_empty(), "{edge}: {:?}", input.labels);
        let s = layout::families::layout(&input)?.0;
        let gap = s.boxes()[1].rect.x - s.boxes()[0].rect.x - s.boxes()[0].rect.w;
        assert!(gap > 0, "{edge}");
        if let Some(expected) = unlabelled_gap {
            assert_eq!(gap, expected, "{edge}");
        } else {
            unlabelled_gap = Some(gap);
        }
    }
    let source = "flowchart LR\nA -->|yes| B\n";
    let parsed = syntax::flowchart::parse(source, &[]);
    assert!(parsed.diagnostics.is_empty());
    let (model, diagnostics) = model::flowchart::resolve(source, &parsed.document);
    assert!(diagnostics.is_empty());
    let input = layout::flowchart::from_flowchart(
        &model,
        scene::Profile::Vector,
        scene::DumpOptions::default(),
    );
    let s = layout::families::layout(&input)?.0;
    let gap = s.boxes()[1].rect.x - s.boxes()[0].rect.x - s.boxes()[0].rect.w;
    assert!(Some(gap) > unlabelled_gap);
    let label = &s.labels()[0];
    assert!(s.boxes()[0].rect.x + s.boxes()[0].rect.w <= label.rect.x);
    assert!(label.rect.x + label.rect.w <= s.boxes()[1].rect.x);
    Ok(())
}

#[test]
fn model_route_styles() {
    for (edge, record) in [
        (
            "A --- B",
            r#"{"id":"e0","from":"A","to":"B","orthogonal":true,"marker_end":"none"}"#,
        ),
        (
            "A <--> B",
            r#"{"id":"e0","from":"A","to":"B","orthogonal":true,"marker_start":"point"}"#,
        ),
        (
            "A o--o B",
            r#"{"id":"e0","from":"A","to":"B","orthogonal":true,"marker_start":"circle","marker_end":"circle"}"#,
        ),
        (
            "A x--x B",
            r#"{"id":"e0","from":"A","to":"B","orthogonal":true,"marker_start":"cross","marker_end":"cross"}"#,
        ),
        (
            "A -.-> B",
            r#"{"id":"e0","from":"A","to":"B","orthogonal":true,"stroke":"dotted"}"#,
        ),
        (
            "A ==> B",
            r#"{"id":"e0","from":"A","to":"B","orthogonal":true,"stroke":"thick"}"#,
        ),
        (
            "A --> B",
            r#"{"id":"e0","from":"A","to":"B","orthogonal":true}"#,
        ),
    ] {
        let source = format!("flowchart\n{edge}\n");
        let parsed = syntax::flowchart::parse(&source, &[]);
        let (model, _) = model::flowchart::resolve(&source, &parsed.document);
        let input = layout::flowchart::from_flowchart(
            &model,
            scene::Profile::Vector,
            scene::DumpOptions::default(),
        );
        let dump = layout::modeldump::model_dump(&input);
        assert!(
            dump.contains(&format!("\"routes\":[{record}]")),
            "{edge}: {dump}"
        );
    }
}
