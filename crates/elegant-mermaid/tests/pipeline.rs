use elegant_mermaid::{layout, model, scene, syntax};

#[test]
fn pipeline_demo_exact_go_bytes() -> Result<(), Box<dyn std::error::Error>> {
    let source = "flowchart LR\n  A[Start] --> B{Choice}\n  B -->|yes| C[Done]\n  B -->|no| A\n";
    let parsed = syntax::flowchart::parse(source, &[]);
    let (model, _) = model::flowchart::resolve(source, &parsed.document);
    let input = layout::flowchart::from_flowchart(
        &model,
        scene::Profile::Vector,
        scene::DumpOptions::default(),
    );
    let actual = layout::families::layout(&input)?.0.dump();
    assert_eq!(
        actual,
        r#"{"version":1,"stage":"layout","kind":"flowchart","profile":"vector","options":{"profile":"vector","thoroughness":3,"max_width":0,"direction":"LR","limits":{"max_nodes":2000,"max_edges":5000,"max_text_bytes":1048576}},"canvas":{"w":18150,"h":2304},
"boxes":[{"id":"A","role":"node","x":0,"y":0,"w":3622,"h":2304,"parent":"","exclusive":true},
{"id":"B","role":"node","x":6694,"y":0,"w":4577,"h":2304,"parent":"","exclusive":true},
{"id":"C","role":"node","x":14343,"y":0,"w":3807,"h":2304,"parent":"","exclusive":true}],
"routes":[{"id":"e0","from":"A","to":"B","orthogonal":true,"points":[[3622,1152],[6694,1152]]},
{"id":"e1","from":"B","to":"C","orthogonal":true,"points":[[11271,1152],[14343,1152]]},
{"id":"e2","from":"B","to":"A","orthogonal":true,"points":[[6694,1152],[3622,1152]]}],
"labels":[]}
"#
    );
    let input = layout::flowchart::from_flowchart(
        &model,
        scene::Profile::Cell,
        scene::DumpOptions::default(),
    );
    let actual = layout::families::layout(&input)?.0.dump();
    assert_eq!(
        actual,
        r#"{"version":1,"stage":"layout","kind":"flowchart","profile":"cell","options":{"profile":"cell","thoroughness":3,"max_width":0,"direction":"LR","limits":{"max_nodes":2000,"max_edges":5000,"max_text_bytes":1048576}},"canvas":{"w":33,"h":3},
"boxes":[{"id":"A","role":"node","x":0,"y":0,"w":9,"h":3,"parent":"","exclusive":true},
{"id":"B","role":"node","x":12,"y":0,"w":10,"h":3,"parent":"","exclusive":true},
{"id":"C","role":"node","x":25,"y":0,"w":8,"h":3,"parent":"","exclusive":true}],
"routes":[{"id":"e0","from":"A","to":"B","orthogonal":true,"points":[[9,1],[12,1]]},
{"id":"e1","from":"B","to":"C","orthogonal":true,"points":[[22,1],[25,1]]},
{"id":"e2","from":"B","to":"A","orthogonal":true,"points":[[12,1],[9,1]]}],
"labels":[]}
"#
    );
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
fn walking_skeleton_ranks_ignore_syntax_and_labels() -> Result<(), Box<dyn std::error::Error>> {
    for edge in [
        "A --- B",
        "A <--> B",
        "A o--x B",
        "A -.-> B",
        "A ==> B",
        "A ---> B",
        "A -->|yes| B",
    ] {
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
        let s = layout::families::layout(&input)?.0;
        assert_eq!(
            s.boxes()[1].rect.x - s.boxes()[0].rect.x - s.boxes()[0].rect.w,
            3072,
            "{edge}"
        );
    }
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
