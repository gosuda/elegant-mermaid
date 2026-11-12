use elegant_mermaid::{layout, model, scene, syntax};

#[test]
fn pipeline_demo_exact_go_bytes() -> Result<(), Box<dyn std::error::Error>> {
    let source = "flowchart LR\n  A[Start] --> B{Choice}\n  B -->|yes| C[Done]\n  B -->|no| A\n";
    let parsed = syntax::flowchart::parse(source, &[]);
    let (model, _) = model::flowchart::resolve(source, &parsed.document);
    let input = layout::flowchart::from_flowchart(
        &parsed.document,
        &model,
        scene::Profile::Vector,
        scene::DumpOptions::default(),
    );
    let actual = layout::families::layout(&input)?.0.dump();
    assert_eq!(
        actual,
        r#"{"version":1,"stage":"layout","kind":"flowchart","profile":"vector","options":{"profile":"vector","thoroughness":3,"max_width":0,"direction":"LR","limits":{"max_nodes":2000,"max_edges":5000,"max_text_bytes":1048576}},"canvas":{"w":25830,"h":2304},
"boxes":[{"id":"A","role":"node","x":0,"y":0,"w":3622,"h":2304,"parent":"","exclusive":true},
{"id":"B","role":"node","x":11302,"y":0,"w":4577,"h":2304,"parent":"","exclusive":true},
{"id":"C","role":"node","x":22023,"y":0,"w":3807,"h":2304,"parent":"","exclusive":true}],
"routes":[{"id":"e0","from":"A","to":"B","orthogonal":true,"points":[[3622,768],[4774,768],[4774,0],[7462,0],[8614,0],[8614,768],[11302,768]]},
{"id":"e1","from":"B","to":"C","orthogonal":true,"points":[[15879,1152],[18951,1152],[22023,1152]]},
{"id":"e2","from":"B","to":"A","orthogonal":true,"points":[[11302,1536],[8614,1536],[8614,2304],[7462,2304],[4774,2304],[4774,1536],[3622,1536]]}],
"labels":[]}
"#
    );
    let input = layout::flowchart::from_flowchart(
        &parsed.document,
        &model,
        scene::Profile::Cell,
        scene::DumpOptions::default(),
    );
    let actual = layout::families::layout(&input)?.0.dump();
    assert_eq!(
        actual,
        r#"{"version":1,"stage":"layout","kind":"flowchart","profile":"cell","options":{"profile":"cell","thoroughness":3,"max_width":0,"direction":"LR","limits":{"max_nodes":2000,"max_edges":5000,"max_text_bytes":1048576}},"canvas":{"w":41,"h":3},
"boxes":[{"id":"A","role":"node","x":0,"y":0,"w":9,"h":3,"parent":"","exclusive":true},
{"id":"B","role":"node","x":17,"y":0,"w":10,"h":3,"parent":"","exclusive":true},
{"id":"C","role":"node","x":33,"y":0,"w":8,"h":3,"parent":"","exclusive":true}],
"routes":[{"id":"e0","from":"A","to":"B","orthogonal":true,"points":[[9,1],[10,1],[10,0],[13,0],[14,0],[14,1],[17,1]]},
{"id":"e1","from":"B","to":"C","orthogonal":true,"points":[[27,1],[30,1],[33,1]]},
{"id":"e2","from":"B","to":"A","orthogonal":true,"points":[[17,2],[13,2],[9,2]]}],
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
        &parsed.document,
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
    let mut input = edge_input();
    input.routes[0].min_length = 1;
    let short = layout::families::layout(&input)?.0;
    input.routes[0].min_length = 2;
    let long = layout::families::layout(&input)?.0;
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
