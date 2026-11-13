use super::*;
#[test]
fn content_size_override_precedes_minimum_and_orientation() -> Result<(), LayoutError> {
    let mut input = Input {
        kind: "flowchart",
        profile: Profile::Vector,
        direction: Direction::Tb,
        options: DumpOptions::default(),
        boxes: Vec::new(),
        routes: Vec::new(),
        labels: Vec::new(),
        groups: Vec::new(),
        sizes: Vec::new(),
    };
    input.boxes.push(crate::layout::input::Box {
        id: "A".into(),
        role: BoxRole::Node,
        shape: String::new(),
        parent: String::new(),
        exclusive: true,
        text: "A".into(),
        direction: String::new(),
    });
    input.sizes = vec![Size { w: 10000, h: 1 }];
    input.direction = Direction::Lr;
    let (graph, _) = measured(&input, &[])?;
    assert_eq!(graph.nodes[0].w, constant(input.profile, "node_min_h"));
    assert_eq!(graph.nodes[0].h, 10000);
    input.sizes.clear();
    let (default_graph, _) = measured(&input, &[])?;
    input.sizes.push(Size { w: 0, h: 0 });
    let (sentinel_graph, _) = measured(&input, &[])?;
    assert_eq!(sentinel_graph.nodes, default_graph.nodes);
    Ok(())
}
#[test]
fn pipeline_bounds_include_route_points() {
    let boxes = [Rect {
        x: 0,
        y: 0,
        w: 3,
        h: 3,
    }];
    let routes = [route::EdgeRoute {
        original: 0,
        points: vec![Point { x: 8, y: 5 }],
    }];
    assert_eq!(bounds(&boxes, &routes), Ok((0, 0, 8, 5)));
}
