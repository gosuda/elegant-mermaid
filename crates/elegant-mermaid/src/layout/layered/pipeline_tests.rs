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
        attachments: Vec::new(),
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
    input.sizes = vec![SizeRule::Content(Size { w: 10000, h: 1 })];
    input.direction = Direction::Lr;
    let (graph, _) = measured(&input, &[])?;
    assert_eq!(graph.nodes[0].w, constant(input.profile, "node_min_h"));
    assert_eq!(graph.nodes[0].h, 10000);
    input.sizes.clear();
    let (default_graph, _) = measured(&input, &[])?;
    input.sizes.push(SizeRule::Measured);
    let (sentinel_graph, _) = measured(&input, &[])?;
    assert_eq!(sentinel_graph.nodes, default_graph.nodes);
    input.sizes[0] = SizeRule::Content(Size { w: 0, h: 0 });
    let (zero_content_graph, _) = measured(&input, &[])?;
    assert_eq!(zero_content_graph.nodes, default_graph.nodes);
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

fn sized_input(profile: Profile, direction: Direction, rule: SizeRule) -> Input {
    let boxes = ["unrelated", "fixed", "a", "b", "c", "d"]
        .into_iter()
        .map(|id| crate::layout::input::Box {
            id: id.into(),
            role: BoxRole::Node,
            shape: String::new(),
            parent: String::new(),
            exclusive: true,
            text: String::new(),
            direction: String::new(),
        })
        .collect();
    Input {
        kind: "flowchart",
        profile,
        direction,
        options: DumpOptions {
            profile,
            thoroughness: 1,
            ..DumpOptions::default()
        },
        boxes,
        routes: Vec::new(),
        labels: Vec::new(),
        groups: Vec::new(),
        sizes: vec![SizeRule::Measured, rule],
        attachments: Vec::new(),
    }
}

fn add_sized_route(input: &mut Input, to: &str, labelled: bool) {
    let id = format!("e{}", input.routes.len());
    if labelled {
        input.labels.push(crate::layout::input::Label {
            id: format!("{id}.label"),
            owner: id.clone(),
            role: TextRole::Label,
            text: "loop label".into(),
        });
    }
    input.routes.push(crate::layout::input::Route {
        id,
        from: "fixed".into(),
        to: to.into(),
        orthogonal: true,
        marker_start: String::new(),
        marker_end: String::new(),
        line: String::new(),
        min_length: 1,
    });
}

#[test]
fn exact_footprint_survives_ports_loops_components_and_orientation() -> Result<(), LayoutError> {
    let cases = [Profile::Vector, Profile::Cell]
        .into_iter()
        .flat_map(|profile| {
            [Direction::Tb, Direction::Bt, Direction::Lr, Direction::Rl]
                .into_iter()
                .flat_map(move |direction| {
                    [0, 1, 3].into_iter().flat_map(move |count| {
                        [false, true].map(|labelled| (profile, direction, count, labelled))
                    })
                })
        });
    for (profile, direction, loop_count, labelled) in cases {
        let side = if profile == Profile::Vector { 896 } else { 1 };
        let size = Size { w: side, h: side };
        let mut input = sized_input(profile, direction, SizeRule::Exact(size));
        for to in ["a", "b", "c", "d"] {
            add_sized_route(&mut input, to, false);
        }
        for _ in 0..loop_count {
            add_sized_route(&mut input, "fixed", labelled);
        }
        let input = input;
        let edges = vec![
            EdgeOptions {
                marker_start: None,
                marker_end: None,
                stroke: "",
                min_length: 1,
            };
            input.routes.len()
        ];
        let (scene, _) = layout_family(&input, &edges)?;
        let Some(fixed) = scene.boxes().iter().find(|b| b.id == "fixed") else {
            return Err(LayoutError::Domain);
        };
        assert_eq!((fixed.rect.w, fixed.rect.h), (side, side));
        assert_eq!(
            scene.validate()?,
            None,
            "profile={profile:?} direction={direction:?} loops={loop_count} labelled={labelled}\n{}",
            scene.dump()
        );
        for route in scene.routes().iter().filter(|r| r.from == "fixed") {
            let Some(first) = route.points.first() else {
                return Err(LayoutError::Domain);
            };
            assert!(
                first.x >= fixed.rect.x && first.x <= fixed.rect.x + side,
                "route {} starts outside the fixed box x interval: {first:?}",
                route.id
            );
            assert!(
                first.y >= fixed.rect.y && first.y <= fixed.rect.y + side,
                "route {} starts outside the fixed box y interval: {first:?}",
                route.id
            );
            assert!(
                first.x == fixed.rect.x
                    || first.x == fixed.rect.x + side
                    || first.y == fixed.rect.y
                    || first.y == fixed.rect.y + side,
                "route {} starts off the fixed box boundary: {first:?}",
                route.id
            );
        }
        let mut content_input = input;
        content_input.sizes[1] = SizeRule::Content(size);
        let (content, _) = layout_family(&content_input, &edges)?;
        let Some(content) = content.boxes().iter().find(|b| b.id == "fixed") else {
            return Err(LayoutError::Domain);
        };
        assert!(
            content.rect.w > side || content.rect.h > side,
            "Content must retain ordinary minimum/port widening: {:?}",
            content.rect
        );
    }
    Ok(())
}

#[test]
fn explicit_negative_sizes_keep_domain_error() {
    for size in [Size { w: -1, h: 1 }, Size { w: 1, h: -1 }] {
        for rule in [SizeRule::Exact(size), SizeRule::Content(size)] {
            let input = sized_input(Profile::Vector, Direction::Tb, rule);
            assert!(
                matches!(measured(&input, &[]), Err(LayoutError::Domain)),
                "negative size rule must return Domain: {rule:?}"
            );
        }
    }
}
