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
        region_sets: Vec::new(),
        spacing: crate::layout::input::Spacing::default(),
    };
    input.boxes.push(crate::layout::input::Box {
        id: "A".into(),
        role: BoxRole::Node,
        shape: String::new(),
        icon: false,
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
            icon: false,
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
        region_sets: Vec::new(),
        spacing: crate::layout::input::Spacing::default(),
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
        from_side: None,
        to_side: None,
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

fn spacing_input(profile: Profile, node_count: usize) -> Input {
    let mut input = sized_input(profile, Direction::Tb, SizeRule::Measured);
    input.boxes = (0..node_count)
        .map(|index| crate::layout::input::Box {
            id: format!("n{index}"),
            role: BoxRole::Node,
            shape: String::new(),
            icon: false,
            parent: String::new(),
            exclusive: true,
            text: String::new(),
            direction: String::new(),
        })
        .collect();
    input.sizes = vec![SizeRule::Exact(Size { w: 20, h: 12 }); input.boxes.len()];
    for index in 1..input.boxes.len() {
        input.routes.push(crate::layout::input::Route {
            id: format!("e{index}"),
            from: "n0".into(),
            to: format!("n{index}"),
            orthogonal: true,
            marker_start: String::new(),
            marker_end: String::new(),
            line: String::new(),
            min_length: 1,
            from_side: None,
            to_side: None,
        });
    }
    input
}

fn spacing_scene(input: &Input) -> Result<Scene, LayoutError> {
    let edges = vec![
        EdgeOptions {
            marker_start: None,
            marker_end: None,
            stroke: "",
            min_length: 1,
        };
        input.routes.len()
    ];
    let (scene, _) = layout_family(input, &edges)?;
    assert_eq!(
        scene.validate()?,
        None,
        "spacing overrides must preserve valid geometry:\n{}",
        scene.dump()
    );
    let canvas = scene.canvas();
    for b in scene.boxes() {
        assert!(
            b.rect.x >= 0
                && b.rect.y >= 0
                && i64::from(b.rect.x) + i64::from(b.rect.w) <= i64::from(canvas.w)
                && i64::from(b.rect.y) + i64::from(b.rect.h) <= i64::from(canvas.h),
            "box {} {:?} must remain inside canvas {canvas:?}",
            b.id,
            b.rect
        );
    }
    Ok(scene)
}

fn spacing_box(scene: &Scene, id: &str) -> Result<Rect, LayoutError> {
    scene
        .boxes()
        .iter()
        .find(|b| b.id == id)
        .map(|b| b.rect)
        .ok_or(LayoutError::Domain)
}

#[test]
fn explicit_spacing_moves_same_rank_siblings_and_rank_pair() -> Result<(), LayoutError> {
    for profile in [Profile::Vector, Profile::Cell] {
        let mut siblings = spacing_input(profile, 3);
        siblings.spacing = crate::layout::input::Spacing {
            node_gap: 38,
            rank_gap: 71,
            canvas_margin: 19,
        };
        let scene = spacing_scene(&siblings)?;
        let a = spacing_box(&scene, "n1")?;
        let b = spacing_box(&scene, "n2")?;
        assert_eq!(a.y, b.y, "fork targets must occupy the same rank");
        assert_eq!(
            (a.x - b.x).abs() - 20,
            38,
            "even-width sibling boxes must have the explicit cross-axis gap"
        );
        let mut pair = spacing_input(profile, 2);
        pair.spacing = siblings.spacing;
        let scene = spacing_scene(&pair)?;
        let source = spacing_box(&scene, "n0")?;
        let target = spacing_box(&scene, "n1")?;
        assert_eq!(
            target.y - source.y - source.h,
            71,
            "aligned rank pair has no horizontal routing slot, so its gap is rank_gap"
        );
        assert_eq!(
            (source.x, source.y, target.x),
            (19, 19, 19),
            "the natural origin must translate by the explicit canvas margin"
        );
        assert_eq!(
            scene.canvas(),
            Size { w: 58, h: 133 },
            "canvas must enclose 20x12 boxes, one 71-unit gap, and two 19-unit margins"
        );
        pair.spacing = crate::layout::input::Spacing::default();
        let default = spacing_scene(&pair)?;
        assert_ne!(
            spacing_box(&default, "n1")?.y - spacing_box(&default, "n0")?.y,
            target.y - source.y,
            "explicit spacing must change observable rank geometry from the default"
        );
    }
    Ok(())
}

#[test]
fn isolated_own_direction_preserves_explicit_child_spacing() -> Result<(), LayoutError> {
    for profile in [Profile::Vector, Profile::Cell] {
        let mut input = spacing_input(profile, 2);
        input.spacing = crate::layout::input::Spacing {
            node_gap: 38,
            rank_gap: 71,
            canvas_margin: 19,
        };
        for b in &mut input.boxes {
            b.parent = "group".into();
        }
        input.boxes.push(crate::layout::input::Box {
            id: "group".into(),
            role: BoxRole::Group,
            shape: String::new(),
            icon: false,
            parent: String::new(),
            exclusive: false,
            text: String::new(),
            direction: "LR".into(),
        });
        input.sizes.push(SizeRule::Measured);
        input.groups.push(crate::layout::input::Group {
            id: "group".into(),
            parent: String::new(),
            direction: "LR".into(),
            direction_span: crate::source::Span { start: 0, end: 0 },
        });
        let scene = spacing_scene(&input)?;
        let source = spacing_box(&scene, "n0")?;
        let target = spacing_box(&scene, "n1")?;
        assert_eq!(
            source.y, target.y,
            "isolated LR child must retain its own direction inside a TB parent"
        );
        assert_eq!(
            target.x - source.x - source.w,
            71,
            "child projection must preserve rank_gap after rotating the rank axis to x"
        );
        input.spacing.rank_gap = 103;
        let wider = spacing_scene(&input)?;
        assert_eq!(
            spacing_box(&wider, "n1")?.x - spacing_box(&wider, "n0")?.x,
            target.x - source.x + 32,
            "changing only child rank_gap must increase its centre distance by the same amount"
        );
    }
    Ok(())
}
#[test]
fn family_wrap_target_beats_max_width_at_scene_and_dump_level() -> Result<(), LayoutError> {
    let text = "alpha beta gamma delta epsilon zeta";
    let input = Input {
        kind: "usecase",
        profile: Profile::Cell,
        direction: Direction::Tb,
        options: DumpOptions {
            max_width: 5,
            ..DumpOptions::default()
        },
        boxes: vec![
            crate::layout::input::Box {
                id: "A".into(),
                role: BoxRole::Node,
                shape: String::new(),
                icon: false,
                parent: String::new(),
                exclusive: true,
                text: text.into(),
                direction: String::new(),
            },
            crate::layout::input::Box {
                id: "B".into(),
                role: BoxRole::Node,
                shape: String::new(),
                icon: false,
                parent: String::new(),
                exclusive: true,
                text: "B".into(),
                direction: String::new(),
            },
        ],
        routes: vec![crate::layout::input::Route {
            id: "e0".into(),
            from: "A".into(),
            to: "B".into(),
            orthogonal: true,
            marker_start: String::new(),
            marker_end: String::new(),
            line: String::new(),
            min_length: 2,
            from_side: None,
            to_side: None,
        }],
        labels: vec![
            crate::layout::input::Label {
                id: "A.label".into(),
                owner: "A".into(),
                role: crate::scene::TextRole::Label,
                text: text.into(),
            },
            crate::layout::input::Label {
                id: "e0.label".into(),
                owner: "e0".into(),
                role: crate::scene::TextRole::Label,
                text: text.into(),
            },
        ],
        groups: Vec::new(),
        sizes: Vec::new(),
        attachments: Vec::new(),
        region_sets: Vec::new(),
        spacing: crate::layout::input::Spacing::default(),
    };
    let edges = [EdgeOptions {
        marker_start: None,
        marker_end: None,
        stroke: "",
        min_length: 2,
    }];
    let (scene, _) = layout_unisolated(&input, &edges, &[])?;
    let expected = ["alpha beta", "gamma delta", "epsilon zeta"];
    let scene_lines = scene
        .items()
        .iter()
        .filter(|group| group.owner == "A")
        .flat_map(|group| group.items.iter())
        .find_map(|item| match item {
            crate::scene::Item::Text(text) => Some(
                text.lines
                    .iter()
                    .map(|line| line.iter().map(|run| run.text.as_str()).collect::<String>())
                    .collect::<Vec<_>>(),
            ),
            _ => None,
        })
        .ok_or(LayoutError::Domain)?;
    assert_eq!(
        scene_lines, expected,
        "scene lines must wrap at the family width, not the smaller max_width"
    );
    let dump_lines = scene
        .dump_part()
        .labels
        .iter()
        .find(|label| label.id == "e0.label" && label.owner == "e0")
        .ok_or(LayoutError::Domain)?
        .lines
        .clone();
    assert_eq!(
        dump_lines, expected,
        "route dump lines must wrap at the family width, not the smaller max_width"
    );
    Ok(())
}

#[test]
fn cell_pipeline_parses_before_replacing_controls() -> Result<(), LayoutError> {
    let mut input = sized_input(Profile::Cell, Direction::Tb, SizeRule::Measured);
    input.boxes.truncate(2);
    input.sizes.clear();
    input.boxes[0].id = "A".into();
    input.boxes[1].id = "B".into();
    input.boxes[0].text = "**a\nb**".into();
    input.boxes[1].text = "B".into();
    input.routes.push(crate::layout::input::Route {
        id: "e0".into(),
        from: "A".into(),
        to: "B".into(),
        orthogonal: true,
        marker_start: String::new(),
        marker_end: String::new(),
        line: String::new(),
        min_length: 2,
        from_side: None,
        to_side: None,
    });
    input.labels.push(crate::layout::input::Label {
        id: "e0.label".into(),
        owner: "e0".into(),
        role: crate::scene::TextRole::Label,
        text: "*c\r\nd*".into(),
    });
    let edges = [EdgeOptions {
        marker_start: None,
        marker_end: None,
        stroke: "",
        min_length: 2,
    }];
    let (scene, _) = layout_unisolated(&input, &edges, &[])?;
    let node_text = scene
        .items()
        .iter()
        .filter(|group| group.owner == "A")
        .flat_map(|group| group.items.iter())
        .find_map(|item| match item {
            crate::scene::Item::Text(text) => Some(text),
            _ => None,
        })
        .ok_or(LayoutError::Domain)?;
    let node_lines = node_text
        .lines
        .iter()
        .map(|line| line.iter().map(|run| run.text.as_str()).collect::<String>())
        .collect::<Vec<_>>();
    assert_eq!(node_lines, ["**a\u{fffd}b**"]);
    assert!(
        node_text
            .lines
            .iter()
            .flatten()
            .all(|run| !run.bold && !run.italic)
    );
    let route_label = scene
        .dump_part()
        .labels
        .iter()
        .find(|label| label.id == "e0.label" && label.owner == "e0")
        .ok_or(LayoutError::Domain)?;
    assert_eq!(route_label.text, "*c\r\nd*");
    assert_eq!(route_label.lines, ["*c\u{fffd}\u{fffd}d*"]);
    Ok(())
}
