use elegant_mermaid::{geom::Point, layout, model, scene, syntax};
use scene::{BoxRole, DumpOptions, GroupRole, MarkerAxis, Profile};

type TestResult = Result<(), Box<dyn std::error::Error>>;

const BASE: &str =
    "swimlane-beta DIR\n  subgraph A\n    a1[x]\n  end\n  subgraph B\n    b1[y]\n  end\n";

fn source(direction: &str, edges: &str) -> String {
    BASE.replace("DIR", direction) + edges
}

fn swimlane_scene(
    source: &str,
    profile: Profile,
) -> Result<scene::Scene, Box<dyn std::error::Error>> {
    let preprocessed = syntax::preprocess::preprocess(source);
    assert!(
        preprocessed.diagnostics.is_empty(),
        "preprocess diagnostics for {source:?}: {:?}",
        preprocessed.diagnostics
    );
    let parsed = syntax::swimlane::parse(source, &preprocessed.removed);
    assert!(
        parsed.diagnostics.is_empty(),
        "parse diagnostics for {source:?}: {:?}",
        parsed.diagnostics
    );
    let (resolved, diagnostics) = model::swimlane::resolve(source, &parsed.document);
    assert!(
        diagnostics.is_empty(),
        "resolve diagnostics for {source:?}: {diagnostics:?}"
    );
    let input = layout::swimlane::from_swimlane(&resolved, profile, DumpOptions::default());
    let (scene, _) = layout::families::layout(&input)?;
    assert_eq!(
        scene.validate()?,
        None,
        "scene violates a hard clause for {source:?} {profile:?}: {}",
        scene.dump()
    );
    Ok(scene)
}

#[test]
fn loose_route_stays_clear_of_named_lane_node() -> TestResult {
    let label = "Y".repeat(256);
    let src = format!("swimlane-beta LR\n  subgraph A\n    a1\n  end\n  o1 -->|{label}| o2\n");
    let scene = swimlane_scene(&src, Profile::Vector)?;
    assert!(
        scene
            .routes()
            .iter()
            .any(|r| r.from == "o1" && r.to == "o2"),
        "missing loose route o1 -> o2"
    );
    assert!(
        scene
            .boxes()
            .iter()
            .any(|b| b.id == "a1" && b.parent == "A" && b.exclusive),
        "missing exclusive node a1 in lane A"
    );
    Ok(())
}

fn lane_sources() -> Vec<(String, String)> {
    vec![
        (source("LR", "  A --> A\n"), "LR".to_owned()),
        (source("TB", "  A --> A\n"), "TB".to_owned()),
        (source("RL", "  A --> A\n"), "RL".to_owned()),
        (source("BT", "  A --> A\n"), "BT".to_owned()),
        (source("LR", "  A -->|x| A\n"), "LR".to_owned()),
        (
            source("LR", "  A -->|a much longer loop label text| A\n"),
            "LR".to_owned(),
        ),
        (source("LR", "  A --> A\n  A --> A\n"), "LR".to_owned()),
        (source("TB", "  A --> A\n  A --> A\n"), "TB".to_owned()),
        (source("TB", "  B --> B\n"), "TB".to_owned()),
        (
            "swimlane-beta LR\n  subgraph A\n    a1[x]\n    a2[z]\n  end\n  subgraph B\n    b1[y]\n  end\n  A --> A\n"
                .to_owned(),
            "LR".to_owned(),
        ),
        (
            "swimlane-beta LR\n  subgraph A\n  end\n  subgraph B\n    b1[y]\n  end\n  A --> A\n"
                .to_owned(),
            "LR".to_owned(),
        ),
        (
            "swimlane-beta LR\n  subgraph A\n    a1[x]\n  end\n  c1[loose]\n  A --> A\n".to_owned(),
            "LR".to_owned(),
        ),
    ]
}

fn frame_end(rect: elegant_mermaid::geom::Rect, direction: &str) -> i64 {
    match direction {
        "TB" | "BT" => i64::from(rect.x) + i64::from(rect.w),
        _ => i64::from(rect.y) + i64::from(rect.h),
    }
}

fn cross(point: Point, direction: &str) -> i64 {
    match direction {
        "TB" | "BT" => i64::from(point.x),
        _ => i64::from(point.y),
    }
}

#[test]
fn lane_self_loops_end_on_lane_frame() -> TestResult {
    for profile in [Profile::Vector, Profile::Cell] {
        for (src, direction) in lane_sources() {
            let scene = swimlane_scene(&src, profile)?;
            let lanes: Vec<&str> = scene
                .boxes()
                .iter()
                .filter(|boxed| boxed.role == BoxRole::Group && boxed.parent.is_empty())
                .map(|boxed| boxed.id.as_str())
                .collect();
            let mut loops = 0;
            for route in scene.routes() {
                if route.from != route.to || !lanes.contains(&route.from.as_str()) {
                    continue;
                }
                loops += 1;
                let Some(frame) = scene.boxes().iter().find(|boxed| boxed.id == route.from) else {
                    continue;
                };
                let end = frame_end(frame.rect, &direction);
                let Some(first) = route.points.first() else {
                    continue;
                };
                let Some(last) = route.points.last() else {
                    continue;
                };
                assert_eq!(
                    cross(*first, &direction),
                    end,
                    "head of {} for {src:?} {profile:?}",
                    route.id
                );
                assert_eq!(
                    cross(*last, &direction),
                    end,
                    "tail of {} for {src:?} {profile:?}",
                    route.id
                );
            }
            assert!(loops > 0, "no lane self-loop route for {src:?} {profile:?}");
        }
    }
    Ok(())
}

fn pts(list: &[(i32, i32)]) -> Vec<Point> {
    list.iter().map(|&(x, y)| Point { x, y }).collect()
}

fn route_points(scene: &scene::Scene, id: &str) -> Vec<Point> {
    scene
        .routes()
        .iter()
        .find(|route| route.id == id)
        .map_or_else(Vec::new, |route| route.points.clone())
}

fn end_marker_axis(scene: &scene::Scene, owner: &str, at: Point) -> Option<MarkerAxis> {
    scene
        .items()
        .iter()
        .find(|group| group.role == GroupRole::Edge && group.owner == owner)
        .and_then(|group| {
            group.items.iter().find_map(|item| match item {
                scene::Item::MarkerRef(marker) if marker.at == at => Some(marker.axis),
                _ => None,
            })
        })
}

type ExpectedRoute = (String, Vec<Point>);
type LoopFixture = (String, Vec<ExpectedRoute>);

fn loop_table(vector: bool) -> Vec<LoopFixture> {
    vec![
        (
            source("LR", "  A --> A\n"),
            vec![(
                "e0".to_owned(),
                if vector {
                    pts(&[(1024, 13568), (1024, 11776), (2560, 11776), (2560, 13568)])
                } else {
                    pts(&[(1, 14), (1, 12), (3, 12), (3, 14)])
                },
            )],
        ),
        (
            source("TB", "  A --> A\n"),
            vec![(
                "e0".to_owned(),
                if vector {
                    pts(&[(13312, 1024), (11520, 1024), (11520, 2560), (13312, 2560)])
                } else {
                    pts(&[(16, 1), (14, 1), (14, 3), (16, 3)])
                },
            )],
        ),
        (
            source("RL", "  A --> A\n"),
            vec![(
                "e0".to_owned(),
                if vector {
                    pts(&[
                        (12288, 13568),
                        (12288, 11776),
                        (10752, 11776),
                        (10752, 13568),
                    ])
                } else {
                    pts(&[(16, 14), (16, 12), (14, 12), (14, 14)])
                },
            )],
        ),
        (
            source("BT", "  A --> A\n"),
            vec![(
                "e0".to_owned(),
                if vector {
                    pts(&[
                        (13312, 12544),
                        (11520, 12544),
                        (11520, 11008),
                        (13312, 11008),
                    ])
                } else {
                    pts(&[(16, 14), (14, 14), (14, 12), (16, 12)])
                },
            )],
        ),
        (
            source("LR", "  A -->|x| A\n"),
            vec![(
                "e0".to_owned(),
                if vector {
                    pts(&[(1024, 14848), (1024, 13056), (2560, 13056), (2560, 14848)])
                } else {
                    pts(&[(1, 15), (1, 13), (3, 13), (3, 15)])
                },
            )],
        ),
        (
            source("LR", "  A -->|a much longer loop label text| A\n"),
            vec![(
                "e0".to_owned(),
                if vector {
                    pts(&[(6492, 14848), (6492, 13056), (8028, 13056), (8028, 14848)])
                } else {
                    pts(&[(14, 15), (14, 13), (16, 13), (16, 15)])
                },
            )],
        ),
        (
            source("LR", "  A --> A\n  A --> A\n"),
            if vector {
                vec![
                    (
                        "e0".to_owned(),
                        pts(&[(1024, 16640), (1024, 14080), (2560, 14080), (2560, 16640)]),
                    ),
                    (
                        "e1".to_owned(),
                        pts(&[(2560, 16640), (2560, 14848), (4096, 14848), (4096, 16640)]),
                    ),
                ]
            } else {
                vec![
                    ("e0".to_owned(), pts(&[(1, 18), (1, 15), (3, 15), (3, 18)])),
                    ("e1".to_owned(), pts(&[(3, 18), (3, 16), (5, 16), (5, 18)])),
                ]
            },
        ),
        (
            source("TB", "  B --> B\n"),
            vec![(
                "e0".to_owned(),
                if vector {
                    pts(&[(23312, 1024), (21520, 1024), (21520, 2560), (23312, 2560)])
                } else {
                    pts(&[(28, 1), (26, 1), (26, 3), (28, 3)])
                },
            )],
        ),
        (
            "swimlane-beta LR\n  subgraph A\n  end\n  subgraph B\n    b1[y]\n  end\n  A --> A\n"
                .to_owned(),
            vec![(
                "e0".to_owned(),
                if vector {
                    pts(&[(1024, 12544), (1024, 10752), (2560, 10752), (2560, 12544)])
                } else {
                    pts(&[(1, 12), (1, 10), (3, 10), (3, 12)])
                },
            )],
        ),
        (
            "swimlane-beta LR\n  subgraph A\n    a1[x]\n  end\n  c1[loose]\n  A --> A\n".to_owned(),
            vec![(
                "e0".to_owned(),
                if vector {
                    pts(&[(1024, 13568), (1024, 11776), (2560, 11776), (2560, 13568)])
                } else {
                    pts(&[(1, 14), (1, 12), (3, 12), (3, 14)])
                },
            )],
        ),
    ]
}

fn assert_loop_table(profile: Profile) -> TestResult {
    let vector = profile == Profile::Vector;
    for (src, routes) in loop_table(vector) {
        let scene = swimlane_scene(&src, profile)?;
        for (id, expected) in &routes {
            assert_eq!(
                route_points(&scene, id),
                *expected,
                "route {id} for {src:?} {profile:?}"
            );
        }
    }
    Ok(())
}

fn assert_double_tb_vector() -> TestResult {
    let scene = swimlane_scene(&source("TB", "  A --> A\n  A --> A\n"), Profile::Vector)?;
    assert_eq!(
        route_points(&scene, "e0"),
        pts(&[(16384, 1024), (13824, 1024), (13824, 2560), (16384, 2560)]),
        "double TB e0"
    );
    assert_eq!(
        route_points(&scene, "e1"),
        pts(&[(16384, 2560), (14592, 2560), (14592, 4096), (16384, 4096)]),
        "double TB e1"
    );
    Ok(())
}

fn assert_end_markers() -> TestResult {
    for (direction, at, axis) in [
        ("LR", Point { x: 2560, y: 13568 }, MarkerAxis::PlusY),
        ("TB", Point { x: 13312, y: 2560 }, MarkerAxis::PlusX),
        ("RL", Point { x: 10752, y: 13568 }, MarkerAxis::PlusY),
        ("BT", Point { x: 13312, y: 11008 }, MarkerAxis::PlusX),
    ] {
        let scene = swimlane_scene(&source(direction, "  A --> A\n"), Profile::Vector)?;
        assert_eq!(
            end_marker_axis(&scene, "e0", at),
            Some(axis),
            "end marker for {direction}"
        );
    }
    Ok(())
}

#[test]
fn lane_self_loop_geometry() -> TestResult {
    for profile in [Profile::Vector, Profile::Cell] {
        assert_loop_table(profile)?;
    }
    assert_double_tb_vector()?;
    assert_end_markers()?;
    Ok(())
}
#[test]
fn lane_end_attachment_keeps_other_routes() -> TestResult {
    let nested_tb = "swimlane-beta TB\n  subgraph A\n    subgraph G\n      g1[x]\n    end\n  end\n  subgraph B\n    b1[y]\n  end\n";
    let nested_lr = "swimlane-beta LR\n  subgraph A\n    subgraph G\n      g1[x]\n    end\n  end\n  subgraph B\n    b1[y]\n  end\n";
    let cases: Vec<(String, Vec<Point>, Vec<Point>)> = vec![
        (
            source("LR", "  A --> a1\n"),
            pts(&[
                (1024, 6848),
                (1024, 4096),
                (3852, 4096),
                (3852, 6784),
                (6540, 6784),
            ]),
            pts(&[(1, 6), (1, 4), (4, 4), (4, 6), (7, 6)]),
        ),
        (
            source("TB", "  a1 --> A\n"),
            pts(&[(6656, 8704), (6656, 11776)]),
            pts(&[(7, 9), (7, 12)]),
        ),
        (
            nested_lr.to_owned() + "  G --> G\n",
            pts(&[(5772, 12544), (5772, 13312), (7308, 13312), (7308, 12544)]),
            pts(&[(6, 12), (6, 13), (8, 13), (8, 12)]),
        ),
        (
            nested_tb.to_owned() + "  G --> A\n",
            pts(&[(8192, 17152), (8192, 20224)]),
            pts(&[(8, 17), (8, 20)]),
        ),
        (
            source("LR", "  A --> b1\n"),
            pts(&[(12507, 6784), (15579, 6784), (15579, 17024), (16347, 17024)]),
            pts(&[(16, 6), (19, 6), (19, 16), (20, 16)]),
        ),
        (
            source("LR", "  A --> B\n"),
            pts(&[(10892, 6784), (13196, 6784), (13196, 17024), (13964, 17024)]),
            pts(&[(14, 6), (16, 6), (16, 16), (17, 16)]),
        ),
    ];
    for profile in [Profile::Vector, Profile::Cell] {
        for (src, vector, cell) in &cases {
            let scene = swimlane_scene(src, profile)?;
            let expected = if profile == Profile::Vector {
                vector
            } else {
                cell
            };
            assert_eq!(
                route_points(&scene, "e0"),
                *expected,
                "control route for {src:?} {profile:?}"
            );
        }
    }
    Ok(())
}
