use elegant_mermaid::{
    RenderError, layout, model,
    scene::{self, Direction, DumpOptions, Profile},
    syntax,
};

type TestResult = Result<(), Box<dyn std::error::Error>>;

fn input(source: &str, profile: Profile) -> layout::input::Input {
    let preprocessed = syntax::preprocess::preprocess(source);
    assert!(preprocessed.diagnostics.is_empty());
    let parsed = syntax::flowchart::parse(source, &preprocessed.removed);
    let (model, _) = model::flowchart::resolve(source, &parsed.document);
    layout::flowchart::from_flowchart(&model, profile, DumpOptions::default())
}

#[test]
fn step14_route_labels_are_measured_ranked_and_drawn() -> TestResult {
    for profile in [Profile::Vector, Profile::Cell] {
        let model = input("flowchart TB\nA -->|a substantial edge label| B\n", profile);
        let scene = layout::families::layout(&model)?.0;
        assert!(scene.check()?);
        if profile == Profile::Cell {
            assert_eq!(
                elegant_mermaid::cells::render(
                    &scene,
                    &elegant_mermaid::cells::Options::default()
                )?
                .refused_clusters,
                0
            );
        }
        assert_eq!(scene.labels().len(), 1);
        let label = &scene.labels()[0];
        assert_eq!(label.owner, "e0");
        assert_eq!(label.text, "a substantial edge label");
        assert!(!label.lines.is_empty());
        assert!(scene.boxes()[0].rect.y + scene.boxes()[0].rect.h <= label.rect.y);
        assert!(label.rect.y + label.rect.h <= scene.boxes()[1].rect.y);
        let group = scene
            .items()
            .iter()
            .find(|g| g.owner == "e0")
            .ok_or("edge group missing")?;
        assert!(
            group
                .items
                .iter()
                .any(|item| matches!(item, scene::Item::Text(text) if text.rect == label.rect))
        );
    }
    Ok(())
}

const LOOPS_AND_REVERSED_SOURCE: &str =
    "flowchart TB\nA[alpha] -->|forward| B[beta]\nB -->|back| A\nA -->|one| A\nA -->|two| A\n";

#[test]
fn step14_loop_and_reversed_cell_labels_fit() -> TestResult {
    let mut model = input(LOOPS_AND_REVERSED_SOURCE, Profile::Cell);
    for direction in [Direction::Tb, Direction::Bt, Direction::Lr, Direction::Rl] {
        model.direction = direction;
        let scene = layout::families::layout(&model)?.0;
        assert_eq!(
            elegant_mermaid::cells::render(&scene, &elegant_mermaid::cells::Options::default())?
                .refused_clusters,
            0
        );
    }
    Ok(())
}

#[test]
fn step14_loops_and_reversed_lanes_satisfy_geometry() -> TestResult {
    let source = LOOPS_AND_REVERSED_SOURCE;
    for profile in [Profile::Vector, Profile::Cell] {
        let mut model = input(source, profile);
        for direction in [Direction::Tb, Direction::Bt, Direction::Lr, Direction::Rl] {
            model.direction = direction;
            let scene = layout::families::layout(&model)?.0;
            assert!(scene.check()?, "{profile:?} {direction:?}");
            assert_eq!(scene.labels().len(), 4);
            assert_eq!(scene.routes()[1].points.len(), 6);
            assert_eq!(scene.routes()[2].points.len(), 4);
            assert_eq!(scene.routes()[3].points.len(), 4);
            assert_eq!(scene.labels()[2].text, "one");
            assert_eq!(scene.labels()[3].text, "two");
            let first = scene.labels()[2].rect;
            let second = scene.labels()[3].rect;
            if matches!(direction, Direction::Tb | Direction::Bt) {
                assert_eq!(first.x, second.x);
            } else {
                assert_eq!(first.y, second.y);
            }
            assert_ne!(scene.routes()[2].points, scene.routes()[3].points);
        }
    }
    Ok(())
}

#[test]
fn step14_compound_empty_nested_and_crossing_groups() -> TestResult {
    for source in [
        "flowchart TB\nsubgraph empty[Empty]\nend\n",
        "flowchart TB\nsubgraph outer[Outer]\nsubgraph inner[Inner]\nA --> B\nend\nC\nend\n",
        "flowchart TB\nsubgraph left[Left]\nA --> B\nend\nsubgraph right[Right]\nC --> D\nend\nB --> C\n",
    ] {
        for profile in [Profile::Vector, Profile::Cell] {
            let model = input(source, profile);
            let scene = layout::families::layout(&model)?.0;
            assert!(scene.check()?, "{source} {profile:?}");
            if profile == Profile::Cell {
                assert_eq!(
                    elegant_mermaid::cells::render(
                        &scene,
                        &elegant_mermaid::cells::Options::default()
                    )?
                    .refused_clusters,
                    0
                );
            }
            for group in &model.groups {
                let frame = scene
                    .boxes()
                    .iter()
                    .find(|b| b.id == group.id)
                    .ok_or("group missing")?;
                assert!(frame.rect.w > 0 && frame.rect.h > 0);
                let title = scene
                    .labels()
                    .iter()
                    .find(|l| l.owner == group.id)
                    .ok_or("title missing")?;
                assert_eq!(title.id, format!("{}.label", group.id));
            }
        }
    }
    Ok(())
}

#[test]
fn step14_group_boundary_routes_keep_identity_and_titles() -> TestResult {
    for source in [
        "flowchart TB\nsubgraph S[Group title]\nA\nend\nS --> A\n",
        "flowchart TB\nsubgraph S[Group title]\nA\nend\nS --> X\nX --> S\nS --> S\n",
    ] {
        for profile in [Profile::Vector, Profile::Cell] {
            let model = input(source, profile);
            let scene = layout::families::layout(&model)?.0;
            assert!(scene.check()?, "{source} {profile:?}");
            if profile == Profile::Cell {
                assert_eq!(
                    elegant_mermaid::cells::render(
                        &scene,
                        &elegant_mermaid::cells::Options::default()
                    )?
                    .refused_clusters,
                    0
                );
            }
            assert_eq!(scene.boxes().len(), model.boxes.len());
            assert_eq!(scene.routes().len(), model.routes.len());
            for route in scene.routes() {
                assert!(!route.points.is_empty());
            }
            assert_eq!(scene.boxes().iter().filter(|b| b.id == "S").count(), 1);
            assert!(
                scene
                    .labels()
                    .iter()
                    .any(|l| l.owner == "S" && l.text == "Group title")
            );
        }
    }
    Ok(())
}

#[test]
fn step14_independent_direction_and_exact_ignored_span() -> TestResult {
    let independent =
        "flowchart TB\nsubgraph S[Group]\ndirection LR\nA --> B\nend\nS --> X\nS --> S\n";
    let model = input(independent, Profile::Cell);
    let (scene, diagnostics) = layout::families::layout(&model)?;
    assert!(
        !diagnostics
            .iter()
            .any(|d| d.code == "flowchart/subgraph-direction-ignored")
    );
    assert!(scene.check()?);
    let a = scene
        .boxes()
        .iter()
        .find(|b| b.id == "A")
        .ok_or("A missing")?
        .rect;
    let b = scene
        .boxes()
        .iter()
        .find(|b| b.id == "B")
        .ok_or("B missing")?
        .rect;
    assert!(a.x < b.x);
    assert_eq!(a.y, b.y);
    assert_eq!(scene.routes().len(), model.routes.len());
    let crossing = independent.replace("S --> X", "A --> X");
    let model = input(&crossing, Profile::Cell);
    let (_, diagnostics) = layout::families::layout(&model)?;
    let ignored = diagnostics
        .iter()
        .find(|d| d.code == "flowchart/subgraph-direction-ignored")
        .ok_or("ignored direction diagnostic missing")?;
    assert_eq!(
        &crossing[ignored.span.start..ignored.span.end],
        "direction LR"
    );
    Ok(())
}

#[test]
fn step14_model_transport_includes_only_group_direction_and_owned_title() {
    let model = input(
        "flowchart TB\nsubgraph S[Title]\ndirection TD\nA\nend\n",
        Profile::Vector,
    );
    let dump = layout::modeldump::model_dump(&model);
    assert!(dump.contains("\"exclusive\":false,\"direction\":\"TB\""));
    assert!(dump.contains("\"id\":\"S.label\",\"owner\":\"S\",\"text\":\"Title\",\"lines\":[]"));
    assert_eq!(dump.matches("\"direction\"").count(), 2);
}

#[test]
fn step14_limits_count_resolved_owned_utf8_before_measurement() -> TestResult {
    let source = "flowchart TB\n%% comment bytes do not count\nA[é] -->|x| B\n";
    let mut model = input(source, Profile::Vector);
    model.options.limits.max_text_bytes = 3;
    let result = layout::families::layout(&model);
    assert!(
        matches!(
            &result,
            Err(RenderError::TooLarge {
                limit: 3,
                actual: 4
            })
        ),
        "resolved boxes={:?}, labels={:?}, error={:?}",
        model.boxes,
        model.labels,
        result.err()
    );
    model.options.limits.max_text_bytes = 4;
    layout::families::layout(&model)?;
    model.options.limits.max_nodes = 1;
    assert!(matches!(
        layout::families::layout(&model),
        Err(RenderError::TooLarge {
            limit: 1,
            actual: 2
        })
    ));
    let mut grouped = input("flowchart TB\nsubgraph S[é]\nA\nend\n", Profile::Vector);
    grouped.options.limits.max_text_bytes = 2;
    assert!(matches!(
        layout::families::layout(&grouped),
        Err(RenderError::TooLarge {
            limit: 2,
            actual: 3
        })
    ));
    let mut edges = input("flowchart TB\nA --> A\nA --> B\n", Profile::Cell);
    edges.options.limits.max_edges = 1;
    let mut empty_groups = input(
        "flowchart TB\nsubgraph one\nend\nsubgraph two\nend\n",
        Profile::Cell,
    );
    empty_groups.options.limits.max_nodes = 1;
    assert!(matches!(
        layout::families::layout(&empty_groups),
        Err(RenderError::TooLarge {
            limit: 1,
            actual: 2
        })
    ));
    assert!(matches!(
        layout::families::layout(&edges),
        Err(RenderError::TooLarge {
            limit: 1,
            actual: 2
        })
    ));
    Ok(())
}

#[test]
fn step14_cell_controls_normalize_before_measurement_only() -> TestResult {
    let mut raw = input("flowchart TB\nA[x] -->|y| B\n", Profile::Cell);
    raw.boxes[0].text = "\u{1}\u{7f}\u{85}".into();
    let node_id = raw.boxes[0].id.clone();
    for label in &mut raw.labels {
        if label.owner == node_id {
            label.text = raw.boxes[0].text.clone();
        }
    }
    let mut normalized = raw.clone();
    normalized.boxes[0].text = "���".into();
    for label in &mut normalized.labels {
        if label.owner == node_id {
            label.text = "���".into();
        }
    }
    let a = layout::families::layout(&raw)?.0;
    let b = layout::families::layout(&normalized)?.0;
    assert_eq!(a.boxes(), b.boxes());
    assert_eq!(a.items(), b.items());
    assert!(layout::modeldump::model_dump(&raw).contains("\\u0001"));
    Ok(())
}

#[test]
fn step14_shelf_width_is_cell_only_and_never_crops() -> TestResult {
    let source = "flowchart TB\nA[alpha]\nB[beta]\nC[gamma]\n";
    let mut model = input(source, Profile::Cell);
    model.options.max_width = 1;
    let narrow = layout::families::layout(&model)?.0;
    assert!(narrow.check()?);
    assert!(narrow.canvas().w > 1);
    assert!(
        narrow
            .boxes()
            .windows(2)
            .all(|pair| pair[0].rect.y < pair[1].rect.y)
    );
    let mut model = input(source, Profile::Vector);
    let natural = layout::families::layout(&model)?.0;
    model.options.max_width = 1;
    let ignored = layout::families::layout(&model)?.0;
    assert_eq!(natural.boxes(), ignored.boxes());
    assert_eq!(natural.canvas(), ignored.canvas());
    Ok(())
}

#[test]
fn step14_all_five_portfolio_candidates_are_deterministic() -> TestResult {
    let source = "flowchart TB\nA --> C\nB --> D\nA --> D\nD --> A\nC --> E\nD --> E\n";
    for thoroughness in 1..=5 {
        let mut model = input(source, Profile::Cell);
        model.options.thoroughness = thoroughness;
        let a = layout::families::layout(&model)?.0;
        let b = layout::families::layout(&model)?.0;
        assert_eq!(a.dump(), b.dump());
        assert!(a.check()?);
    }
    Ok(())
}
