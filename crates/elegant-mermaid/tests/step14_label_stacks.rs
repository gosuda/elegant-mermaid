use elegant_mermaid::{
    RenderError, cells, geom, layout, model,
    scene::{Direction, DumpOptions, Profile, TextRole},
    syntax,
};

type TestResult = Result<(), Box<dyn std::error::Error>>;

fn model(source: &str, profile: Profile) -> layout::input::Input {
    let parsed = syntax::flowchart::parse(source, &[]);
    let (resolved, _) = model::flowchart::resolve(source, &parsed.document);
    layout::flowchart::from_flowchart(&resolved, profile, DumpOptions::default())
}

fn stacked_labels_input(profile: Profile, direction: Direction) -> layout::input::Input {
    let mut input = model("flowchart TB\nA --> B\nB --> A\nA --> A\n", profile);
    input.direction = direction;
    for (index, (owner, text)) in [
        ("e0", "alpha"),
        ("e1", "back"),
        ("e2", "loop"),
        ("e0", "b"),
        ("e1", "z"),
        ("e2", "two"),
    ]
    .into_iter()
    .enumerate()
    {
        input.labels.push(layout::input::Label {
            id: format!("label-{index}"),
            owner: owner.into(),
            role: TextRole::Label,
            text: text.into(),
        });
    }
    input
}

#[test]
fn stacked_route_labels_preserve_declaration_identity() -> TestResult {
    for profile in [Profile::Vector, Profile::Cell] {
        for direction in [Direction::Tb, Direction::Bt, Direction::Lr, Direction::Rl] {
            let input = stacked_labels_input(profile, direction);
            let scene = layout::families::layout(&input)?.0;
            assert_eq!(scene.labels().len(), input.labels.len());
            for (actual, expected) in scene.labels().iter().zip(&input.labels) {
                assert_eq!(actual.id, expected.id);
                assert_eq!(actual.owner, expected.owner);
                assert_eq!(actual.text, expected.text);
            }
        }
    }
    Ok(())
}

#[test]
fn distinct_labels_on_forward_reversed_and_loop_routes_form_ordered_stacks() -> TestResult {
    for profile in [Profile::Vector, Profile::Cell] {
        for direction in [Direction::Tb, Direction::Bt, Direction::Lr, Direction::Rl] {
            let input = stacked_labels_input(profile, direction);
            let scene = layout::families::layout(&input)?.0;
            assert!(scene.check()?, "{profile:?} {direction:?}");
            for owner in ["e0", "e1", "e2"] {
                let labels: Vec<_> = scene
                    .labels()
                    .iter()
                    .filter(|label| label.owner == owner)
                    .collect();
                assert_eq!(labels.len(), 2);
                assert!(!geom::intersects(labels[0].rect, labels[1].rect)?);
                match direction {
                    Direction::Tb => assert!(labels[0].rect.y < labels[1].rect.y),
                    Direction::Bt => assert!(labels[0].rect.y > labels[1].rect.y),
                    Direction::Lr => assert!(labels[0].rect.x < labels[1].rect.x),
                    Direction::Rl => assert!(labels[0].rect.x > labels[1].rect.x),
                }
            }
        }
    }
    Ok(())
}

#[test]
fn stacked_cell_labels_render_without_refused_clusters() -> TestResult {
    for direction in [Direction::Tb, Direction::Bt, Direction::Lr, Direction::Rl] {
        let input = stacked_labels_input(Profile::Cell, direction);
        let scene = layout::families::layout(&input)?.0;
        let rendered = cells::render(&scene, &cells::Options::default())?;
        assert_eq!(
            rendered.refused_clusters, 0,
            "{direction:?}\n{}",
            rendered.text
        );
    }
    Ok(())
}

#[test]
fn stacked_route_labels_count_toward_text_limit() -> TestResult {
    for profile in [Profile::Vector, Profile::Cell] {
        for direction in [Direction::Tb, Direction::Bt, Direction::Lr, Direction::Rl] {
            let mut input = stacked_labels_input(profile, direction);
            input.options.limits.max_text_bytes = 19;
            assert!(matches!(
                layout::families::layout(&input),
                Err(RenderError::TooLarge {
                    limit: 19,
                    actual: 20
                })
            ));
        }
    }
    Ok(())
}

#[test]
fn labelled_parallel_proper_neighbours_size_internal_cross_width() -> TestResult {
    let mut source = String::from("flowchart TB\n");
    for _ in 0..8 {
        source.push_str("A -->|x| B\n");
    }
    for direction in [Direction::Tb, Direction::Bt, Direction::Lr, Direction::Rl] {
        let mut input = model(&source, Profile::Cell);
        input.direction = direction;
        let scene = layout::families::layout(&input)?.0;
        assert!(scene.check()?);
        assert_eq!(scene.labels().len(), 8);
        for node in scene.boxes() {
            let cross = match direction {
                Direction::Tb | Direction::Bt => node.rect.w,
                Direction::Lr | Direction::Rl => node.rect.h,
            };
            assert_eq!(cross, 9);
        }
        let rendered = cells::render(&scene, &cells::Options::default())?;
        assert_eq!(
            rendered.refused_clusters, 0,
            "{direction:?}\n{}",
            rendered.text
        );
    }
    Ok(())
}
