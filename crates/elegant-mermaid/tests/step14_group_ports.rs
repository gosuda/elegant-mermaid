use elegant_mermaid::{
    cells, layout, model,
    scene::{Direction, DumpOptions, Profile},
    syntax,
};

type TestResult = Result<(), Box<dyn std::error::Error>>;

#[test]
fn group_endpoint_aliases_and_title_gutters_work_in_every_direction() -> TestResult {
    let source = "flowchart TB\nsubgraph S[Group title]\nA\nend\nS --> A\nA --> S\nS --> X\nX --> S\nS --> S\n";
    let parsed = syntax::flowchart::parse(source, &[]);
    let (model, _) = model::flowchart::resolve(source, &parsed.document);
    for profile in [Profile::Vector, Profile::Cell] {
        for direction in [Direction::Tb, Direction::Bt, Direction::Lr, Direction::Rl] {
            let mut input =
                layout::flowchart::from_flowchart(&model, profile, DumpOptions::default());
            input.direction = direction;
            let scene = layout::families::layout(&input)?.0;
            assert!(scene.check()?, "{profile:?} {direction:?}");
            let frame = scene
                .boxes()
                .iter()
                .find(|b| b.id == "S")
                .ok_or("frame missing")?
                .rect;
            let leading = |point: elegant_mermaid::geom::Point| match direction {
                Direction::Tb => point.y == frame.y,
                Direction::Bt => point.y == frame.y + frame.h,
                Direction::Lr => point.x == frame.x,
                Direction::Rl => point.x == frame.x + frame.w,
            };
            let trailing = |point: elegant_mermaid::geom::Point| match direction {
                Direction::Tb => point.y == frame.y + frame.h,
                Direction::Bt => point.y == frame.y,
                Direction::Lr => point.x == frame.x + frame.w,
                Direction::Rl => point.x == frame.x,
            };
            assert!(leading(scene.routes()[0].points[0]));
            assert!(trailing(
                *scene.routes()[1].points.last().ok_or("route missing")?
            ));
            assert!(trailing(scene.routes()[2].points[0]));
            assert!(leading(
                *scene.routes()[3].points.last().ok_or("route missing")?
            ));
            assert_eq!(scene.routes().len(), 5);
            assert_eq!(scene.boxes().iter().filter(|b| b.id == "S").count(), 1);
            if profile == Profile::Cell {
                let rendered = cells::render(&scene, &cells::Options::default())?;
                assert_eq!(
                    rendered.refused_clusters, 0,
                    "{direction:?}\n{}",
                    rendered.text
                );
                assert!(rendered.text.contains("Group title"));
            }
        }
    }
    Ok(())
}

#[test]
fn independent_contents_remain_upright_under_each_parent_direction() -> TestResult {
    let source = "flowchart TB\nsubgraph S[Independent title]\ndirection LR\nA --> B\nend\nS --> X\nS --> S\n";
    let parsed = syntax::flowchart::parse(source, &[]);
    let (model, _) = model::flowchart::resolve(source, &parsed.document);
    for direction in [Direction::Tb, Direction::Bt, Direction::Lr, Direction::Rl] {
        let mut input =
            layout::flowchart::from_flowchart(&model, Profile::Cell, DumpOptions::default());
        input.direction = direction;
        let (scene, diagnostics) = layout::families::layout(&input)?;
        assert!(
            !diagnostics
                .iter()
                .any(|d| d.code == "flowchart/subgraph-direction-ignored")
        );
        assert!(scene.check()?, "{direction:?}");
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
        assert_eq!(scene.routes().len(), 3);
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
fn explicit_empty_group_title_is_not_replaced_by_its_id() -> TestResult {
    let source = "flowchart TB\nsubgraph S[\"\"]\nend\n";
    let parsed = syntax::flowchart::parse(source, &[]);
    let (model, _) = model::flowchart::resolve(source, &parsed.document);
    let input = layout::flowchart::from_flowchart(&model, Profile::Cell, DumpOptions::default());
    let title = input
        .labels
        .iter()
        .find(|l| l.owner == "S")
        .ok_or("title value missing")?;
    assert_eq!(title.text, "");
    let scene = layout::families::layout(&input)?.0;
    assert_eq!(
        scene
            .labels()
            .iter()
            .find(|l| l.owner == "S")
            .ok_or("placed title missing")?
            .text,
        ""
    );
    assert!(
        layout::modeldump::model_dump(&input).contains("\"exclusive\":false,\"direction\":\"\"")
    );
    Ok(())
}
