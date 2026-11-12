use elegant_mermaid::{
    RenderError, layout, model,
    scene::{DumpOptions, Profile},
    syntax,
};

type TestResult = Result<(), Box<dyn std::error::Error>>;

#[test]
fn generated_route_ids_skip_source_node_and_group_ids() -> TestResult {
    let source = "flowchart TB\ne0[A]\nsubgraph e1[Group]\nB\nend\ne0 -->|yes| B\nB -->|back| e0\n";
    let parsed = syntax::flowchart::parse(source, &[]);
    let (model, _) = model::flowchart::resolve(source, &parsed.document);
    for profile in [Profile::Vector, Profile::Cell] {
        let input = layout::flowchart::from_flowchart(&model, profile, DumpOptions::default());
        assert_eq!(
            input
                .routes
                .iter()
                .map(|route| route.id.as_str())
                .collect::<Vec<_>>(),
            vec!["e2", "e3"]
        );
        assert!(input.boxes.iter().any(|b| b.id == "e0"));
        assert!(input.boxes.iter().any(|b| b.id == "e1"));
        assert!(
            input
                .labels
                .iter()
                .any(|label| label.id == "e2.label" && label.owner == "e2" && label.text == "yes")
        );
        assert!(
            input
                .labels
                .iter()
                .any(|label| label.id == "e3.label" && label.owner == "e3" && label.text == "back")
        );
        let scene = layout::families::layout(&input)?.0;
        assert!(scene.check()?);
        assert_eq!(scene.routes()[0].from, "e0");
        assert_eq!(scene.routes()[0].to, "B");
        assert_eq!(scene.routes()[0].id, "e2");
    }
    Ok(())
}

#[test]
fn noncanonical_numeric_source_id_does_not_reserve_a_generated_id() {
    let source = "flowchart TB\ne00 --> B\n";
    let parsed = syntax::flowchart::parse(source, &[]);
    let (model, _) = model::flowchart::resolve(source, &parsed.document);
    let input = layout::flowchart::from_flowchart(&model, Profile::Cell, DumpOptions::default());
    assert_eq!(input.routes[0].id, "e0");
    assert_eq!(input.routes[0].from, "e00");
}

#[test]
fn explicit_user_edge_identity_remains_in_the_semantic_model() {
    let source = "flowchart LR\ne0[box]\nA named@--> B\nnamed@{ animate: true }\n";
    let parsed = syntax::flowchart::parse(source, &[]);
    let (model, _) = model::flowchart::resolve(source, &parsed.document);
    let input = layout::flowchart::from_flowchart(&model, Profile::Cell, DumpOptions::default());
    assert_eq!(model.edges[0].user_id, "named");
    assert_eq!(
        model.edges[0].attrs.get("animate").map(String::as_str),
        Some("true")
    );
    assert_eq!(input.routes[0].id, "e1");
}

#[test]
fn ambiguous_direct_model_owner_names_are_rejected() {
    let source = "flowchart TB\nA --> B\n";
    let parsed = syntax::flowchart::parse(source, &[]);
    let (model, _) = model::flowchart::resolve(source, &parsed.document);
    let mut input =
        layout::flowchart::from_flowchart(&model, Profile::Cell, DumpOptions::default());
    input.routes[0].id = "A".into();
    assert!(matches!(
        layout::families::layout(&input),
        Err(RenderError::InvalidConfig { errors: 1 })
    ));
}
