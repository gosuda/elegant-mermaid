use super::*;

fn resolved(source: &str) -> (Model, Vec<Diagnostic>) {
    let parsed = crate::syntax::er::parse(source, &[]);
    assert_eq!(parsed.diagnostics, Vec::<Diagnostic>::new());
    resolve(source, &parsed.document)
}

#[test]
fn implicit_entities_keep_first_insertion_order() {
    let (model, diagnostics) = resolved("erDiagram\nB ||--o{ A : owns\nA\nB\n");
    assert_eq!(diagnostics.len(), 0);
    assert_eq!(
        model
            .entities
            .iter()
            .map(|entity| entity.id.as_str())
            .collect::<Vec<_>>(),
        ["B", "A"]
    );
    assert_eq!(
        model
            .entities
            .first()
            .map(|entity| entity.classes.as_slice()),
        Some(["default".to_owned()].as_slice())
    );
}

#[test]
fn first_nonempty_alias_wins_after_implicit_declaration() {
    let (model, _) = resolved("erDiagram\nA ||--|| B : owns\nA [First]\nA [Second]\n");
    assert_eq!(
        model.entities.first().map(|entity| entity.label.as_str()),
        Some("First")
    );
    assert_eq!(
        model
            .relationships
            .first()
            .map(|relation| relation.from.as_str()),
        Some("A")
    );
}

#[test]
fn repeated_blocks_append_attributes_and_keys() {
    let source = "erDiagram\nA { int? id PK,FK,PK \"key\" }\nA { string id UK }\n";
    let (model, diagnostics) = resolved(source);
    assert_eq!(diagnostics.len(), 0);
    let attributes = model
        .entities
        .first()
        .map(|entity| entity.attributes.as_slice())
        .unwrap_or(&[]);
    assert_eq!(attributes.len(), 2);
    assert_eq!(
        attributes
            .first()
            .map(|attribute| attribute.attribute_type.as_str()),
        Some("int?")
    );
    assert_eq!(
        attributes
            .first()
            .map(|attribute| attribute.keys.as_slice()),
        Some(["PK".to_owned(), "FK".to_owned(), "PK".to_owned()].as_slice())
    );
    assert_eq!(
        attributes
            .first()
            .map(|attribute| attribute.comment.as_str()),
        Some("key")
    );
    assert_eq!(
        attributes
            .get(1)
            .map(|attribute| attribute.comment.as_str()),
        Some("")
    );
    assert_eq!(
        attributes.first().map(|attribute| attribute.nullable),
        Some(true)
    );
}

#[test]
fn attributes_keep_backticks_and_field_spans() -> Result<(), &'static str> {
    let source = "erDiagram\nA { `long type` `field name` }\n";
    let (model, diagnostics) = resolved(source);
    assert_eq!(diagnostics.len(), 0);
    let attribute = model
        .entities
        .first()
        .and_then(|entity| entity.attributes.first())
        .ok_or("missing attribute")?;
    assert_eq!(attribute.attribute_type, "long type");
    assert_eq!(attribute.name, "field name");
    assert_eq!(
        source.get(attribute.type_span.start..attribute.type_span.end),
        Some("`long type`")
    );
    assert_eq!(
        source.get(attribute.name_span.start..attribute.name_span.end),
        Some("`field name`")
    );
    Ok(())
}

#[test]
fn repeated_self_relationships_keep_markers_and_declaration_index() {
    let (model, _) = resolved("erDiagram\nA |o..|{ A : relates\nA }o--|| A : other\n");
    assert_eq!(model.relationships.len(), 2);
    assert_eq!(
        model
            .relationships
            .iter()
            .map(|relation| (
                relation.marker_start,
                relation.marker_end,
                relation.identifying,
                relation.index
            ))
            .collect::<Vec<_>>(),
        [
            ("one_or_more", "zero_or_one", false, 0),
            ("only_one", "zero_or_more", true, 1)
        ]
    );
}

#[test]
fn subgraphs_keep_nested_empty_groups_and_local_direction() {
    let (model, diagnostics) = resolved(
        "erDiagram\ndirection LR\nsubgraph Outer [Outer group]\n direction BT\n subgraph Inner\n A\n end\n subgraph Empty\n end\nend\ndirection RL\n",
    );
    assert_eq!(diagnostics.len(), 0);
    assert_eq!(model.direction, "RL");
    assert_eq!(
        model
            .groups
            .iter()
            .map(|group| (group.id.as_str(), group.parent, group.members.len()))
            .collect::<Vec<_>>(),
        [
            ("Inner", Some(2), 1),
            ("Empty", Some(2), 0),
            ("Outer", None, 2)
        ]
    );
    assert_eq!(
        model.groups.get(2).map(|group| group.direction.as_str()),
        Some("BT")
    );
    assert_eq!(
        model.groups.get(2).map(|group| group.label.as_str()),
        Some("Outer group")
    );
}

#[test]
fn first_completed_group_claims_membership_and_alias_only_returns_nothing() {
    let (model, _) =
        resolved("erDiagram\nsubgraph First\nA\nB [Alias]\nend\nsubgraph Second\nA\nend\n");
    assert_eq!(
        model
            .groups
            .iter()
            .map(|group| group.members.len())
            .collect::<Vec<_>>(),
        [1, 0]
    );
    assert_eq!(
        model
            .entities
            .iter()
            .map(|entity| entity.parent)
            .collect::<Vec<_>>(),
        [Some(0), None]
    );
}

#[test]
fn endpoint_binding_observes_subgraph_completion() {
    let (model, _) =
        resolved("erDiagram\nG ||--|| A : before\nsubgraph G\nB\nend\nG ||--|| A : after\n");
    assert_eq!(
        model
            .relationships
            .first()
            .map(|relation| relation.from_target),
        Some(Target::Entity(0))
    );
    assert_eq!(
        model
            .relationships
            .get(1)
            .map(|relation| relation.from_target),
        Some(Target::Group(0))
    );
}

#[test]
fn definitions_compile_late_and_missing_style_targets_are_ignored() {
    let (model, diagnostics) = resolved(
        "erDiagram\nclass Missing hot\nstyle Missing fill:red\nA:::hot\nstyle A stroke:blue\nclass A hot\nclassDef hot fill:#abc,color:red\nclassDef hot stroke:#123\n",
    );
    assert_eq!(diagnostics.len(), 0);
    assert_eq!(model.entities.len(), 1);
    assert_eq!(
        model
            .entities
            .first()
            .map(|entity| entity.classes.as_slice()),
        Some(["default".to_owned(), "hot".to_owned(), "hot".to_owned()].as_slice())
    );
    assert_eq!(
        model
            .definitions
            .first()
            .map(|definition| definition.styles.as_slice()),
        Some(
            [
                "fill:#abc".to_owned(),
                "color:red".to_owned(),
                "stroke:#123".to_owned()
            ]
            .as_slice()
        )
    );
    assert_eq!(
        model
            .definitions
            .first()
            .map(|definition| definition.text_styles.as_slice()),
        Some(["color:red".to_owned()].as_slice())
    );
}

#[test]
fn accessibility_trims_and_replaces() {
    let (model, _) =
        resolved("erDiagram\naccTitle: first\naccTitle: last \naccDescr: detail \nA\n");
    assert_eq!(model.acc_title, "last");
    assert_eq!(model.acc_descr, "detail");
}

#[test]
fn empty_blocks_and_missing_attribute_fields_keep_defaults() {
    let (model, diagnostics) = resolved("erDiagram\nA {}\nA { string value }\n");
    assert_eq!(diagnostics.len(), 0);
    assert_eq!(model.entities.len(), 1);
    let values = model
        .entities
        .iter()
        .flat_map(|entity| &entity.attributes)
        .map(|attribute| {
            (
                attribute.keys.len(),
                attribute.comment.as_str(),
                attribute.nullable,
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(values, [(0, "", false)]);
}

#[test]
fn label_entities_decode_without_touching_identity_or_styles() {
    let (model, diagnostics) =
        resolved("erDiagram\nA [\"A #amp; B\"]\nstyle A fill:#abc\nA ||--|| B : \"#35; #amp;\"\n");
    assert_eq!(diagnostics.len(), 0);
    assert_eq!(
        model.entities.first().map(Entity::display_name),
        Some("A & B".to_owned())
    );
    assert_eq!(
        model.entities.first().map(|entity| entity.id.as_str()),
        Some("A")
    );
    assert_eq!(
        model
            .entities
            .first()
            .map(|entity| entity.styles.as_slice()),
        Some(["fill:#abc".to_owned()].as_slice())
    );
    assert_eq!(
        model
            .relationships
            .first()
            .map(|relation| relation.label.as_str()),
        Some("# &")
    );
}

#[test]
fn duplicate_subgraphs_keep_closure_records_and_last_lookup() {
    let (model, diagnostics) =
        resolved("erDiagram\nsubgraph G\nA\nend\nsubgraph G\nB\nend\nG ||--|| C : owns\n");
    assert_eq!(diagnostics.len(), 0);
    assert_eq!(
        model
            .groups
            .iter()
            .map(|group| group.id.as_str())
            .collect::<Vec<_>>(),
        ["G", "G"]
    );
    assert_eq!(
        model
            .relationships
            .first()
            .map(|relation| relation.from_target),
        Some(Target::Group(1))
    );
}
