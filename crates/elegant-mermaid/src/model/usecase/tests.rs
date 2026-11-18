use super::*;

fn resolved(source: &str) -> (Model, Vec<Diagnostic>) {
    let parsed = crate::syntax::usecase::parse(source, &[]);
    assert_eq!(parsed.diagnostics, Vec::<Diagnostic>::new());
    resolve(source, &parsed.document)
}

#[test]
fn forward_actor_references_keep_first_occurrence_order() -> Result<(), &'static str> {
    let (model, diagnostics) = resolved("usecase-beta\nA --> B\nactor A(User)\nB(Task)\n");
    assert_eq!(diagnostics.len(), 0);
    assert_eq!(
        model
            .nodes
            .iter()
            .map(|node| node.id.as_str())
            .collect::<Vec<_>>(),
        ["A", "B"]
    );
    let actor = model.nodes.first().ok_or("missing actor")?;
    assert_eq!((actor.kind, actor.label.as_str()), (Kind::Actor, "User"));
    assert_eq!(model.nodes.get(1).ok_or("missing usecase")?.label, "Task");
    assert_eq!(model.relations.first().ok_or("missing edge")?.id, "edge-0");
    Ok(())
}

#[test]
fn matching_declarations_merge_unique_classes() -> Result<(), &'static str> {
    let (model, diagnostics) = resolved("usecase-beta\nA(Task):::one\nA(Task):::two,one\n");
    assert_eq!(diagnostics.len(), 0);
    assert_eq!(model.nodes.len(), 1);
    assert_eq!(
        model.nodes.first().ok_or("missing node")?.classes,
        ["one", "two"]
    );
    Ok(())
}

#[test]
fn declaration_conflicts_report_later_and_related_first_span() -> Result<(), &'static str> {
    let source = "usecase-beta\nA(First)\nA(Second)\n";
    let (_, diagnostics) = resolved(source);
    assert_eq!(diagnostics.len(), 1);
    let error = diagnostics.first().ok_or("missing conflict")?;
    assert_eq!(error.code, "usecase/declaration-conflict");
    assert_eq!(
        error.message,
        "conflicting declaration of A: different label"
    );
    assert_eq!(
        source.get(error.span.start..error.span.end),
        Some("A(Second)")
    );
    let related = error.related.first().ok_or("missing related declaration")?;
    assert_eq!(
        source.get(related.span.start..related.span.end),
        Some("A(First)")
    );
    assert_eq!(related.message, "first declared here");
    Ok(())
}

#[test]
fn quoted_names_generate_ascii_ids_and_repeated_names_conflict() -> Result<(), &'static str> {
    let (_, diagnostics) = resolved("usecase-beta\n\"Some user\"\n\"Some user\"\n");
    let error = diagnostics.first().ok_or("missing generated conflict")?;
    assert_eq!(
        error.message,
        "conflicting declaration of Some_user: duplicate generated id"
    );
    Ok(())
}

#[test]
fn boundary_members_are_ordered_unique_and_geometry_defaults_rect() -> Result<(), &'static str> {
    let (model, diagnostics) =
        resolved("usecase-beta\nsystemBoundary S(Title)\nactor A\nB\nB\nend\n");
    assert_eq!(diagnostics.len(), 0);
    let group = model.nodes.first().ok_or("missing boundary")?;
    assert_eq!(
        (group.kind, group.boundary_type.as_str()),
        (Kind::Boundary, "rect")
    );
    assert_eq!(group.members, ["A", "B"]);
    assert_eq!(
        model
            .nodes
            .iter()
            .skip(1)
            .map(|node| node.parent.as_str())
            .collect::<Vec<_>>(),
        ["S", "S"]
    );
    Ok(())
}

#[test]
fn metadata_updates_existing_symbols_without_creating_nodes() -> Result<(), &'static str> {
    let (model, diagnostics) = resolved(
        "usecase-beta\nA@{business:true}\nA(Task)\nactor B\nB@{type:hollow}\nB@{business:true}\n",
    );
    assert_eq!(diagnostics.len(), 0);
    assert_eq!(model.nodes.len(), 2);
    assert!(
        model.nodes.first().ok_or("missing A")?.business,
        "metadata must make A a business use case; observed nodes: {:?}",
        model.nodes
    );
    let actor = model.nodes.get(1).ok_or("missing B")?;
    assert_eq!(actor.actor_type, "hollow");
    assert!(
        actor.business,
        "the second metadata update must preserve hollow B and enable business; observed actor: {actor:?}"
    );
    Ok(())
}

#[test]
fn invalid_metadata_reports_property_span() -> Result<(), &'static str> {
    let source = "usecase-beta\nA(Task)@{type:hollow}\n";
    let (_, diagnostics) = resolved(source);
    let error = diagnostics.first().ok_or("missing metadata error")?;
    assert_eq!(error.code, "usecase/invalid-metadata");
    assert_eq!(error.message, "invalid metadata type for usecase A");
    assert_eq!(
        source.get(error.span.start..error.span.end),
        Some("type:hollow")
    );
    Ok(())
}

#[test]
fn incompatible_actor_geometry_reports_declaration() -> Result<(), &'static str> {
    let source = "usecase-beta\nactor A@{type:hollow,icon:person}\n";
    let (_, diagnostics) = resolved(source);
    let error = diagnostics.first().ok_or("missing actor error")?;
    assert_eq!(error.code, "usecase/invalid-actor");
    assert_eq!(
        error.message,
        "invalid actor A: icon cannot combine with hollow or awesome type"
    );
    assert_eq!(
        source.get(error.span.start..error.span.end),
        Some("A@{type:hollow,icon:person}")
    );
    Ok(())
}

#[test]
fn business_rectangle_is_rejected() -> Result<(), &'static str> {
    let (_, diagnostics) = resolved("usecase-beta\nA[Task]@{business:true}\n");
    let error = diagnostics.first().ok_or("missing business error")?;
    assert_eq!(error.code, "usecase/invalid-business-usecase");
    assert_eq!(error.message, "rectangular use case A cannot be business");
    Ok(())
}

#[test]
fn relation_ids_labels_and_backward_markers_preserve_order() -> Result<(), &'static str> {
    let (model, diagnostics) =
        resolved("usecase-beta\nA named@ --> B\nA <-- back -- C\nA -- next --o D\nA ----> E\n");
    assert_eq!(diagnostics.len(), 0);
    assert_eq!(
        model
            .relations
            .iter()
            .map(|edge| edge.id.as_str())
            .collect::<Vec<_>>(),
        ["named", "edge-0", "edge-1", "edge-2"]
    );
    let back = model.relations.get(1).ok_or("missing backward edge")?;
    assert_eq!(
        (
            back.from.as_str(),
            back.to.as_str(),
            back.marker_start.as_str(),
            back.label.as_str()
        ),
        ("A", "C", "point", "back")
    );
    assert_eq!(
        model
            .relations
            .get(2)
            .ok_or("missing circle edge")?
            .marker_end,
        "circle"
    );
    assert_eq!(
        model
            .relations
            .get(3)
            .ok_or("missing long edge")?
            .min_length,
        3
    );
    Ok(())
}

#[test]
fn semantic_relations_normalize_and_reject_wrong_endpoints() -> Result<(), &'static str> {
    let (_, diagnostics) = resolved("usecase-beta\nactor A\nA ..>:INCLUDE B\n");
    let error = diagnostics.first().ok_or("missing relation error")?;
    assert_eq!(error.code, "usecase/invalid-relationship");
    assert_eq!(
        error.message,
        "invalid include relationship: both endpoints must be use cases"
    );
    let (model, diagnostics) = resolved("usecase-beta\nA ..>:EXTEND B\nA --|> B\n");
    assert_eq!(diagnostics.len(), 0);
    assert_eq!(
        model.relations.first().ok_or("missing extend")?.label,
        "«extend»"
    );
    assert_eq!(
        model
            .relations
            .get(1)
            .ok_or("missing generalization")?
            .marker_end,
        "extension"
    );
    Ok(())
}

#[test]
fn bare_endpoint_class_suffix_is_rejected() -> Result<(), &'static str> {
    let source = "usecase-beta\nA --> B:::hot\n";
    let (_, diagnostics) = resolved(source);
    let error = diagnostics.first().ok_or("missing reference error")?;
    assert_eq!(error.code, "usecase/reference-class-suffix");
    assert_eq!(
        error.message,
        "endpoint B uses classes without a declaration"
    );
    assert_eq!(
        source.get(error.span.start..error.span.end),
        Some("B:::hot")
    );
    Ok(())
}

#[test]
fn notes_require_actor_or_usecase_and_keep_order() -> Result<(), &'static str> {
    let (model, diagnostics) = resolved(
        "usecase-beta\nnote for A \"First\"\nA(Task)\nnote for A \"Second\"\nnote for Missing \"No\"\n",
    );
    assert_eq!(
        model
            .notes
            .iter()
            .map(|note| (note.id.as_str(), note.text.as_str()))
            .collect::<Vec<_>>(),
        [("note-0", "First"), ("note-1", "Second")]
    );
    assert_eq!(
        diagnostics.first().ok_or("missing note error")?.message,
        "unresolved note target Missing"
    );
    Ok(())
}

#[test]
fn json_preserves_nested_property_order_and_rejects_metadata() -> Result<(), &'static str> {
    let (model, diagnostics) = resolved(
        "usecase-beta\njson J@{\"z\":{\"b\":1,\"a\":2},\"a\":[true,null]}\nJ@{business:true}\n",
    );
    assert_eq!(
        model.nodes.first().ok_or("missing JSON node")?.json,
        Some(Json::Object(vec![
            (
                "\"z\"".into(),
                Json::Object(vec![
                    ("\"b\"".into(), Json::Scalar("1".into())),
                    ("\"a\"".into(), Json::Scalar("2".into()))
                ])
            ),
            (
                "\"a\"".into(),
                Json::Array(vec![
                    Json::Scalar("true".into()),
                    Json::Scalar("null".into())
                ])
            )
        ]))
    );
    assert_eq!(
        diagnostics
            .first()
            .ok_or("missing JSON metadata error")?
            .message,
        "invalid metadata business for json J"
    );
    Ok(())
}

#[test]
fn definitions_replace_classes_deduplicate_styles_append() -> Result<(), &'static str> {
    let (model, diagnostics) = resolved(
        "usecase-beta\nclassDef hot fill:red\nclassDef hot fill:blue\nclass A hot,other\nA(Task):::hot\nstyle A color:red\nstyle A stroke:blue\n",
    );
    assert_eq!(diagnostics.len(), 0);
    assert_eq!(model.definitions, [("hot".into(), "fill:blue".into())]);
    let node = model.nodes.first().ok_or("missing styled node")?;
    assert_eq!(node.classes, ["hot", "other"]);
    assert_eq!(node.styles, ["color:red", "stroke:blue"]);
    Ok(())
}

#[test]
fn explicit_edge_metadata_enables_animation() -> Result<(), &'static str> {
    let (model, diagnostics) = resolved("usecase-beta\nlink@{animation:fast}\nA link@ --> B\n");
    assert_eq!(diagnostics.len(), 0);
    let edge = model.relations.first().ok_or("missing animated edge")?;
    assert!(
        edge.animate,
        "setting animation speed must enable animation; observed edge: {edge:?}"
    );
    assert_eq!(edge.animation, "fast");
    Ok(())
}

#[test]
fn accessibility_direction_and_stereotype_are_last_wins() -> Result<(), &'static str> {
    let (model, diagnostics) = resolved(
        "usecase-beta\naccTitle: first\naccTitle: last\naccDescr: detail\ndirection LR\ndirection TD\nA(Task)<< service >>\n",
    );
    assert_eq!(diagnostics.len(), 0);
    assert_eq!(
        (
            model.acc_title.as_str(),
            model.acc_descr.as_str(),
            model.direction.as_str()
        ),
        ("last", "detail", "TB")
    );
    assert_eq!(
        model.nodes.first().ok_or("missing stereotype")?.stereotype,
        "service"
    );
    Ok(())
}

#[test]
fn unresolved_assignments_never_create_symbols() -> Result<(), &'static str> {
    for (source, message, span) in [
        (
            "usecase-beta\nM@{business:true}\n",
            "unresolved metadata target M",
            Span { start: 13, end: 14 },
        ),
        (
            "usecase-beta\nclass X hot\n",
            "unresolved class target X",
            Span { start: 19, end: 20 },
        ),
        (
            "usecase-beta\nstyle X fill:red\n",
            "unresolved style target X",
            Span { start: 19, end: 20 },
        ),
        (
            "usecase-beta\nnote for X \"text\"\n",
            "unresolved note target X",
            Span { start: 22, end: 23 },
        ),
    ] {
        let (model, diagnostics) = resolved(source);
        assert_eq!(model.nodes.len(), 0);
        assert_eq!(model.notes.len(), 0);
        assert_eq!(diagnostics.len(), 1);
        let error = diagnostics.first().ok_or("missing unresolved target")?;
        assert_eq!(error.code, "usecase/unresolved-target");
        assert_eq!(error.message, message);
        assert_eq!(error.span, span);
    }
    Ok(())
}

#[test]
fn explicit_edge_ids_are_reserved_before_endpoint_references() -> Result<(), &'static str> {
    let source = "usecase-beta\nA --> link\nB link@ --> C\n";
    let (model, diagnostics) = resolved(source);
    assert!(
        !model.nodes.iter().any(|node| node.id == "link"),
        "an explicit edge id must never become an implicit use case; observed nodes: {:?}",
        model.nodes
    );
    let error = diagnostics
        .first()
        .ok_or("missing forbidden endpoint error")?;
    assert_eq!(error.code, "usecase/invalid-relationship");
    assert_eq!(
        error.message,
        "invalid association relationship: edge symbols cannot be endpoints"
    );
    assert_eq!(
        source.get(error.span.start..error.span.end),
        Some("A --> link")
    );
    Ok(())
}

#[test]
fn duplicate_explicit_edges_report_the_later_id() -> Result<(), &'static str> {
    let (model, diagnostics) = resolved("usecase-beta\nA link@ --> B\nC link@ --> D\n");
    assert_eq!(model.relations.len(), 1);
    assert_eq!(diagnostics.len(), 1);
    let error = diagnostics.first().ok_or("missing duplicate edge")?;
    assert_eq!(error.code, "usecase/declaration-conflict");
    assert_eq!(
        error.message,
        "conflicting declaration of link: duplicate symbol id"
    );
    assert_eq!(error.span, Span { start: 29, end: 33 });
    assert_eq!(
        error.related.first().ok_or("missing first edge")?.span,
        Span { start: 15, end: 19 }
    );
    Ok(())
}

#[test]
fn all_association_variants_and_generalization_keep_source_orientation() -> Result<(), &'static str>
{
    let (model, diagnostics) = resolved(
        "usecase-beta\nA -- B\nA --> B\nA <-- B\nA --o B\nA o-- B\nA --x B\nA x-- B\nactor X\nactor Y\nX --|> Y\n",
    );
    assert_eq!(diagnostics.len(), 0);
    assert_eq!(
        model
            .relations
            .iter()
            .map(|edge| (edge.marker_start.as_str(), edge.marker_end.as_str()))
            .collect::<Vec<_>>(),
        [
            ("none", "none"),
            ("none", "point"),
            ("point", "none"),
            ("none", "circle"),
            ("circle", "none"),
            ("none", "cross"),
            ("cross", "none"),
            ("none", "extension")
        ]
    );
    assert!(
        model.relations.iter().all(|edge| edge.min_length == 1),
        "ordinary associations and generalization must retain minimum length one; observed relations: {:?}",
        model.relations
    );
    assert_eq!(
        model.relations.last().ok_or("missing generalization")?.from,
        "X"
    );
    Ok(())
}

#[test]
fn boundary_and_json_endpoint_constraints_are_diagnostic() -> Result<(), &'static str> {
    let (_, diagnostics) = resolved("usecase-beta\nsystemBoundary S\nend\nS --> A\n");
    assert_eq!(
        diagnostics
            .first()
            .ok_or("missing boundary endpoint error")?
            .message,
        "invalid association relationship: boundaries cannot be endpoints"
    );
    let (_, diagnostics) = resolved("usecase-beta\njson J@{}\nJ --o A\n");
    assert_eq!(
        diagnostics
            .first()
            .ok_or("missing JSON endpoint error")?
            .message,
        "invalid association relationship: JSON endpoints require a solid point or markerless association"
    );
    Ok(())
}

#[test]
fn empty_json_metadata_is_still_invalid() -> Result<(), &'static str> {
    let (_, diagnostics) = resolved("usecase-beta\njson J@{}\nJ@{}\n");
    let error = diagnostics
        .first()
        .ok_or("missing empty JSON metadata error")?;
    assert_eq!(error.code, "usecase/invalid-metadata");
    assert_eq!(error.message, "invalid metadata metadata for json J");
    Ok(())
}
