use super::*;

fn resolved(source: &str) -> Result<Model, &'static str> {
    let parsed = crate::syntax::requirement::parse(source, &[]);
    if !parsed.diagnostics.is_empty() {
        return Err("requirement syntax diagnostics");
    }
    let (model, diagnostics) = resolve(source, &parsed.document);
    assert_eq!(diagnostics, Vec::<Diagnostic>::new());
    Ok(model)
}

#[test]
fn requirement_fields_keep_first_value_and_all_spans() -> Result<(), &'static str> {
    let source = "requirementDiagram\nfunctionalRequirement R {\nid: first\nid: second\ntext: detail\nrisk: high\nverifyMethod: inspection\n}\n";
    let model = resolved(source)?;
    let node = model.requirements.first().ok_or("missing requirement")?;
    assert_eq!(
        (
            &*node.name,
            &*node.kind,
            &*node.id,
            &*node.text,
            &*node.risk,
            &*node.verify_method
        ),
        (
            "R",
            "Functional Requirement",
            "first",
            "detail",
            "High",
            "Inspection"
        )
    );
    assert_eq!(node.fields.len(), 5);
    let first = node.fields.first().ok_or("missing field")?;
    assert_eq!(
        source.get(first.span.start..first.span.end),
        Some("id: first")
    );
    assert_eq!(
        source.get(first.keyword_span.start..first.keyword_span.end),
        Some("id")
    );
    assert_eq!(
        source.get(first.colon_span.start..first.colon_span.end),
        Some(":")
    );
    assert_eq!(
        source.get(node.delimiters.0.start..node.delimiters.0.end),
        Some("{")
    );
    assert_eq!(
        source.get(node.delimiters.1.start..node.delimiters.1.end),
        Some("}")
    );
    Ok(())
}

#[test]
fn empty_definitions_have_empty_fields_and_default_classes() -> Result<(), &'static str> {
    let model = resolved("requirementDiagram\nrequirement R {\n}\nelement E {\n}\n")?;
    let requirement = model.requirements.first().ok_or("missing requirement")?;
    assert_eq!(
        (
            &*requirement.id,
            &*requirement.text,
            &*requirement.risk,
            &*requirement.verify_method
        ),
        ("", "", "", "")
    );
    assert_eq!(
        requirement
            .classes
            .iter()
            .map(|v| v.value.as_str())
            .collect::<Vec<_>>(),
        ["default"]
    );
    assert_eq!(requirement.styles.len(), 0);
    let element = model.elements.first().ok_or("missing element")?;
    assert_eq!((&*element.kind, &*element.docref), ("", ""));
    assert_eq!(element.rows(), ["<<Element>>", "E"]);
    assert_eq!(model.direction, "TB");
    Ok(())
}

#[test]
fn duplicate_definitions_keep_first_fields_without_leaking_pending_values()
-> Result<(), &'static str> {
    let model = resolved(
        "requirementDiagram\nrequirement R {\nid: first\n}\nphysicalRequirement R {\nid: ignored\n}\nrequirement S {\n}\nelement E {\ntype: service\ndocref: first\n}\nelement E {\ntype: ignored\n}\nelement F {\n}\n",
    )?;
    assert_eq!(
        model
            .requirements
            .iter()
            .map(|n| (n.name.as_str(), n.kind.as_str(), n.id.as_str()))
            .collect::<Vec<_>>(),
        [("R", "Requirement", "first"), ("S", "Requirement", "")]
    );
    assert_eq!(
        model
            .elements
            .iter()
            .map(|n| (n.name.as_str(), n.kind.as_str(), n.docref.as_str()))
            .collect::<Vec<_>>(),
        [("E", "service", "first"), ("F", "", "")]
    );
    Ok(())
}

#[test]
fn namespaces_stay_separate_and_lookup_prefers_requirements() -> Result<(), &'static str> {
    let model = resolved(
        "requirementDiagram\nelement X {\n}\nrequirement X {\n}\nX - traces -> X\nstyle X fill:red\n",
    )?;
    assert_eq!(model.requirements.len(), 1);
    assert_eq!(model.elements.len(), 1);
    let relation = model.relationships.first().ok_or("missing relationship")?;
    assert_eq!(
        (relation.from_node, relation.to_node),
        (Some(NodeRef::Requirement(0)), Some(NodeRef::Requirement(0)))
    );
    assert_eq!(
        model
            .requirements
            .first()
            .ok_or("missing requirement")?
            .styles
            .first()
            .ok_or("missing style")?
            .value,
        "fill:red"
    );
    assert_eq!(
        model
            .elements
            .first()
            .ok_or("missing element")?
            .styles
            .len(),
        0
    );
    Ok(())
}

#[test]
fn reversed_and_unresolved_relations_remain_ordered_without_implicit_nodes()
-> Result<(), &'static str> {
    let source = "requirementDiagram\nA <- contains - B\nA - copies -> B\nA - derives -> B\nA - satisfies -> B\nA - verifies -> B\nA - refines -> B\nA - traces -> A\n";
    let model = resolved(source)?;
    assert_eq!((model.requirements.len(), model.elements.len()), (0, 0));
    assert_eq!(
        model
            .relationships
            .iter()
            .map(|r| r.kind.as_str())
            .collect::<Vec<_>>(),
        [
            "contains",
            "copies",
            "derives",
            "satisfies",
            "verifies",
            "refines",
            "traces"
        ]
    );
    let first = model.relationships.first().ok_or("missing relationship")?;
    assert_eq!(
        (&*first.from.value, &*first.to.value, &*first.label),
        ("B", "A", "<<contains>>")
    );
    assert_eq!((first.from_node, first.to_node), (None, None));
    assert_eq!(
        source.get(first.arrow_span.start..first.arrow_span.end),
        Some("<-")
    );
    assert_eq!(
        source.get(first.from.span.start..first.from.span.end),
        Some("B")
    );
    Ok(())
}

#[test]
fn later_definitions_resolve_existing_endpoint_records() -> Result<(), &'static str> {
    let model =
        resolved("requirementDiagram\nR - verifies -> E\nelement E {\n}\nrequirement R {\n}\n")?;
    let relation = model.relationships.first().ok_or("missing relationship")?;
    assert_eq!(
        (relation.from_node, relation.to_node),
        (Some(NodeRef::Requirement(0)), Some(NodeRef::Element(0)))
    );
    Ok(())
}

#[test]
fn classes_append_and_late_definitions_reach_existing_nodes() -> Result<(), &'static str> {
    let model = resolved(
        "requirementDiagram\nclassDef hot fill:red,color:blue\nrequirement R:::hot {\n}\nrequirement R:::unknown {\n}\nclass R hot\nclassDef hot stroke:black\n",
    )?;
    let node = model.requirements.first().ok_or("missing requirement")?;
    assert_eq!(
        node.classes
            .iter()
            .map(|c| c.value.as_str())
            .collect::<Vec<_>>(),
        ["default", "hot", "unknown", "hot"]
    );
    assert_eq!(
        node.styles
            .iter()
            .map(|s| s.value.as_str())
            .collect::<Vec<_>>(),
        [
            "fill:red",
            "color:blue",
            "fill:red",
            "color:blue",
            "stroke:black"
        ]
    );
    let definition = model
        .class_definitions
        .first()
        .ok_or("missing class definition")?;
    assert_eq!(
        definition
            .text_styles
            .iter()
            .map(|s| s.value.as_str())
            .collect::<Vec<_>>(),
        ["color:blue"]
    );
    Ok(())
}

#[test]
fn direct_styles_stop_at_first_missing_target_and_preserve_order() -> Result<(), &'static str> {
    let model = resolved(
        "requirementDiagram\nrequirement A {\n}\nelement B {\n}\nstyle A,Missing,B fill:red,stroke:blue\nstyle A color:green\nclass Missing,B unknown\n",
    )?;
    assert_eq!(
        model
            .requirements
            .first()
            .ok_or("missing requirement")?
            .styles
            .iter()
            .map(|s| s.value.as_str())
            .collect::<Vec<_>>(),
        ["fill:red", "stroke:blue", "color:green"]
    );
    let element = model.elements.first().ok_or("missing element")?;
    assert_eq!(element.styles.len(), 0);
    assert_eq!(
        element
            .classes
            .iter()
            .map(|s| s.value.as_str())
            .collect::<Vec<_>>(),
        ["default", "unknown"]
    );
    Ok(())
}

#[test]
fn directions_and_accessibility_use_last_trimmed_value() -> Result<(), &'static str> {
    let model = resolved(
        "accTitle: leading\nrequirementDiagram\ndirection LR\ndirection BT\naccTitle: final title   \naccDescr: first\naccDescr { final description }\n",
    )?;
    assert_eq!(
        (&*model.direction, &*model.acc_title, &*model.acc_descr),
        ("BT", "final title", "final description")
    );
    assert_eq!(model.directives.len(), 4);
    Ok(())
}

#[test]
fn enum_values_map_to_display_strings() -> Result<(), &'static str> {
    let model = resolved(
        "requirementDiagram\ninterfaceRequirement A {\nrisk: medium\nverifyMethod: analysis\n}\nperformanceRequirement B {\nverifyMethod: demonstration\n}\nphysicalRequirement C {\n}\ndesignConstraint D {\n}\n",
    )?;
    assert_eq!(
        model
            .requirements
            .iter()
            .map(|r| r.kind.as_str())
            .collect::<Vec<_>>(),
        [
            "Interface Requirement",
            "Performance Requirement",
            "Physical Requirement",
            "Design Constraint"
        ]
    );
    let first = model.requirements.first().ok_or("missing requirement")?;
    assert_eq!(
        (&*first.risk, &*first.verify_method),
        ("Medium", "Analysis")
    );
    Ok(())
}

#[test]
fn labels_decode_entities_once_without_changing_identity_or_style() -> Result<(), &'static str> {
    let model = resolved(
        "requirementDiagram\nrequirement \"R#38;\" {\ntext: \"#35;name; #65; #unknown;\"\n}\nstyle \"R#38;\" fill:#abc\n",
    )?;
    let node = model.requirements.first().ok_or("missing requirement")?;
    assert_eq!(node.name, "R#38;");
    assert_eq!(node.text, "#name; A #unknown;");
    assert_eq!(
        node.rows(),
        ["<<Requirement>>", "R&", "Text: #name; A #unknown;"]
    );
    assert_eq!(
        node.styles.first().ok_or("missing style")?.value,
        "fill:#abc"
    );
    Ok(())
}

#[test]
fn empty_first_field_wins_and_does_not_create_a_display_row() -> Result<(), &'static str> {
    let model = resolved("requirementDiagram\nrequirement R {\nid: \"\"\nid: later\n}\n")?;
    let node = model.requirements.first().ok_or("missing requirement")?;
    assert_eq!(node.id, "");
    assert_eq!(node.fields.len(), 2);
    assert_eq!(node.rows(), ["<<Requirement>>", "R"]);
    Ok(())
}

#[test]
fn repeated_element_fields_keep_first_text_and_renderer_row_order() -> Result<(), &'static str> {
    let model = resolved(
        "requirementDiagram\nelement E {\ndocref: first\ntype: service\ndocref: ignored\ntype: ignored\n}\n",
    )?;
    let node = model.elements.first().ok_or("missing element")?;
    assert_eq!(
        node.rows(),
        ["<<Element>>", "E", "Type: service", "Doc Ref: first"]
    );
    assert_eq!(
        node.fields
            .iter()
            .map(|field| field.name.as_str())
            .collect::<Vec<_>>(),
        ["docref", "type", "docref", "type"]
    );
    Ok(())
}

#[test]
fn text_class_styles_select_lowercase_color_and_replace_first_fill() -> Result<(), &'static str> {
    let source = "requirementDiagram\nclassDef A fill:colorfill,COLOR:red,color:green\n";
    let model = resolved(source)?;
    let class = model
        .class_definitions
        .first()
        .ok_or("missing class definition")?;
    assert_eq!(
        class
            .text_styles
            .iter()
            .map(|style| style.value.as_str())
            .collect::<Vec<_>>(),
        ["bgFill:colorfill", "color:green"]
    );
    assert_eq!(
        class
            .styles
            .iter()
            .map(|style| style.value.as_str())
            .collect::<Vec<_>>(),
        ["fill:colorfill", "COLOR:red", "color:green"]
    );
    Ok(())
}
