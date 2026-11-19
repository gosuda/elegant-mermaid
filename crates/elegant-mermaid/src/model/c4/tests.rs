use super::*;

fn resolved(source: &str) -> Model {
    let parsed = crate::syntax::c4::parse(source, &[]);
    assert_eq!(parsed.diagnostics.len(), 0, "{:#?}", parsed.diagnostics);
    let (model, diagnostics) = resolve(source, &parsed.document);
    assert_eq!(diagnostics.len(), 0);
    model
}

#[test]
fn all_headers_keep_c4_type() {
    for header in [
        "C4Context",
        "C4Container",
        "C4Component",
        "C4Dynamic",
        "C4Deployment",
    ] {
        let model = resolved(&format!("{header}\nPerson(p, \"Person\")\n"));
        assert_eq!(model.c4_type, header);
        assert_eq!(model.direction, "TB");
    }
}

#[test]
fn element_variants_keep_family_shape_and_external_identity() {
    let names = [
        "Person",
        "Person_Ext",
        "System",
        "System_Ext",
        "SystemDb",
        "SystemDb_Ext",
        "SystemQueue",
        "SystemQueue_Ext",
        "Container",
        "Container_Ext",
        "ContainerDb",
        "ContainerDb_Ext",
        "ContainerQueue",
        "ContainerQueue_Ext",
        "Component",
        "Component_Ext",
        "ComponentDb",
        "ComponentDb_Ext",
        "ComponentQueue",
        "ComponentQueue_Ext",
    ];
    let mut source = String::from("C4Context\n");
    for (index, name) in names.iter().enumerate() {
        source.push_str(&format!("{name}(a{index}, \"Label\")\n"));
    }
    let model = resolved(&source);
    assert_eq!(
        model
            .elements
            .iter()
            .map(|element| element.kind.as_str())
            .collect::<Vec<_>>(),
        [
            "person",
            "external_person",
            "system",
            "external_system",
            "system_db",
            "external_system_db",
            "system_queue",
            "external_system_queue",
            "container",
            "external_container",
            "container_db",
            "external_container_db",
            "container_queue",
            "external_container_queue",
            "component",
            "external_component",
            "component_db",
            "external_component_db",
            "component_queue",
            "external_component_queue"
        ]
    );
}

#[test]
fn repeated_elements_update_in_place_and_keep_omitted_optional_fields() -> Result<(), &'static str>
{
    let model = resolved(
        "C4Context\nContainer(a, \"First\", \"Rust\", \"Description\")\nPerson(b, \"B\")\nBoundary(g, \"Group\") {\nSystem_Ext(a, \"Last\")\n}\n",
    );
    assert_eq!(model.elements.len(), 2);
    let first = model.elements.first().ok_or("missing element")?;
    assert_eq!(
        (
            &*first.id,
            &*first.kind,
            &*first.parent,
            &*first.label.value
        ),
        ("a", "external_system", "g", "Last")
    );
    assert_eq!(
        first
            .fields
            .iter()
            .find(|field| field.name == "descr")
            .ok_or("missing description")?
            .value
            .value,
        "Description"
    );
    assert_eq!(
        first
            .fields
            .iter()
            .find(|field| field.name == "techn")
            .ok_or("missing technology")?
            .value
            .value,
        "Rust"
    );
    Ok(())
}

#[test]
fn required_alias_slots_are_positional_and_missing_labels_become_empty() -> Result<(), &'static str>
{
    let model = resolved(
        "C4Context\nPerson(a, \"First\")\nPerson(\"a\")\nPerson($alias=\"ignored\", \"Ignored\")\n",
    );
    assert_eq!(model.elements.len(), 1);
    assert_eq!(
        model.elements.first().ok_or("missing element")?.label.value,
        ""
    );
    Ok(())
}

#[test]
fn optional_named_arguments_override_fields_and_keep_attribute_spans() -> Result<(), &'static str> {
    let source = "C4Context\nContainer(a, \"API\", $descr=\"Description\", $techn=\"Rust\", $arbitrary=\"value\")\n";
    let model = resolved(source);
    let element = model.elements.first().ok_or("missing API")?;
    assert_eq!(
        element
            .fields
            .iter()
            .map(|field| (field.name.as_str(), field.value.value.as_str()))
            .collect::<Vec<_>>(),
        [
            ("techn", "Rust"),
            ("descr", "Description"),
            ("arbitrary", "value")
        ]
    );
    let attr = element.attributes.get(2).ok_or("missing attribute")?;
    assert_eq!(
        source.get(attr.span.start..attr.span.end),
        Some("$descr=\"Description\"")
    );
    assert_eq!(
        source.get(element.macro_span.start..element.macro_span.end),
        Some("Container")
    );
    assert_eq!(
        source.get(element.alias_span.start..element.alias_span.end),
        Some("a")
    );
    Ok(())
}

#[test]
fn boundaries_restore_parent_scope_and_helpers_insert_type() {
    let model = resolved(
        "C4Context\nEnterprise_Boundary(e, \"Enterprise\") {\nSystem_Boundary(s, \"System\") {\nContainer_Boundary(c, \"Container\") {\nPerson(a, \"A\")\n}\nPerson(b, \"B\")\n}\nPerson(d, \"D\")\n}\nPerson(z, \"Z\")\n",
    );
    assert_eq!(
        model
            .boundaries
            .iter()
            .map(|boundary| (boundary.id.as_str(), boundary.parent.as_str()))
            .collect::<Vec<_>>(),
        [("e", ""), ("s", "e"), ("c", "s")]
    );
    assert_eq!(
        model
            .elements
            .iter()
            .map(|element| element.parent.as_str())
            .collect::<Vec<_>>(),
        ["c", "s", "e", ""]
    );
    assert_eq!(
        model
            .boundaries
            .iter()
            .flat_map(|boundary| boundary
                .fields
                .iter()
                .filter(|field| field.name == "type")
                .map(|field| field.value.value.as_str()))
            .collect::<Vec<_>>(),
        ["ENTERPRISE", "SYSTEM", "CONTAINER"]
    );
}

#[test]
fn boundary_redefinition_resets_type_and_keeps_first_position() -> Result<(), &'static str> {
    let model = resolved(
        "C4Context\nBoundary(a, \"First\", \"Custom\") {\nPerson(p, \"P\")\n}\nBoundary(a, \"Last\") {\nPerson(q, \"Q\")\n}\n",
    );
    assert_eq!(model.boundaries.len(), 1);
    let boundary = model.boundaries.first().ok_or("missing boundary")?;
    assert_eq!(boundary.label.value, "Last");
    assert_eq!(
        boundary.fields.first().ok_or("missing type")?.value.value,
        "system"
    );
    Ok(())
}

#[test]
fn deployment_nodes_keep_orientation_and_ignore_sprite() {
    let model = resolved(
        "C4Deployment\nDeployment_Node(a, \"A\", \"Host\", \"Description\", \"ignored sprite\") {\nNode_L(b, \"B\") {\nNode_R(c, \"C\") {\nNode(d, \"D\") {\nPerson(p, \"P\")\n}\n}\n}\n}\n",
    );
    assert_eq!(
        model
            .boundaries
            .iter()
            .map(|boundary| boundary.node_type.as_str())
            .collect::<Vec<_>>(),
        ["node", "nodeL", "nodeR", "node"]
    );
    assert!(
        model
            .boundaries
            .iter()
            .all(|boundary| boundary.fields.iter().all(|field| field.name != "sprite")),
        "C4 deployment sprite arguments must remain absent from resolved fields; observed {:?}",
        model.boundaries
    );
}

#[test]
fn relation_macros_preserve_endpoints_and_update_ordered_pairs() -> Result<(), &'static str> {
    let model = resolved(
        "C4Dynamic\nRel(a, b, \"First\", \"HTTP\")\nBiRel(b, a, \"Both\")\nRel_Back(a, b, \"Back\")\nRelIndex(7, c, d, \"Indexed\")\nRel(a, \"b\")\n",
    );
    assert_eq!(model.elements.len(), 0);
    assert_eq!(model.relations.len(), 3);
    let relation = model.relations.first().ok_or("missing relation")?;
    assert_eq!(
        (
            &*relation.from.value,
            &*relation.to.value,
            &*relation.macro_name,
            &*relation.label.value
        ),
        ("a", "b", "Rel_Back", "Back")
    );
    assert_eq!(
        relation
            .fields
            .first()
            .ok_or("missing technology")?
            .value
            .value,
        "HTTP"
    );
    assert_eq!(
        model
            .relations
            .get(2)
            .ok_or("missing indexed relation")?
            .macro_name,
        "Rel"
    );
    Ok(())
}

#[test]
fn directional_macros_are_retained_without_geometry_changes() {
    for name in [
        "Rel_Up",
        "Rel_U",
        "Rel_Down",
        "Rel_D",
        "Rel_Left",
        "Rel_L",
        "Rel_Right",
        "Rel_R",
    ] {
        let model = resolved(&format!("C4Context\n{name}(a, b, \"Label\")\n"));
        assert_eq!(
            model
                .relations
                .first()
                .map(|relation| relation.macro_name.as_str()),
            Some(name)
        );
        assert_eq!(model.direction, "TB");
    }
}

#[test]
fn styles_target_existing_elements_before_boundaries() -> Result<(), &'static str> {
    let model = resolved(
        "C4Context\nUpdateElementStyle(a, \"ignored\")\nPerson(a, \"A\")\nBoundary(a, \"Boundary\") {\nPerson(b, \"B\")\n}\nUpdateElementStyle(a, \"red\", $techn=\"Metadata\")\nUpdateElementStyle(missing, \"ignored\")\n",
    );
    let element = model.elements.first().ok_or("missing element")?;
    assert_eq!(
        element
            .styles
            .iter()
            .map(|field| (field.name.as_str(), field.value.value.as_str()))
            .collect::<Vec<_>>(),
        [("bgColor", "red"), ("techn", "Metadata")]
    );
    assert_eq!(
        model
            .boundaries
            .first()
            .ok_or("missing boundary")?
            .styles
            .len(),
        0
    );
    assert_eq!(model.elements.len(), 2);
    Ok(())
}

#[test]
fn relationship_offsets_keep_leading_integers_and_invalid_metadata() -> Result<(), &'static str> {
    let model = resolved(
        "C4Context\nRel(a, b, \"Call\")\nUpdateRelStyle(a, b, \"red\", \"blue\", \"-12px\", \"unknown\")\nUpdateRelStyle(b, a, \"ignored\")\n",
    );
    let relation = model.relations.first().ok_or("missing relation")?;
    assert_eq!(
        relation
            .styles
            .iter()
            .map(|field| (field.name.as_str(), field.value.value.as_str()))
            .collect::<Vec<_>>(),
        [
            ("textColor", "red"),
            ("lineColor", "blue"),
            ("offsetX", "-12"),
            ("offsetY", "unknown")
        ]
    );
    Ok(())
}

#[test]
fn layout_hints_accept_only_positive_leading_decimal_integers() {
    let model = resolved(
        "C4Context\nUpdateLayoutConfig(\"3shapes\", \"2boundaries\")\nUpdateLayoutConfig(\"0\", \"invalid\")\nUpdateLayoutConfig($c4BoundaryInRow=\"5px\", $unused=\"9\")\n",
    );
    assert_eq!(
        model
            .layout_config
            .iter()
            .map(|field| (field.name.as_str(), field.value.value.as_str()))
            .collect::<Vec<_>>(),
        [("c4ShapeInRow", "3"), ("c4BoundaryInRow", "5")]
    );
}

#[test]
fn accessibility_forms_share_last_title_and_description() {
    let model = resolved(
        "C4Context\ntitle First\naccTitle: Last\naccDescription Old\naccDescr: Middle\naccDescr {\n Final description \n}\nPerson(a, \"A\")\n",
    );
    assert_eq!(model.acc_title, "Last");
    assert_eq!(model.acc_descr, "Final description");
    assert_eq!(model.accessibility.len(), 5);
}

#[test]
fn leading_integer_handles_signs_and_overflow_without_panicking() {
    assert_eq!(leading_integer(" +42px"), Some(42));
    assert_eq!(leading_integer("-7.5"), Some(-7));
    assert_eq!(leading_integer("no number"), None);
    assert_eq!(leading_integer("999999999999999999999999999999"), None);
}

#[test]
fn empty_optional_arguments_reset_text_and_extra_arguments_are_ignored() -> Result<(), &'static str>
{
    let model = resolved(
        "C4Context\nSystem(a, \"First\", \"Before\")\nSystem(a, \"Last\", \"\", \"sprite\", \"tags\", \"link\", $descr=\"ignored\")\n",
    );
    let element = model.elements.first().ok_or("missing system")?;
    let description = element
        .fields
        .iter()
        .find(|field| field.name == "descr")
        .ok_or("missing description")?;
    assert_eq!(description.value.value, "");
    assert_eq!(element.label.value, "Last");
    assert_eq!(element.attributes.len(), 7);
    Ok(())
}

#[test]
fn helper_named_types_and_boundary_styles_remain_metadata() -> Result<(), &'static str> {
    let model = resolved(
        "C4Context\nSystem_Boundary(g, \"Group\", $type=\"Custom\") {\nPerson(p, \"P\")\n}\nUpdateElementStyle(g, $shape=\"cloud\")\n",
    );
    let boundary = model.boundaries.first().ok_or("missing boundary")?;
    assert_eq!(
        boundary.fields.first().ok_or("missing type")?.value.value,
        "Custom"
    );
    assert_eq!(
        boundary.styles.first().ok_or("missing style")?.name,
        "shape"
    );
    assert_eq!(
        boundary.styles.first().ok_or("missing style")?.value.value,
        "cloud"
    );
    Ok(())
}

#[test]
fn named_label_override_does_not_outlive_a_later_required_label() -> Result<(), &'static str> {
    let model =
        resolved("C4Context\nPerson(p, \"First\", $label=\"Override\")\nPerson(p, \"Last\")\n");
    assert_eq!(
        model.elements.first().ok_or("missing person")?.label.value,
        "Last"
    );
    Ok(())
}
