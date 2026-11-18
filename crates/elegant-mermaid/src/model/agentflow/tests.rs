use super::*;

fn resolved(source: &str) -> (Model, Vec<Diagnostic>) {
    let preprocessed = crate::syntax::preprocess::preprocess(source);
    assert_eq!(preprocessed.diagnostics.len(), 0);
    let parsed = crate::syntax::agentflow::parse(source, &preprocessed.removed);
    assert_eq!(parsed.diagnostics.len(), 0, "{:?}", parsed.diagnostics);
    resolve(source, &parsed.document)
}
#[test]
fn labels_replace_without_reordering_and_bare_ids_keep_labels() -> Result<(), &'static str> {
    let (model, diagnostics) = resolved("agentflow-beta LR\nA --> B\nA[First]\nA[Last]\n");
    assert_eq!(diagnostics.len(), 0);
    assert_eq!(
        model
            .nodes
            .iter()
            .map(|n| (n.id.as_str(), n.label.as_str()))
            .collect::<Vec<_>>(),
        [("A", "Last"), ("B", "B")]
    );
    assert_eq!(model.direction, "LR");
    assert_eq!(model.nodes.first().ok_or("missing A")?.shape, "roundedRect");
    Ok(())
}
#[test]
fn cartesian_chains_keep_source_then_target_declaration_order() {
    let (model, diagnostics) = resolved("agentflow-beta\nA & B --> C & D --> E\n");
    assert_eq!(diagnostics.len(), 0);
    assert_eq!(
        model
            .edges
            .iter()
            .map(|e| (e.from.as_str(), e.to.as_str()))
            .collect::<Vec<_>>(),
        [
            ("A", "C"),
            ("A", "D"),
            ("B", "C"),
            ("B", "D"),
            ("C", "E"),
            ("D", "E")
        ]
    );
}
#[test]
fn named_edge_uses_last_source_first_target_and_reuse_gets_unique_id() {
    let (model, diagnostics) = resolved("agentflow-beta\nA & B link@--> C & D\nA link@--> D\n");
    assert_eq!(diagnostics.len(), 0);
    assert_eq!(
        model
            .edges
            .iter()
            .map(|e| e.id.as_str())
            .collect::<Vec<_>>(),
        ["e0", "e1", "link", "e3", "e4"]
    );
}
#[test]
fn aliases_normalize_and_metadata_label_type_and_unknown_fields_survive() -> Result<(), &'static str>
{
    let (model, diagnostics) = resolved(
        "agentflow-beta\nA@{ shape: task, label: 'Ready #38; set', labelType: markdown, icon: cloud, custom: [a, b] }\nB@{ shape: input }\nC@{ shape: tool }\n",
    );
    assert_eq!(diagnostics.len(), 0);
    assert_eq!(
        model
            .nodes
            .iter()
            .map(|n| n.shape.as_str())
            .collect::<Vec<_>>(),
        ["roundedRect", "lean-right", "subroutine"]
    );
    let node = model.nodes.first().ok_or("missing metadata node")?;
    assert_eq!(node.label, "Ready & set");
    assert_eq!(node.label_kind, TextKind::Markdown);
    assert!(
        node.appearance
            .metadata
            .iter()
            .any(|e| e.key == "custom" && matches!(e.value, ConfigValue::Sequence(_))),
        "node {:?} must keep the metadata key \"custom\" as a Sequence, keys present: {:?}",
        node.id,
        node.appearance
            .metadata
            .iter()
            .map(|e| &e.key)
            .collect::<Vec<_>>(),
    );
    Ok(())
}
#[test]
fn removed_bracket_shapes_have_exact_diagnostics() -> Result<(), &'static str> {
    let source = "agentflow-beta\nA((Circle))\n";
    let (model, diagnostics) = resolved(source);
    let diagnostic = diagnostics
        .first()
        .ok_or("missing removed-shape diagnostic")?;
    assert_eq!(diagnostic.code, "agentflow/shape-removed");
    assert_eq!(diagnostic.severity, Severity::Error);
    assert_eq!(
        diagnostic.message,
        "shape circle was removed; using roundedRect"
    );
    assert_eq!(
        source.get(diagnostic.span.start..diagnostic.span.end),
        Some("A((Circle))")
    );
    assert_eq!(
        model.nodes.first().ok_or("missing fallback node")?.shape,
        "roundedRect"
    );
    Ok(())
}
#[test]
fn invalid_metadata_shapes_report_value_not_key() -> Result<(), &'static str> {
    for shape in ["lean_right", "Missing", "missing", "true"] {
        let source = format!("agentflow-beta\nA@{{ shape: {shape} }}\n");
        let (_, diagnostics) = resolved(&source);
        let diagnostic = diagnostics
            .first()
            .ok_or("missing unknown-shape diagnostic")?;
        assert_eq!(diagnostic.code, "agentflow/shape-unknown");
        assert_eq!(diagnostic.message, format!("unknown shape {shape}"));
        assert_eq!(
            source.get(diagnostic.span.start..diagnostic.span.end),
            Some(shape)
        );
    }
    Ok(())
}
#[test]
fn flows_merge_members_and_global_nodes_release_old_ownership() -> Result<(), &'static str> {
    let (model, diagnostics) = resolved(
        "agentflow-beta\nflow F[First]\nA --> B\nend\nflow F[Last]\ndirection RL\nB --> C\nend\nglobal\nA --> D\nend\n",
    );
    assert_eq!(diagnostics.len(), 0);
    let flow = model.groups.first().ok_or("missing flow")?;
    assert_eq!(
        (&*flow.id, &*flow.title, &*flow.direction),
        ("F", "Last", "RL")
    );
    assert_eq!(flow.members, ["B", "C"]);
    assert_eq!(
        model
            .nodes
            .iter()
            .map(|n| (n.id.as_str(), n.parent.as_str()))
            .collect::<Vec<_>>(),
        [("A", ""), ("B", "F"), ("C", "F"), ("D", "")]
    );
    Ok(())
}
#[test]
fn connectors_are_nodes_and_reserved_connectors_id_is_omitted() -> Result<(), &'static str> {
    let (model, diagnostics) = resolved(
        "agentflow-beta\nconnector Port[Old]\nconnector Port[New] @{ custom: yes }\nconnectors\n",
    );
    assert_eq!(diagnostics.len(), 0);
    assert_eq!(model.nodes.len(), 1);
    let node = model.nodes.first().ok_or("missing connector")?;
    assert_eq!(
        (&*node.id, &*node.label, &*node.shape),
        ("Port", "New", "connector")
    );
    assert!(
        node.connector,
        "node {:?} declared under `connectors` must be a connector, shape is {:?}",
        node.id, node.shape,
    );
    Ok(())
}
#[test]
fn style_and_class_only_apply_to_existing_targets() -> Result<(), &'static str> {
    let (model, diagnostics) = resolved(
        "agentflow-beta\nclass Missing hot\nstyle Missing fill:red\nclassDef hot fill:blue,stroke:red\nA:::hot --> B\nstyle A stroke:black\nclass B hot\nlinkStyle 0 stroke:red\n",
    );
    assert_eq!(diagnostics.len(), 0);
    assert_eq!(model.nodes.len(), 2);
    assert_eq!(
        model.nodes.first().ok_or("missing A")?.appearance.styles,
        ["fill:blue", "stroke:red", "stroke:black"]
    );
    assert_eq!(
        model.edges.first().ok_or("missing edge")?.appearance.styles,
        ["stroke:red", "fill:none"]
    );
    Ok(())
}
#[test]
fn out_of_range_link_style_reports_index_span_and_current_bound() -> Result<(), &'static str> {
    let source = "agentflow-beta\nA --> B\nlinkStyle 2 stroke:red\n";
    let (_, diagnostics) = resolved(source);
    let diagnostic = diagnostics.first().ok_or("missing style diagnostic")?;
    assert_eq!(diagnostic.code, "agentflow/link-style-index");
    assert_eq!(diagnostic.message, "linkStyle index 2 is outside 0..0");
    assert_eq!(
        source.get(diagnostic.span.start..diagnostic.span.end),
        Some("2")
    );
    Ok(())
}
#[test]
fn clicks_retain_fields_and_accessibility_last_value_wins() -> Result<(), &'static str> {
    let (model, diagnostics) = resolved(
        "agentflow-beta\nA\nclick A href \"https://example.test\" \"Open\" _blank\naccTitle: first\naccTitle: last\naccDescr: detail\n",
    );
    assert_eq!(diagnostics.len(), 0);
    let link = model.links.first().ok_or("missing click")?;
    assert_eq!(link.url.as_deref(), Some("https://example.test"));
    assert_eq!(link.tooltip.as_deref(), Some("Open"));
    assert_eq!(link.target.as_deref(), Some("_blank"));
    assert_eq!((&*model.acc_title, &*model.acc_descr), ("last", "detail"));
    Ok(())
}
#[test]
fn collapse_redirects_hidden_endpoints_but_preserves_authored_self_loops() {
    let (model, diagnostics) = resolved(
        "agentflow-beta\nflow F[Fold] @{ view: collapsed }\nA --> B\nA --> A\nend\nB --> C\n",
    );
    assert_eq!(diagnostics.len(), 0);
    assert_eq!(
        model
            .nodes
            .iter()
            .map(|n| n.id.as_str())
            .collect::<Vec<_>>(),
        ["C"]
    );
    assert_eq!(
        model
            .edges
            .iter()
            .map(|e| (e.from.as_str(), e.to.as_str()))
            .collect::<Vec<_>>(),
        [("F", "F"), ("F", "C")]
    );
}
#[test]
fn containment_cycle_warns_and_retains_earlier_parent() -> Result<(), &'static str> {
    let (model, diagnostics) =
        resolved("agentflow-beta\nflow A\nflow B\nend\nend\nflow B\nA\nend\n");
    let diagnostic = diagnostics.first().ok_or("missing containment warning")?;
    assert_eq!(diagnostic.code, "agentflow/containment-violation");
    assert_eq!(diagnostic.severity, Severity::Warning);
    assert_eq!(
        diagnostic.message,
        "container B cannot contain A because it closes a containment cycle"
    );
    assert_eq!(model.groups.get(1).ok_or("missing B")?.parent, "A");
    Ok(())
}

#[test]
fn default_and_authored_directions_normalize_without_losing_tokens() {
    for (token, expected) in [
        ("", "TB"),
        ("TD", "TB"),
        ("v", "TB"),
        ("<", "RL"),
        (">", "LR"),
        ("^", "BT"),
        ("BR", "TB"),
    ] {
        let source = format!("agentflow-beta {token}\nA\n");
        let (model, diagnostics) = resolved(&source);
        assert_eq!(diagnostics.len(), 0);
        assert_eq!(model.direction, expected);
        assert_eq!(model.authored_direction, token);
    }
}

#[test]
fn reference_metadata_updates_named_edges_instead_of_creating_nodes() -> Result<(), &'static str> {
    let (model, diagnostics) =
        resolved("agentflow-beta\nA named@--> B\nnamed@{ label: changed, custom: retained }\n");
    assert_eq!(diagnostics.len(), 0);
    assert_eq!(model.nodes.len(), 2);
    let edge = model.edges.first().ok_or("missing named edge")?;
    assert_eq!((&*edge.id, &*edge.label), ("named", "changed"));
    assert!(
        edge.appearance
            .metadata
            .iter()
            .any(|entry| entry.key == "custom"),
        "named edge {:?} must keep its reference metadata key \"custom\"; keys present: {:?}",
        edge.id,
        edge.appearance
            .metadata
            .iter()
            .map(|e| &e.key)
            .collect::<Vec<_>>(),
    );
    Ok(())
}

#[test]
fn unsupported_registered_shape_warns_and_preserves_source_span() -> Result<(), &'static str> {
    let source = "agentflow-beta\nA@{ shape: cloud }\n";
    let (model, diagnostics) = resolved(source);
    let diagnostic = diagnostics
        .first()
        .ok_or("missing unsupported-shape warning")?;
    assert_eq!(diagnostic.code, "agentflow/shape-unsupported");
    assert_eq!(diagnostic.severity, Severity::Warning);
    assert_eq!(
        diagnostic.message,
        "shape cloud is not supported; using roundedRect"
    );
    assert_eq!(
        source.get(diagnostic.span.start..diagnostic.span.end),
        Some("cloud")
    );
    assert_eq!(
        model.nodes.first().ok_or("missing fallback")?.shape,
        "roundedRect"
    );
    Ok(())
}

#[test]
fn unknown_shape_after_newline_preserves_value_span() {
    for source in [
        "agentflow-beta\nA@{\n shape:\n  missing\n}\n",
        "agentflow-beta\r\nA@{\r\n shape:\r\n  missing\r\n}\r\n",
    ] {
        let (_, diagnostics) = resolved(source);
        assert_eq!(diagnostics.len(), 1);
        let diagnostic = &diagnostics[0];
        assert_eq!(diagnostic.code, "agentflow/shape-unknown");
        assert_eq!(
            source.get(diagnostic.span.start..diagnostic.span.end),
            Some("missing")
        );
    }
}

#[test]
fn malformed_metadata_reports_original_byte_span() -> Result<(), &'static str> {
    let value = " label: [one,, two] ";
    let data = ShapeData {
        span: Span {
            start: 10,
            end: 10 + value.len() + 3,
        },
        pieces: Vec::new(),
        value: value.into(),
    };
    let mut model = Model::default();
    assert_eq!(model.metadata(&[data]).len(), 0);
    let diagnostic = model
        .diagnostics
        .first()
        .ok_or("missing malformed metadata")?;
    let at = value.find(",,").ok_or("missing authored commas")? + 1;
    assert_eq!(diagnostic.code, "agentflow/metadata-malformed");
    assert_eq!(diagnostic.message, "invalid metadata value");
    assert_eq!(diagnostic.severity, Severity::Error);
    assert_eq!(
        diagnostic.span,
        Span {
            start: 12 + at,
            end: 13 + at
        }
    );
    Ok(())
}

#[test]
fn multiline_metadata_retries_line_trailing_commas() {
    let value = "\n label: \"first\",\n shape: \"task\",\n";
    let data = ShapeData {
        span: Span {
            start: 0,
            end: value.len() + 3,
        },
        pieces: Vec::new(),
        value: value.into(),
    };
    let (entries, error) = metadata_entries(&data);
    assert_eq!(error, None);
    assert_eq!(
        entries
            .iter()
            .map(|entry| (entry.key.as_str(), value_text(&entry.value)))
            .collect::<Vec<_>>(),
        [("label", "first".into()), ("shape", "task".into())]
    );
}

#[test]
fn first_container_owns_repeated_members_and_global_scope_releases_them() {
    let (model, diagnostics) = resolved("agentflow-beta\nflow F\nA\nend\nflow G\nA & B\nend\n");
    assert_eq!(diagnostics.len(), 0);
    assert_eq!(
        model
            .nodes
            .iter()
            .map(|node| (node.id.as_str(), node.parent.as_str()))
            .collect::<Vec<_>>(),
        [("A", "F"), ("B", "G")]
    );
}

#[test]
fn default_link_styles_apply_to_existing_and_future_edges() -> Result<(), &'static str> {
    let (model, diagnostics) = resolved(
        "agentflow-beta\nA ---> B\nlinkStyle default interpolate basis stroke:red\nB -..- C\n",
    );
    assert_eq!(diagnostics.len(), 0);
    assert_eq!(
        model
            .edges
            .iter()
            .map(|edge| (edge.length, edge.interpolation.as_str()))
            .collect::<Vec<_>>(),
        [(2, "basis"), (2, "basis")]
    );
    assert_eq!(
        model
            .edges
            .get(1)
            .ok_or("missing reference")?
            .appearance
            .styles,
        ["stroke:red"]
    );
    Ok(())
}

#[test]
fn prototype_keys_are_discarded_and_falsy_labels_do_not_replace_text() -> Result<(), &'static str> {
    let (model, diagnostics) =
        resolved("agentflow-beta\nA[Keep]@{ label: 0, __proto__: value, icon: cloud }\n");
    assert_eq!(diagnostics.len(), 0);
    let node = model.nodes.first().ok_or("missing node")?;
    assert_eq!(node.label, "Keep");
    assert_eq!(node.shape, "roundedRect");
    assert_eq!(
        node.appearance
            .metadata
            .iter()
            .map(|entry| entry.key.as_str())
            .collect::<Vec<_>>(),
        ["label", "icon"]
    );
    Ok(())
}

#[test]
fn unsafe_links_and_callbacks_use_shared_diagnostics_and_retain_interactions()
-> Result<(), &'static str> {
    let source = "agentflow-beta\nA\nclick A href \"javascript:bad\"\nclick A call handler(\"arg\") \"Run\"\n";
    let (model, diagnostics) = resolved(source);
    assert_eq!(model.links.len(), 2);
    assert_eq!(diagnostics.len(), 2);
    let unsafe_link = diagnostics.first().ok_or("missing unsafe URL")?;
    assert_eq!(unsafe_link.code, "interaction/unsafe-url");
    assert_eq!(unsafe_link.message, "link URL is not allowed");
    assert_eq!(unsafe_link.severity, Severity::Warning);
    assert_eq!(
        source.get(unsafe_link.span.start..unsafe_link.span.end),
        Some("\"javascript:bad\"")
    );
    let callback = diagnostics.get(1).ok_or("missing callback diagnostic")?;
    assert_eq!(callback.code, "interaction/callback-ignored");
    assert_eq!(callback.message, "callback handler is ignored");
    assert_eq!(callback.severity, Severity::Info);
    assert_eq!(
        model
            .links
            .get(1)
            .ok_or("missing callback")?
            .arguments
            .as_deref(),
        Some("\"arg\"")
    );
    Ok(())
}

#[test]
fn frontmatter_padding_keeps_set_zero_and_directives_take_precedence() {
    let source = "---\nconfig:\n  flowchart:\n    padding: 0\n---\nagentflow-beta\nA\n";
    let (model, diagnostics) = resolved(source);
    assert_eq!(diagnostics.len(), 0);
    assert_eq!(model.padding, Some(0));
}
