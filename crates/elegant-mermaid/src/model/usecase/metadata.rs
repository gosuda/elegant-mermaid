use super::*;
pub(super) fn apply_metadata(
    node: &mut Node,
    metadata: Option<&Metadata<'_>>,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let Some(metadata) = metadata else {
        return;
    };
    if node.kind == Kind::Json && metadata.properties.is_empty() {
        diagnostics.push(invalid_metadata(
            "metadata",
            "json",
            &node.id,
            metadata.span,
        ));
        return;
    }
    for property in &metadata.properties {
        let key = content(&property.key);
        let value = content(&property.value);
        if !set_metadata(node, key, value, property.value.kind) {
            diagnostics.push(invalid_metadata(
                key,
                node.kind.name(),
                &node.id,
                property.span,
            ));
            continue;
        }
        if let Some(field) = node.metadata.iter_mut().find(|(name, _)| name == key) {
            field.1 = value.into();
        } else {
            node.metadata.push((key.into(), value.into()));
        }
    }
}
fn set_metadata(node: &mut Node, key: &str, value: &str, token_kind: &str) -> bool {
    match (node.kind, key) {
        (Kind::Actor, "type") if matches!(value, "normal" | "hollow" | "awesome") => {
            node.actor_type = value.into()
        }
        (Kind::Actor, "icon") if !matches!(token_kind, "TRUE" | "FALSE") => {
            node.icon = value.into()
        }
        (Kind::Actor | Kind::Usecase, "business") if matches!(token_kind, "TRUE" | "FALSE") => {
            node.business = value == "true"
        }
        (Kind::Boundary, "type") if matches!(value, "rect" | "package") => {
            node.boundary_type = value.into()
        }
        _ => return false,
    }
    true
}
fn invalid_metadata(key: &str, kind: &str, id: &str, span: Span) -> Diagnostic {
    diagnostic(
        "usecase/invalid-metadata",
        format!("invalid metadata {key} for {kind} {id}"),
        span,
    )
}
pub(super) fn edge_metadata(
    edge: &mut Relation,
    property: &MetadataProperty<'_>,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let key = content(&property.key);
    let value = content(&property.value);
    match key {
        "animate" if matches!(property.value.kind, "TRUE" | "FALSE") => {
            edge.animate = value == "true"
        }
        "animation" if matches!(value, "fast" | "slow") => {
            edge.animation = value.into();
            edge.animate = true;
        }
        _ => diagnostics.push(invalid_metadata(key, "edge", &edge.id, property.span)),
    }
}
pub(super) fn validate_node(node: &Node, diagnostics: &mut Vec<Diagnostic>) {
    if node.kind == Kind::Usecase && node.shape == "rect" && node.business {
        diagnostics.push(diagnostic(
            "usecase/invalid-business-usecase",
            format!("rectangular use case {} cannot be business", node.id),
            node.span,
        ));
    }
    if node.kind != Kind::Actor {
        return;
    }
    let reason = if !node.icon.is_empty() && node.actor_type != "normal" {
        "icon cannot combine with hollow or awesome type"
    } else if node.business && node.actor_type == "awesome" {
        "business actor must use normal or hollow geometry"
    } else {
        return;
    };
    diagnostics.push(diagnostic(
        "usecase/invalid-actor",
        format!("invalid actor {}: {reason}", node.id),
        node.span,
    ));
}
