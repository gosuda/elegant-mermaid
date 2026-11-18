mod metadata;
mod resolve;

use metadata::validate_node;

use crate::{
    diag::{Diagnostic, Related},
    source::Span,
    syntax::usecase::{ast::*, diagnostic, lexer::Token},
};

#[derive(Debug, Clone, Default)]
pub struct Model {
    pub nodes: Vec<Node>,
    pub relations: Vec<Relation>,
    pub notes: Vec<Note>,
    pub definitions: Vec<(String, String)>,
    pub direction: String,
    pub acc_title: String,
    edge_symbols: Vec<(String, Span)>,
    pub acc_descr: String,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    Actor,
    Usecase,
    Boundary,
    Json,
}
impl Kind {
    fn name(self) -> &'static str {
        match self {
            Self::Actor => "actor",
            Self::Usecase => "usecase",
            Self::Boundary => "boundary",
            Self::Json => "json",
        }
    }
}
#[derive(Debug, Clone)]
pub struct Node {
    pub id: String,
    pub label: String,
    pub label_kind: LabelKind,
    pub kind: Kind,
    pub shape: String,
    pub parent: String,
    pub members: Vec<String>,
    pub stereotype: String,
    pub classes: Vec<String>,
    pub styles: Vec<String>,
    pub metadata: Vec<(String, String)>,
    pub actor_type: String,
    pub icon: String,
    pub business: bool,
    pub boundary_type: String,
    pub json: Option<Json>,
    pub span: Span,
    pub first_span: Span,
    pub generated: bool,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Json {
    Object(Vec<(String, Json)>),
    Array(Vec<Json>),
    Scalar(String),
}
#[derive(Debug, Clone)]
pub struct Relation {
    pub id: String,
    pub explicit: bool,
    pub from: String,
    pub to: String,
    pub kind: String,
    pub label: String,
    pub marker_start: String,
    pub marker_end: String,
    pub min_length: usize,
    pub animate: bool,
    pub animation: String,
    pub span: Span,
    pub classes: Vec<String>,
    pub styles: Vec<String>,
}
#[derive(Debug, Clone)]
pub struct Note {
    pub id: String,
    pub target: String,
    pub text: String,
    pub span: Span,
}

pub fn resolve(source: &str, document: &Start<'_>) -> (Model, Vec<Diagnostic>) {
    let statements = document
        .lines
        .iter()
        .filter_map(|line| match &line.kind {
            LineKind::Statement(statement) => Some(statement.as_ref()),
            _ => None,
        })
        .collect::<Vec<_>>();
    let mut model = Model {
        direction: "TB".into(),
        ..Model::default()
    };
    let mut diagnostics = Vec::new();
    for statement in &statements {
        model.collect(statement, &mut diagnostics);
    }
    for statement in &statements {
        model.reserve_edge(statement, &mut diagnostics);
    }
    for statement in &statements {
        model.connect(statement, &mut diagnostics);
    }
    for statement in &statements {
        model.configure(source, statement, &mut diagnostics);
    }
    for node in &model.nodes {
        validate_node(node, &mut diagnostics);
    }
    for relation in &model.relations {
        model.validate_relation(relation, &mut diagnostics);
    }
    model.nodes.sort_by_key(|node| node.first_span.start);
    diagnostics.sort_by(|a, b| (a.span.start, a.code).cmp(&(b.span.start, b.code)));
    (model, diagnostics)
}

fn conflict(id: &str, reason: &str, later: Span, earlier: Span) -> Diagnostic {
    let mut diagnostic = diagnostic(
        "usecase/declaration-conflict",
        format!("conflicting declaration of {id}: {reason}"),
        later,
    );
    diagnostic.related.push(Related {
        span: earlier,
        message: "first declared here".into(),
    });
    diagnostic
}
fn unresolved(kind: &str, id: &str, span: Span) -> Diagnostic {
    diagnostic(
        "usecase/unresolved-target",
        format!("unresolved {kind} target {id}"),
        span,
    )
}
fn content<'t>(token: &'t Token<'_>) -> &'t str {
    match token.kind {
        "PLAIN_STRING" => token
            .text
            .get(1..token.text.len().saturating_sub(1))
            .unwrap_or(""),
        "MARKDOWN_STRING" => token
            .text
            .get(2..token.text.len().saturating_sub(2))
            .unwrap_or(""),
        _ => token.text.as_ref(),
    }
}
fn identity(token: &Token<'_>) -> String {
    let text = content(token);
    if matches!(token.kind, "PLAIN_STRING" | "MARKDOWN_STRING") {
        text.chars()
            .map(|c| {
                if c.is_ascii_alphanumeric() || c == '_' {
                    c
                } else {
                    '_'
                }
            })
            .collect()
    } else {
        text.into()
    }
}
fn classes(suffix: Option<&ClassSuffix<'_>>) -> Vec<String> {
    let mut result = Vec::new();
    if let Some(suffix) = suffix {
        append_unique(
            &mut result,
            suffix.classes.iter().map(|token| token.text.to_string()),
        );
    }
    result
}
fn append_unique(target: &mut Vec<String>, values: impl IntoIterator<Item = String>) {
    for value in values {
        if !target.contains(&value) {
            target.push(value);
        }
    }
}
fn node(token: &Token<'_>, label: Option<&NodeLabel<'_>>, kind: Kind, span: Span) -> Node {
    let generated = matches!(token.kind, "PLAIN_STRING" | "MARKDOWN_STRING");
    let label_kind = label.map_or_else(
        || match token.kind {
            "PLAIN_STRING" => LabelKind::Quoted,
            "MARKDOWN_STRING" => LabelKind::Markdown,
            _ => LabelKind::Plain,
        },
        |label| label.kind,
    );
    Node {
        id: identity(token),
        label: label.map_or_else(|| content(token).into(), |label| label.text.as_ref().into()),
        label_kind,
        kind,
        shape: "usecaseEllipse".into(),
        parent: String::new(),
        members: Vec::new(),
        stereotype: String::new(),
        classes: Vec::new(),
        styles: Vec::new(),
        metadata: Vec::new(),
        actor_type: "normal".into(),
        icon: String::new(),
        business: false,
        boundary_type: "rect".into(),
        json: None,
        span,
        first_span: span,
        generated,
    }
}
fn entity(name: &EntityName<'_>, parent: &str) -> Node {
    let mut node = node(&name.id, name.label.as_ref(), Kind::Usecase, name.span);
    if name
        .delimiters
        .as_ref()
        .is_some_and(|(open, _)| open.text == "[")
    {
        node.shape = "rect".into();
    }
    node.parent = parent.into();
    node.classes = classes(name.classes.as_ref());
    node.stereotype = name
        .stereotype
        .as_ref()
        .map_or("", |value| value.content.text.trim())
        .into();
    node
}
fn explicit(name: &EntityName<'_>) -> bool {
    name.label.is_some()
        || matches!(name.id.kind, "PLAIN_STRING" | "MARKDOWN_STRING")
        || name.metadata.is_some()
        || name.stereotype.is_some()
}
fn declaration_difference(a: &Node, b: &Node) -> Option<&'static str> {
    if a.generated || b.generated {
        return Some("duplicate generated id");
    }
    if a.kind != b.kind {
        return Some("different kind");
    }
    if a.kind == Kind::Json {
        return Some("duplicate JSON id");
    }
    if a.label != b.label || a.label_kind != b.label_kind {
        return Some("different label");
    }
    if a.shape != b.shape {
        return Some("different shape");
    }
    if a.parent != b.parent {
        return Some("different parent boundary");
    }
    if a.stereotype != b.stereotype {
        return Some("different stereotype");
    }
    if !same_metadata(&a.metadata, &b.metadata) {
        return Some("different metadata");
    }
    None
}
fn same_metadata(a: &[(String, String)], b: &[(String, String)]) -> bool {
    a.len() == b.len() && a.iter().all(|field| b.contains(field))
}
fn boundary_members(members: &mut Vec<String>, element: &BoundaryElementKind<'_>) {
    match element {
        BoundaryElementKind::Actor(value) => append_unique(
            members,
            value.items.iter().map(|item| identity(&item.name.id)),
        ),
        BoundaryElementKind::Entity(name, _) => append_unique(members, [identity(&name.id)]),
        _ => {}
    }
}
fn arrow(edge: &mut Relation, arrow: &ArrowKind<'_>) {
    match arrow {
        ArrowKind::Semantic(value) => semantic_arrow(edge, value),
        ArrowKind::ForwardSolid(value) => solid(edge, &value.token.text, "point"),
        ArrowKind::BackwardSolid(value) => {
            edge.marker_start = "point".into();
            solid(edge, &value.token.text, "none");
            if let Some(right) = &value.right {
                edge.min_length = edge.min_length.max(solid_min_length(&right.text));
            }
            edge.label = edge_label(value.label.as_ref());
        }
        ArrowKind::MarkerlessSolid(value) => {
            let right = value
                .right
                .as_ref()
                .map_or(value.token.text.as_ref(), |token| token.text.as_ref());
            solid(edge, right, association_marker(right));
            edge.label = edge_label(value.label.as_ref());
        }
        ArrowKind::ForwardCircle(_) => edge.marker_end = "circle".into(),
        ArrowKind::ForwardCross(_) => edge.marker_end = "cross".into(),
        ArrowKind::BackwardCircle(value) => {
            edge.marker_start = "circle".into();
            edge.label = edge_label(value.label.as_ref());
        }
        ArrowKind::BackwardCross(value) => {
            edge.marker_start = "cross".into();
            edge.label = edge_label(value.label.as_ref());
        }
    }
}
fn semantic_arrow(edge: &mut Relation, value: &SemanticRelation<'_>) {
    if let Some(relation) = &value.relation {
        edge.kind = relation.text.to_ascii_lowercase();
        edge.label = format!("«{}»", edge.kind);
        edge.marker_end = "point".into();
    } else {
        edge.kind = "generalization".into();
        edge.marker_end = "extension".into();
    }
}
fn association_marker(operator: &str) -> &'static str {
    match operator.chars().last() {
        Some('>') => "point",
        Some('o') => "circle",
        Some('x') => "cross",
        _ => "none",
    }
}
fn solid(edge: &mut Relation, operator: &str, marker: &str) {
    edge.marker_end = marker.into();
    edge.min_length = solid_min_length(operator);
    if matches!(marker, "circle" | "cross") {
        edge.min_length = 1;
    }
}
fn solid_min_length(operator: &str) -> usize {
    operator
        .bytes()
        .filter(|byte| *byte == b'-')
        .count()
        .saturating_sub(1)
        .max(1)
}
fn edge_label(label: Option<&EdgeLabel<'_>>) -> String {
    label.map_or("", |value| value.label.text.as_ref()).into()
}
fn relationship_error(
    edge: &Relation,
    from: Option<&Node>,
    to: Option<&Node>,
) -> Option<&'static str> {
    let (Some(from), Some(to)) = (from, to) else {
        return Some("edge symbols cannot be endpoints");
    };
    let kinds = (from.kind, to.kind);
    if matches!(kinds, (Kind::Boundary, _) | (_, Kind::Boundary)) {
        return Some("boundaries cannot be endpoints");
    }
    match edge.kind.as_str() {
        "include" | "extend" => {
            (kinds != (Kind::Usecase, Kind::Usecase)).then_some("both endpoints must be use cases")
        }
        "generalization" => (!matches!(
            kinds,
            (Kind::Actor, Kind::Actor) | (Kind::Usecase, Kind::Usecase)
        ))
        .then_some("both endpoints must be actors or both use cases"),
        _ if matches!(kinds, (Kind::Json, _) | (_, Kind::Json)) => {
            [edge.marker_start.as_str(), edge.marker_end.as_str()]
                .into_iter()
                .any(|marker| !matches!(marker, "none" | "point"))
                .then_some("JSON endpoints require a solid point or markerless association")
        }
        _ => None,
    }
}
fn json_object(object: &JsonObject<'_>) -> Json {
    Json::Object(
        object
            .properties
            .iter()
            .map(|property| {
                (
                    property.key.text.as_ref().into(),
                    json_value(&property.value),
                )
            })
            .collect(),
    )
}
fn json_value(value: &JsonValue<'_>) -> Json {
    match &value.kind {
        JsonValueKind::Object(object) => json_object(object),
        JsonValueKind::Array(values) => Json::Array(values.iter().map(json_value).collect()),
        JsonValueKind::Scalar(token) => Json::Scalar(token.text.as_ref().into()),
    }
}

#[cfg(test)]
mod tests;
