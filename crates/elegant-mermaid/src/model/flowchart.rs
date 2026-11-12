use crate::diag::Diagnostic;
use crate::source::Span;
use crate::syntax::flowchart::ast::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node {
    pub id: String,
    pub label: String,
    pub shape: String,
    pub classes: Vec<String>,
    pub styles: Vec<String>,
    pub first: Span,
    pub span: Span,
    pub attrs: std::collections::BTreeMap<String, String>,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Edge {
    pub from: String,
    pub to: String,
    pub label: Option<String>,
    pub stroke: String,
    pub marker: String,
    pub start: String,
    pub length: usize,
    pub user_id: String,
    pub span: Span,
    pub attrs: std::collections::BTreeMap<String, String>,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Group {
    pub id: String,
    pub title: String,
    pub parent: String,
    pub direction: String,
    pub members: Vec<String>,
    pub span: Span,
    pub view: String,
}
#[derive(Debug)]
pub struct Model {
    pub direction: String,
    pub direction_span: Span,
    pub nodes: Vec<Node>,
    pub edges: Vec<Edge>,
    pub groups: Vec<Group>,
    pub class_defs: Vec<ClassDefStatement>,
    pub link_styles: Vec<LinkStyleStatement>,
    pub clicks: Vec<ClickStatement>,
    pub acc_title: String,
    pub acc_descr: String,
    diagnostics: Vec<Diagnostic>,
}

impl Default for Node {
    fn default() -> Self {
        Self {
            id: String::new(),
            label: String::new(),
            shape: String::new(),
            classes: Vec::new(),
            styles: Vec::new(),
            first: Span { start: 0, end: 0 },
            span: Span { start: 0, end: 0 },
            attrs: std::collections::BTreeMap::new(),
        }
    }
}
impl Default for Group {
    fn default() -> Self {
        Self {
            id: String::new(),
            title: String::new(),
            parent: String::new(),
            direction: String::new(),
            members: Vec::new(),
            span: Span { start: 0, end: 0 },
            view: String::new(),
        }
    }
}
impl Default for Model {
    fn default() -> Self {
        Self {
            direction: String::new(),
            direction_span: Span { start: 0, end: 0 },
            nodes: Vec::new(),
            edges: Vec::new(),
            groups: Vec::new(),
            class_defs: Vec::new(),
            link_styles: Vec::new(),
            clicks: Vec::new(),
            acc_title: String::new(),
            acc_descr: String::new(),
            diagnostics: Vec::new(),
        }
    }
}

pub fn resolve(source: &str, document: &Document) -> (Model, Vec<Diagnostic>) {
    let mut model = Model {
        direction: "TB".into(),
        ..Model::default()
    };
    if let Some(span) = document.config.direction {
        model.direction = direction(&source[span.start..span.end]).into();
        model.direction_span = span;
    }
    walk(source, &document.lines, &mut model, "");
    let mut diagnostics = link_style_diagnostics(source, &model);
    diagnostics.append(&mut model.diagnostics);
    crate::diag::sort(&mut diagnostics);
    (model, diagnostics)
}

fn link_style_diagnostics(source: &str, model: &Model) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for style in &model.link_styles {
        let LinkSelector::NumList(list) = &style.selector else {
            continue;
        };
        diagnostics.extend(list.numbers.iter().filter_map(|span| {
            let number = source[span.start..span.end].parse::<usize>().ok()?;
            (number >= model.edges.len()).then(|| {
                crate::syntax::flowchart::diagnostic(
                    "flowchart/linkstyle-id-unknown",
                    crate::diag::Severity::Error,
                    "linkStyle references an edge id that no link defines".into(),
                    *span,
                )
            })
        }));
    }
    diagnostics
}

fn direction(text: &str) -> &str {
    match text.trim() {
        "BT" | "^" => "BT",
        "LR" | ">" => "LR",
        "RL" | "<" => "RL",
        _ => "TB",
    }
}

fn walk(source: &str, lines: &[Line], model: &mut Model, parent: &str) {
    for line in lines {
        match &line.kind {
            Statement::Vertex(value) => vertices(source, value, model, parent),
            Statement::Subgraph(value) => subgraph(source, value, model, parent),
            Statement::Style(value) => apply_style(value, model),
            Statement::Class(value) => apply_class(value, model),
            Statement::ClassDef(value) => model.class_defs.push(value.clone()),
            Statement::LinkStyle(value) => model.link_styles.push(value.clone()),
            Statement::Click(value) => model.clicks.push(value.clone()),
            Statement::AccTitle(value) => {
                model.acc_title = source[value.value.start..value.value.end].trim().into()
            }
            Statement::AccDescr(value) => {
                model.acc_descr = source[value.value.start..value.value.end].trim().into()
            }
            Statement::AccDescrBlock(value) => {
                model.acc_descr = source[value.value.start..value.value.end].trim().into()
            }
            Statement::Direction(value) => {
                if let Some(group) = model.groups.iter_mut().find(|group| group.id == parent) {
                    group.direction = direction(
                        source[value.span.start..value.span.end].trim_start_matches("direction"),
                    )
                    .into();
                }
            }
        }
    }
}

fn node_index(model: &mut Model, id: &str, span: Span) -> usize {
    if let Some(index) = model.nodes.iter().position(|node| node.id == id) {
        return index;
    }
    model.nodes.push(Node {
        id: id.into(),
        shape: "squareRect".into(),
        first: span,
        span,
        ..Node::default()
    });
    model.nodes.len() - 1
}

fn group_nodes(group: &NodeGroup, model: &mut Model, parent: &str) -> Vec<String> {
    group
        .nodes
        .iter()
        .map(|styled| {
            let vertex = &styled.vertex;
            if reference_data(model, styled) {
                return vertex.id.text.clone();
            }
            let index = node_index(model, &vertex.id.text, vertex.id.span);
            let node = &mut model.nodes[index];
            node.span = styled.span;
            if let Some(label) = &vertex.label {
                node.label = resolve_label(&label.text.text);
                node.shape = shape(&label.form).into();
            }
            if let Some(class) = &styled.class {
                node.classes.push(class.text.clone());
            }
            if let Some(data) = &styled.shape_data {
                model.diagnostics.extend(apply_shape_data(node, data));
            }
            join_group(model, &vertex.id.text, parent);
            vertex.id.text.clone()
        })
        .collect()
}

fn join_group(model: &mut Model, id: &str, parent: &str) {
    if model
        .groups
        .iter()
        .any(|group| group.members.iter().any(|member| member == id))
    {
        return;
    }
    if let Some(group) = model.groups.iter_mut().find(|group| group.id == parent) {
        group.members.push(id.into());
    }
}

fn vertices(source: &str, value: &VertexStatement, model: &mut Model, parent: &str) {
    let mut previous = group_nodes(&value.first, model, parent);
    for (link, group) in &value.rest {
        let next = group_nodes(group, model, parent);
        if let (Some(from), Some(to)) = (previous.last(), next.first()) {
            model.edges.push(edge(source, link, from, to));
        }
        previous = next;
    }
}

fn edge(source: &str, link: &Link, from: &str, to: &str) -> Edge {
    let body = source[link.statement.end.start..link.statement.end.end].trim();
    let stroke = stroke_of(body);
    let (start_marker, end_marker) = edge_markers(source, link, body);
    let count = body
        .bytes()
        .filter(|byte| matches!(byte, b'-' | b'=' | b'.'))
        .count();
    Edge {
        from: from.into(),
        to: to.into(),
        label: link
            .arrow_text
            .as_ref()
            .map(|text| resolve_label(&text.text.text))
            .or_else(|| {
                link.edge_text
                    .as_ref()
                    .map(|text| resolve_label(&text.text))
            }),
        stroke: stroke.into(),
        marker: end_marker.into(),
        start: start_marker.into(),
        length: count.saturating_sub(1).min(10),
        user_id: link
            .statement
            .link_id
            .map(|span| source[span.start..span.end].into())
            .unwrap_or_default(),
        span: link.span,
        attrs: std::collections::BTreeMap::new(),
    }
}

fn stroke_of(body: &str) -> &'static str {
    if body.contains('~') {
        "invisible"
    } else if body.contains('=') {
        "thick"
    } else if body.contains('.') {
        "dotted"
    } else {
        "normal"
    }
}

fn edge_markers(source: &str, link: &Link, end: &str) -> (&'static str, &'static str) {
    let end_marker = marker(end.chars().last());
    let Some(span) = link.statement.start else {
        return ("", end_marker);
    };
    let start = source[span.start..span.end].trim();
    let start_marker = marker(start.chars().next());
    if stroke_of(start) != stroke_of(end) || start_marker != end_marker && !start.starts_with('<') {
        return ("", "none");
    }
    (start_marker, end_marker)
}
fn marker(value: Option<char>) -> &'static str {
    match value {
        Some('<' | '>') => "point",
        Some('x') => "cross",
        Some('o') => "circle",
        _ => "none",
    }
}

fn resolve_label(text: &str) -> String {
    let trimmed = text.trim();
    let text = trimmed
        .strip_prefix('"')
        .and_then(|text| text.strip_suffix('"'))
        .unwrap_or(trimmed);
    let mut output = String::with_capacity(text.len());
    let mut cursor = 0;
    while cursor < text.len() {
        let tail = &text[cursor..];
        if let Some((end, decoded)) = decode_entity(tail) {
            output.push_str(&decoded);
            cursor += end;
        } else if let Some(value) = tail.chars().next() {
            output.push(value);
            cursor += value.len_utf8();
        }
    }
    output
}

fn decode_entity(text: &str) -> Option<(usize, String)> {
    let tail = text.strip_prefix('#')?;
    let end = tail.find(';')?;
    let name = &tail[..end];
    if name.is_empty()
        || !name
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
    {
        return None;
    }
    if let Some(value) = name
        .parse::<u32>()
        .ok()
        .filter(|value| *value != 0)
        .and_then(char::from_u32)
    {
        return Some((end + 2, value.to_string()));
    }
    let key = format!("&{name};");
    let row = crate::r#gen::entities::ENTITIES
        .iter()
        .find(|row| row.name == key)?;
    Some((
        end + 2,
        row.cps
            .iter()
            .filter_map(|value| char::from_u32(*value))
            .collect(),
    ))
}
fn shape(form: &LabelForm) -> &'static str {
    match form {
        LabelForm::Square => "squareRect",
        LabelForm::Round => "roundedRect",
        LabelForm::Round2 => "circle",
        LabelForm::Circle => "doublecircle",
        LabelForm::Ellipse => "ellipse",
        LabelForm::Stadium => "stadium",
        LabelForm::Subroutine => "subroutine",
        LabelForm::RectProps { .. } => "rect",
        LabelForm::Cylinder => "cylinder",
        LabelForm::Diamond => "diamond",
        LabelForm::Diamond2 => "hexagon",
        LabelForm::Odd => "odd",
        LabelForm::Trap {
            closer: TrapCloser::Trap,
        } => "trapezoid",
        LabelForm::Trap { .. } => "lean_right",
        LabelForm::InvTrap {
            closer: TrapCloser::InvTrap,
        } => "inv_trapezoid",
        LabelForm::InvTrap { .. } => "lean_left",
    }
}
fn subgraph(source: &str, value: &Subgraph, model: &mut Model, parent: &str) {
    let id = value
        .id
        .as_ref()
        .map(|id| id.text.trim().to_owned())
        .unwrap_or_else(|| format!("subGraph{}", model.groups.len()));
    let title = value
        .title
        .as_ref()
        .map(|title| title.text.clone())
        .unwrap_or_else(|| {
            value
                .id
                .as_ref()
                .map(|id| id.text.clone())
                .unwrap_or_default()
        });
    if !model.groups.iter().any(|group| group.id == id) {
        model.groups.push(Group {
            id: id.clone(),
            title,
            parent: parent.into(),
            span: value.span,
            ..Group::default()
        });
    }
    walk(source, &value.body, model, &id);
}
fn apply_style(value: &StyleStatement, model: &mut Model) {
    for id in value.target.text.split(',').map(str::trim) {
        let index = node_index(model, id, value.target.span);
        model.nodes[index]
            .styles
            .extend(value.styles.styles.iter().cloned());
    }
}
fn apply_class(value: &ClassStatement, model: &mut Model) {
    for id in value.targets.text.split(',').map(str::trim) {
        let index = node_index(model, id, value.targets.span);
        model.nodes[index]
            .classes
            .push(value.class_name.text.clone());
    }
}

fn apply_shape_data(node: &mut Node, data: &ShapeData) -> Vec<Diagnostic> {
    let (entries, mut diagnostics) = shape_entries(data);
    if !diagnostics.is_empty() {
        return diagnostics;
    }
    for entry in entries {
        let value = config_text(entry.value);
        if entry.key == "shape" {
            if let Some(shape) = shape_id(&value) {
                node.shape = shape.into();
            } else {
                diagnostics.push(crate::syntax::flowchart::diagnostic(
                    "flowchart/typed-shape-unsupported",
                    crate::diag::Severity::Error,
                    "A typed shape in an @{ shape: ... } node is not supported".into(),
                    Span {
                        start: entry.key_span.start,
                        end: entry.key_span.end,
                    },
                ));
            }
        }
        node.attrs.insert(entry.key, value);
    }
    finish_shape_data(node);
    diagnostics
}

fn shape_entries(data: &ShapeData) -> (Vec<crate::syntax::config_value::Entry>, Vec<Diagnostic>) {
    use crate::syntax::config_value::{ConfigValue, parse_config_yaml};
    let wrapped = !data.text.contains(['\r', '\n']);
    let input = if wrapped {
        format!("{{{}}}", data.text)
    } else {
        data.text.clone()
    };
    let (value, mut diagnostics) = parse_config_yaml(&input, 0, input.len());
    let offset = data.span.start + 2;
    for diagnostic in &mut diagnostics {
        diagnostic.span = map_shape_span(data, diagnostic.span, offset, usize::from(wrapped));
    }
    let ConfigValue::Mapping(mut entries) = value else {
        return (Vec::new(), diagnostics);
    };
    for entry in &mut entries {
        entry.key_span = map_shape_span(data, entry.key_span, offset, usize::from(wrapped));
    }
    (entries, diagnostics)
}

fn map_shape_span(data: &ShapeData, span: Span, offset: usize, prefix: usize) -> Span {
    Span {
        start: (offset + span.start.saturating_sub(prefix)).min(data.span.end),
        end: (offset + span.end.saturating_sub(prefix)).min(data.span.end),
    }
}

fn reference_data(model: &mut Model, styled: &StyledVertex) -> bool {
    let id = &styled.vertex.id.text;
    let edge = model
        .edges
        .iter()
        .position(|edge| edge.user_id.trim_end_matches('@') == id);
    let group = model.groups.iter().position(|group| group.id == *id);
    if edge.is_none() && group.is_none() {
        return false;
    }
    let Some(data) = &styled.shape_data else {
        return false;
    };
    let (entries, diagnostics) = shape_entries(data);
    model.diagnostics.extend(diagnostics);
    for entry in entries {
        if let Some(index) = edge {
            if matches!(
                entry.key.as_str(),
                "curve" | "animate" | "animation" | "step"
            ) {
                model.edges[index]
                    .attrs
                    .insert(entry.key, config_text(entry.value));
            }
        } else if entry.key == "view"
            && let Some(index) = group
        {
            model.groups[index].view = config_text(entry.value);
        }
    }
    true
}

fn config_text(value: crate::syntax::config_value::ConfigValue) -> String {
    use crate::syntax::config_value::ConfigValue;
    match value {
        ConfigValue::String(value) | ConfigValue::Integer(value) | ConfigValue::Decimal(value) => {
            value
        }
        ConfigValue::Bool(value) => value.to_string(),
        _ => String::new(),
    }
}

fn shape_id(value: &str) -> Option<&'static str> {
    if value.is_empty()
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_lowercase() || byte.is_ascii_digit() || byte == b'-')
    {
        return None;
    }
    const BUILTINS: &[(&str, &str)] = &[
        ("stadium", "stadium"),
        ("subroutine", "subroutine"),
        ("cylinder", "cylinder"),
        ("circle", "circle"),
        ("doublecircle", "doublecircle"),
        ("diamond", "diamond"),
        ("hexagon", "hexagon"),
        ("odd", "odd"),
        ("trapezoid", "trapezoid"),
        ("inv-trapezoid", "inv_trapezoid"),
        ("lean-right", "lean_right"),
        ("lean-left", "lean_left"),
        ("ellipse", "ellipse"),
    ];
    crate::r#gen::shapes::SHAPES
        .iter()
        .find(|shape| shape.id == value || shape.aliases.contains(&value))
        .map(|shape| shape.id)
        .or_else(|| {
            BUILTINS
                .iter()
                .find(|(name, _)| *name == value)
                .map(|(_, id)| *id)
        })
}

fn finish_shape_data(node: &mut Node) {
    if let Some(label) = node.attrs.get("label") {
        node.label = resolve_label(label);
    }
    if node.attrs.get("img").is_some_and(|image| !image.is_empty()) {
        node.shape = "imageSquare".into();
    }
    if node.attrs.contains_key("icon") {
        node.shape = match node.attrs.get("form").map(String::as_str) {
            Some("circle") => "iconCircle",
            Some("square") => "iconSquare",
            Some("rounded") => "iconRounded",
            _ => "icon",
        }
        .into();
    }
}
