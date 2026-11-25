use crate::diag::Diagnostic;
use crate::source::Span;
use crate::syntax::flowchart::ast::*;
use crate::syntax::flowchart::tokens::TokenKind;

mod interaction;
pub use interaction::ClickLink;
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Decl {
    pub span: Span,
    pub label: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node {
    pub id: String,
    pub label: String,
    pub label_kind: Option<TextKind>,
    pub shape: String,
    pub classes: Vec<String>,
    pub styles: Vec<String>,
    pub first: Span,
    pub span: Span,
    pub attrs: std::collections::BTreeMap<String, String>,
    pub decls: Vec<Decl>,
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
    /// The enclosing vertex statement; `span` retains the link-token provenance.
    pub statement_span: Span,
    pub attrs: std::collections::BTreeMap<String, String>,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Group {
    pub id: String,
    pub title: String,
    pub parent: String,
    pub direction: String,
    pub direction_span: Span,
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
    pub links: Vec<ClickLink>,
    pub acc_title: String,
    pub acc_descr: String,
    diagnostics: Vec<Diagnostic>,
    member_owners: std::collections::BTreeMap<String, String>,
    subgraph_count: usize,
    /// The id-token spans of node occurrences named like an enclosing subgraph.
    pub subgraph_collisions: Vec<Span>,
    pub unquoted_at_spans: Vec<Span>,
}

impl Default for Node {
    fn default() -> Self {
        Self {
            id: String::new(),
            label: String::new(),
            label_kind: None,
            shape: String::new(),
            classes: Vec::new(),
            styles: Vec::new(),
            first: Span { start: 0, end: 0 },
            span: Span { start: 0, end: 0 },
            attrs: std::collections::BTreeMap::new(),
            decls: Vec::new(),
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
            direction_span: Span { start: 0, end: 0 },
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
            links: Vec::new(),
            acc_title: String::new(),
            acc_descr: String::new(),
            diagnostics: Vec::new(),
            member_owners: std::collections::BTreeMap::new(),
            subgraph_count: 0,
            subgraph_collisions: Vec::new(),
            unquoted_at_spans: Vec::new(),
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
    model.member_owners.clear();
    let mut diagnostics = link_style_diagnostics(source, &model);
    diagnostics.extend(interaction::resolve(source, &mut model));
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
            Statement::AccTitle(value) => model.acc_title = value.text.trim().into(),
            Statement::AccDescr(value) => model.acc_descr = value.text.trim().into(),
            Statement::AccDescrBlock(value) => model.acc_descr = value.text.trim().into(),
            Statement::Direction(value) => {
                if let Some(group) = model.groups.iter_mut().find(|group| group.id == parent) {
                    group.direction = direction(
                        source[value.span.start..value.span.end]
                            .trim()
                            .trim_start_matches("direction"),
                    )
                    .into();
                    group.direction_span = value.span;
                }
            }
        }
    }
}

fn node_index(model: &mut Model, id: &str, span: Span, label: Option<&str>) -> usize {
    let decl = Decl {
        span,
        label: label.map(str::to_owned),
    };
    if let Some(index) = model.nodes.iter().position(|node| node.id == id) {
        model.nodes[index].decls.push(decl);
        return index;
    }
    model.nodes.push(Node {
        id: id.into(),
        shape: "squareRect".into(),
        first: span,
        span,
        decls: vec![decl],
        ..Node::default()
    });
    model.nodes.len() - 1
}

fn group_nodes(source: &str, group: &NodeGroup, model: &mut Model, parent: &str) -> Vec<String> {
    group
        .nodes
        .iter()
        .map(|styled| {
            let vertex = &styled.vertex;
            if let Some(span) = unquoted_at(source, vertex) {
                model.unquoted_at_spans.push(span);
            }
            if subgraph_scoped(model, parent, &vertex.id.text) {
                model.subgraph_collisions.push(vertex.id.span);
            }
            if reference_data(model, styled) {
                return vertex.id.text.clone();
            }
            let index = node_index(
                model,
                &vertex.id.text,
                vertex.id.span,
                vertex
                    .label
                    .as_ref()
                    .map(|label| resolve_label(&label.text.text))
                    .as_deref(),
            );
            let node = &mut model.nodes[index];
            node.span = styled.span;
            if let Some(label) = &vertex.label {
                node.label = resolve_label(&label.text.text);
                node.label_kind = Some(label.text.kind);
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

fn unquoted_at(source: &str, vertex: &Vertex) -> Option<Span> {
    let label = vertex.label.as_ref()?;
    if label.text.kind != TextKind::Plain
        || !matches!(
            label.form,
            LabelForm::Square | LabelForm::Stadium | LabelForm::Subroutine | LabelForm::Cylinder
        )
    {
        return None;
    }
    let trimmed = label.text.text.trim();
    let slash = |byte: u8| matches!(byte, b'/' | b'\\');
    if trimmed.as_bytes().first().is_some_and(|byte| slash(*byte))
        && trimmed.as_bytes().last().is_some_and(|byte| slash(*byte))
    {
        return None;
    }
    for token in &label.text.tokens {
        if matches!(token.kind, TokenKind::Str | TokenKind::MdStr) {
            continue;
        }
        if let Some(offset) = token.text(source).find('@') {
            return Some(Span {
                start: token.span.start + offset,
                end: token.span.start + offset + 1,
            });
        }
    }
    None
}

fn subgraph_scoped(model: &Model, parent: &str, id: &str) -> bool {
    let mut scope = parent;
    loop {
        if scope.is_empty() {
            return false;
        }
        if scope == id {
            return true;
        }
        let Some(group) = model.groups.iter().find(|group| group.id == scope) else {
            return false;
        };
        scope = group.parent.as_str();
    }
}

fn join_group(model: &mut Model, id: &str, parent: &str) {
    if model
        .groups
        .iter()
        .any(|group| group.id == parent && group.members.iter().any(|member| member == id))
    {
        return;
    }
    if let Some(group) = model.groups.iter_mut().find(|group| group.id == parent) {
        group.members.push(id.into());
    }
}

fn vertices(source: &str, value: &VertexStatement, model: &mut Model, parent: &str) {
    let mut previous = group_nodes(source, &value.first, model, parent);
    for (link, group) in &value.rest {
        let next = group_nodes(source, group, model, parent);
        if let (Some(from), Some(to)) = (previous.last(), next.first()) {
            model.edges.push(edge(source, link, from, to, value.span));
        }
        previous = next;
    }
}

fn edge(source: &str, link: &Link, from: &str, to: &str, statement_span: Span) -> Edge {
    let body = link.statement.end_text.trim();
    let stroke = stroke_of(body);
    let (start_marker, end_marker) = edge_markers(link, body);
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
        length: if body.contains('.') {
            body.bytes().filter(|b| *b == b'.').count().min(10)
        } else {
            count.saturating_sub(1).min(10)
        },
        user_id: link
            .statement
            .link_id
            .map(|span| source[span.start..span.end].trim_end_matches('@').into())
            .unwrap_or_default(),
        span: link.span,
        statement_span,
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

fn edge_markers(link: &Link, end: &str) -> (&'static str, &'static str) {
    let end_marker = marker(end.chars().last());
    let start = link.statement.start_text.as_deref().map_or(end, str::trim);
    let start_marker = marker(start.chars().next());
    if stroke_of(start) != stroke_of(end) || start_marker != "none" && start_marker != end_marker {
        return ("none", "none");
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
    crate::syntax::entities::decode_entities(text)
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
    let declaration = model.subgraph_count;
    model.subgraph_count += 1;
    let id = value
        .id
        .as_ref()
        .map(|id| resolve_label(&id.text))
        .filter(|id| {
            value.title.is_some()
                || !id
                    .bytes()
                    .any(|b| matches!(b, b' ' | b'\t' | b'\r' | b'\n' | 0x0b | 0x0c))
        })
        .unwrap_or_else(|| format!("subGraph{declaration}"));
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
    let previous_direction = model
        .groups
        .iter()
        .position(|group| group.id == id)
        .map(|index| {
            (
                index,
                model.groups[index].direction.clone(),
                model.groups[index].direction_span,
            )
        });
    if previous_direction.is_none() {
        model.groups.push(Group {
            id: id.clone(),
            title: resolve_label(&title),
            parent: parent.into(),
            span: value.span,
            ..Group::default()
        });
    }
    walk(source, &value.body, model, &id);
    if let Some((index, direction, span)) = previous_direction {
        model.groups[index].direction = direction;
        model.groups[index].direction_span = span;
    }
    finish_group(model, &id);
}

fn finish_group(model: &mut Model, id: &str) {
    let Some(group) = model.groups.iter_mut().find(|group| group.id == id) else {
        return;
    };
    group.members.retain(|member| {
        if member == id
            || model
                .member_owners
                .get(member)
                .is_some_and(|owner| owner != id)
        {
            return false;
        }
        model.member_owners.insert(member.clone(), id.into());
        true
    });
}
fn apply_style(value: &StyleStatement, model: &mut Model) {
    for id in value.target.text.split(',').map(str::trim) {
        let index = node_index(model, id, value.target.span, None);
        model.nodes[index]
            .styles
            .extend(value.styles.styles.iter().cloned());
    }
}
fn apply_class(value: &ClassStatement, model: &mut Model) {
    for id in value.targets.text.split(',').map(str::trim) {
        let index = node_index(model, id, value.targets.span, None);
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
                    shape_value_span(data, entry.key_span),
                ));
            }
        }
        node.attrs.insert(entry.key, value);
    }
    finish_shape_data(node);
    diagnostics
}

fn shape_value_span(data: &ShapeData, key: Span) -> Span {
    let prefix = shape_prefix(data);
    let tail = data
        .text
        .get(key.end.saturating_sub(prefix)..)
        .unwrap_or("");
    let value = tail.trim_start_matches([' ', '\t', '\r', '\n', ':']);
    let start = key.end + tail.len() - value.len();
    let end = shape_value_end(value);
    shape_source_span(
        data,
        Span {
            start,
            end: start + value[..end].trim_end().len(),
        },
    )
}

fn shape_value_end(value: &str) -> usize {
    let mut quote = None;
    let mut escaped = false;
    for (index, character) in value.char_indices() {
        if escaped {
            escaped = false;
            continue;
        }
        if character == '\\' && quote == Some('"') {
            escaped = true;
        } else if Some(character) == quote {
            quote = None;
        } else if quote.is_none() {
            match character {
                '"' | '\'' => quote = Some(character),
                ',' | '\r' | '\n' => return index,
                _ => {}
            }
        }
    }
    value.len()
}

fn shape_prefix(data: &ShapeData) -> usize {
    usize::from(!data.text.contains(['\r', '\n']))
}

fn shape_positions(data: &ShapeData) -> Vec<usize> {
    if shape_prefix(data) == 0 {
        return data.src_at.clone();
    }
    let first = data.src_at.first().copied().unwrap_or(data.span.start);
    let last = data.src_at.last().map_or(data.span.end, |at| at + 1);
    let mut positions = Vec::with_capacity(data.src_at.len() + 2);
    positions.push(first);
    positions.extend_from_slice(&data.src_at);
    positions.push(last);
    positions
}

fn shape_source_span(data: &ShapeData, span: Span) -> Span {
    let positions = shape_positions(data);
    let first = data.src_at.first().copied().unwrap_or(data.span.start);
    let offset = |reader_offset: usize| {
        positions
            .get(reader_offset)
            .copied()
            .or_else(|| positions.last().map(|at| at + 1))
            .unwrap_or(first)
            .min(data.span.end)
    };
    let start = offset(span.start);
    Span {
        start,
        end: offset(span.end).max(start),
    }
}

fn shape_entries(data: &ShapeData) -> (Vec<crate::syntax::config_value::Entry>, Vec<Diagnostic>) {
    use crate::syntax::config_value::{ConfigValue, parse_config_yaml};
    let input = if shape_prefix(data) == 1 {
        format!("{{{}}}", data.text)
    } else {
        data.text.clone()
    };
    let (value, mut diagnostics) = parse_config_yaml(&input, 0, input.len());
    for diagnostic in &mut diagnostics {
        diagnostic.span = shape_source_span(data, diagnostic.span);
    }
    let ConfigValue::Mapping(entries) = value else {
        return (Vec::new(), diagnostics);
    };
    (entries, diagnostics)
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
        node.label_kind = Some(match node.attrs.get("labelType").map(String::as_str) {
            Some("markdown") => TextKind::Markdown,
            Some("string") => TextKind::String,
            _ => TextKind::Plain,
        });
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

#[cfg(test)]
mod parity_tests {
    #[test]
    fn unquoted_at_declaration_evidence() -> Result<(), &'static str> {
        let source = "flowchart TD\nA[first@host@other]\nsubgraph outer\nsubgraph inner\nB([nested@host])\nend\nend\nA[last@host]\nC[\"quoted@host\"]\nD[\"`markdown@host`\"]\nE[ /slash@host/ ]\nF(round@host)\nG[[subroutine@host]]\nH[(cylinder@host)]\n";
        let parsed = crate::syntax::flowchart::parse(source, &[]);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let (model, diagnostics) = super::resolve(source, &parsed.document);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let expected: Vec<_> = [
            "first@host",
            "nested@host",
            "last@host",
            "subroutine@host",
            "cylinder@host",
        ]
        .into_iter()
        .map(|label| {
            let start = source.find(label).ok_or("source label")?
                + label.find('@').ok_or("label at sign")?;
            Ok(crate::source::Span {
                start,
                end: start + 1,
            })
        })
        .collect::<Result<_, &'static str>>()?;
        assert_eq!(model.unquoted_at_spans, expected);
        Ok(())
    }

    #[test]
    fn flowchart_typed_shape_value_span() {
        for source in [
            "flowchart\nA@{ shape: missing }\n",
            "flowchart\nA@{\n shape:\n  missing\n}\n",
            "flowchart\r\nA@{\r\n shape:\r\n  missing\r\n}\r\n",
            "flowchart\rA@{\r shape:\r  missing\r}\r",
        ] {
            let parsed = crate::syntax::flowchart::parse(source, &[]);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let (_, diagnostics) = super::resolve(source, &parsed.document);
            assert_eq!(diagnostics.len(), 1);
            let diagnostic = &diagnostics[0];
            assert_eq!(diagnostic.code, "flowchart/typed-shape-unsupported");
            assert_eq!(
                &source[diagnostic.span.start..diagnostic.span.end],
                "missing"
            );
        }
    }
}
