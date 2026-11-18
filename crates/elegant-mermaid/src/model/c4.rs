use crate::{
    diag::Diagnostic,
    source::Span,
    syntax::c4::{ast::*, lexer::Token},
};

#[derive(Debug, Clone, Default)]
pub struct Model {
    pub c4_type: String,
    pub direction: String,
    pub elements: Vec<Element>,
    pub boundaries: Vec<Boundary>,
    pub relations: Vec<Relation>,
    pub declarations: Vec<Declaration>,
    pub aliases: Vec<AliasOccurrence>,
    pub usages: Vec<Usage>,
    pub acc_title: String,
    pub acc_descr: String,
    pub accessibility: Vec<Text>,
    pub layout_config: Vec<Field>,
}

#[derive(Debug, Clone, Copy)]
pub enum Declaration {
    Element(usize),
    Boundary(usize),
}

#[derive(Debug, Clone, Copy)]
pub struct AliasOccurrence {
    pub declaration: Declaration,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum Usage {
    Relation { index: usize, from: Span, to: Span },
    ElementStyle(Text),
    RelationStyle(Text, Text),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Text {
    pub value: String,
    pub span: Span,
}

impl Default for Text {
    fn default() -> Self {
        Self {
            value: String::new(),
            span: Span { start: 0, end: 0 },
        }
    }
}

#[derive(Debug, Clone)]
pub struct Field {
    pub name: String,
    pub value: Text,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Element {
    pub id: String,
    pub alias_span: Span,
    pub macro_name: String,
    pub macro_span: Span,
    pub kind: String,
    pub parent: String,
    pub label: Text,
    pub fields: Vec<Field>,
    pub styles: Vec<Field>,
    pub attributes: Vec<Field>,
    pub span: Span,
    pub wrap: bool,
}

#[derive(Debug, Clone)]
pub struct Boundary {
    pub id: String,
    pub alias_span: Span,
    pub macro_name: String,
    pub macro_span: Span,
    pub node_type: String,
    pub parent: String,
    pub label: Text,
    pub fields: Vec<Field>,
    pub styles: Vec<Field>,
    pub attributes: Vec<Field>,
    pub span: Span,
    pub wrap: bool,
}

#[derive(Debug, Clone)]
pub struct Relation {
    pub from: Text,
    pub to: Text,
    pub label: Text,
    pub macro_name: String,
    pub macro_span: Span,
    pub fields: Vec<Field>,
    pub styles: Vec<Field>,
    pub attributes: Vec<Field>,
    pub span: Span,
    pub wrap: bool,
}

struct Call<'a, 'src> {
    name: &'src str,
    attrs: &'a Attributes<'src>,
    macro_span: Span,
    span: Span,
}

pub fn resolve(_source: &str, document: &Start<'_>) -> (Model, Vec<Diagnostic>) {
    let mut model = Model {
        direction: "TB".into(),
        ..Model::default()
    };
    match &document.kind {
        StartKind::Direction(direction) => {
            model.direction = direction
                .direction
                .text
                .trim()
                .trim_start_matches("direction")
                .trim()
                .into();
        }
        StartKind::MermaidDoc(document) => {
            let config = &document.graph_config;
            model.c4_type = config.header.text.as_ref().into();
            model.statements(&config.statements.items, "");
        }
    }
    (model, Vec::new())
}

impl Model {
    fn statements(&mut self, statements: &[Statement<'_>], parent: &str) {
        for statement in statements {
            match statement {
                Statement::Other(other) => self.accessibility(other),
                Statement::Diagram(diagram) => self.diagram(diagram, parent),
            }
        }
    }

    fn accessibility(&mut self, statement: &OtherStatement<'_>) {
        let value = text(&statement.value);
        match statement.form {
            "title" | "acc_title" => self.acc_title = value.value.clone(),
            _ => self.acc_descr = value.value.clone(),
        }
        self.accessibility.push(Text {
            value: value.value,
            span: statement.span,
        });
    }

    fn diagram(&mut self, statement: &DiagramStatement<'_>, parent: &str) {
        match &statement.kind {
            DiagramStatementKind::Boundary(boundary) => {
                let Some(id) = self.boundary(boundary, parent) else {
                    return;
                };
                self.statements(&boundary.body.items, &id);
            }
            DiagramStatementKind::Call {
                macro_token,
                attributes,
            } => {
                self.call(
                    Call {
                        name: &macro_token.text,
                        attrs: attributes,
                        macro_span: macro_token.span,
                        span: statement.span,
                    },
                    parent,
                );
            }
        }
    }

    fn call(&mut self, call: Call<'_, '_>, parent: &str) {
        match call.name {
            "UpdateElementStyle" => self.element_style(call.attrs),
            "UpdateRelStyle" => self.relation_style(call.attrs),
            "UpdateLayoutConfig" => self.layout_hint(call.attrs),
            name if name.starts_with("Rel") || name == "BiRel" => self.relation(&call),
            _ => self.element(&call, parent),
        }
    }

    fn element(&mut self, call: &Call<'_, '_>, parent: &str) {
        let Some(alias) = positional(call.attrs, 0) else {
            return;
        };
        let index = self
            .elements
            .iter()
            .position(|element| element.id == alias.value);
        self.aliases.push(AliasOccurrence {
            declaration: Declaration::Element(index.unwrap_or(self.elements.len())),
            span: alias.span,
        });
        let mut element = Element::new(call, parent, alias);
        if let Some(old) = index.and_then(|index| self.elements.get_mut(index)) {
            element.fields = std::mem::take(&mut old.fields);
            element.styles = std::mem::take(&mut old.styles);
        }
        element.fields.retain(|field| field.name != "label");
        let signature: &[&str] =
            if call.name.starts_with("Container") || call.name.starts_with("Component") {
                &["techn", "descr", "sprite", "tags", "link"]
            } else {
                &["descr", "sprite", "tags", "link"]
            };
        default_text_fields(&mut element.fields, signature);
        apply_optional(call.attrs, 2, signature, &mut element.fields);
        sync_label(&mut element.label, &element.fields);
        if let Some(old) = index.and_then(|index| self.elements.get_mut(index)) {
            *old = element;
            return;
        }
        self.declarations
            .push(Declaration::Element(self.elements.len()));
        self.elements.push(element);
    }

    fn boundary(&mut self, statement: &BoundaryStatement<'_>, parent: &str) -> Option<String> {
        let start = &statement.start.start;
        let call = Call {
            name: &start.macro_token.text,
            attrs: &start.attributes,
            macro_span: start.macro_token.span,
            span: statement.span,
        };
        let alias = positional(call.attrs, 0)?;
        let index = self
            .boundaries
            .iter()
            .position(|boundary| boundary.id == alias.value);
        self.aliases.push(AliasOccurrence {
            declaration: Declaration::Boundary(index.unwrap_or(self.boundaries.len())),
            span: alias.span,
        });
        let mut boundary = Boundary::new(&call, parent, alias);
        if let Some(old) = index.and_then(|index| self.boundaries.get_mut(index)) {
            boundary.fields = std::mem::take(&mut old.fields);
            boundary.styles = std::mem::take(&mut old.styles);
        }
        boundary.fields.retain(|field| field.name != "label");
        boundary_fields(&call, &mut boundary.fields);
        sync_label(&mut boundary.label, &boundary.fields);
        let id = boundary.id.clone();
        if let Some(old) = index.and_then(|index| self.boundaries.get_mut(index)) {
            *old = boundary;
            return Some(id);
        }
        self.declarations
            .push(Declaration::Boundary(self.boundaries.len()));
        self.boundaries.push(boundary);
        Some(id)
    }

    fn relation(&mut self, call: &Call<'_, '_>) {
        let offset = usize::from(call.name == "RelIndex");
        let Some(from) = positional(call.attrs, offset) else {
            return;
        };
        let Some(to) = positional(call.attrs, offset + 1) else {
            return;
        };
        let Some(label) = positional(call.attrs, offset + 2) else {
            return;
        };
        let index = self.relations.iter().position(|relation| {
            relation.from.value == from.value && relation.to.value == to.value
        });
        self.usages.push(Usage::Relation {
            index: index.unwrap_or(self.relations.len()),
            from: from.span,
            to: to.span,
        });
        let mut relation = Relation::new(call, [from, to, label]);
        if let Some(old) = index.and_then(|index| self.relations.get_mut(index)) {
            relation.fields = std::mem::take(&mut old.fields);
            relation.styles = std::mem::take(&mut old.styles);
        }
        relation.fields.retain(|field| field.name != "label");
        let signature = ["techn", "descr", "sprite", "tags", "link"];
        default_text_fields(&mut relation.fields, &signature);
        apply_optional(call.attrs, offset + 3, &signature, &mut relation.fields);
        sync_label(&mut relation.label, &relation.fields);
        if let Some(old) = index.and_then(|index| self.relations.get_mut(index)) {
            *old = relation;
            return;
        }
        self.relations.push(relation);
    }

    fn element_style(&mut self, attrs: &Attributes<'_>) {
        let Some(alias) = positional(attrs, 0) else {
            return;
        };
        let target = self
            .elements
            .iter_mut()
            .find(|element| element.id == alias.value)
            .map(|element| &mut element.styles)
            .or_else(|| {
                self.boundaries
                    .iter_mut()
                    .find(|boundary| boundary.id == alias.value)
                    .map(|boundary| &mut boundary.styles)
            });
        self.usages.push(Usage::ElementStyle(alias));
        let Some(fields) = target else {
            return;
        };
        let signature = [
            "bgColor",
            "fontColor",
            "borderColor",
            "shadowing",
            "shape",
            "sprite",
            "techn",
            "legendText",
            "legendSprite",
        ];
        apply_optional(attrs, 1, &signature, fields);
    }

    fn relation_style(&mut self, attrs: &Attributes<'_>) {
        let Some(from) = positional(attrs, 0) else {
            return;
        };
        let Some(to) = positional(attrs, 1) else {
            return;
        };
        let index = self.relations.iter().position(|relation| {
            relation.from.value == from.value && relation.to.value == to.value
        });
        self.usages.push(Usage::RelationStyle(from, to));
        let Some(relation) = index.and_then(|index| self.relations.get_mut(index)) else {
            return;
        };
        apply_optional(
            attrs,
            2,
            &["textColor", "lineColor", "offsetX", "offsetY"],
            &mut relation.styles,
        );
        normalize_offsets(&mut relation.styles);
    }

    fn layout_hint(&mut self, attrs: &Attributes<'_>) {
        let mut fields = Vec::new();
        apply_optional(attrs, 0, &["c4ShapeInRow", "c4BoundaryInRow"], &mut fields);
        for mut field in fields {
            if !matches!(field.name.as_str(), "c4ShapeInRow" | "c4BoundaryInRow") {
                continue;
            }
            let Some(value) = leading_integer(&field.value.value).filter(|value| *value >= 1)
            else {
                continue;
            };
            field.value.value = value.to_string();
            set_field(&mut self.layout_config, field);
        }
    }
}

impl Element {
    fn new(call: &Call<'_, '_>, parent: &str, alias: Text) -> Self {
        Self {
            id: alias.value,
            alias_span: alias.span,
            macro_name: call.name.into(),
            macro_span: call.macro_span,
            kind: element_kind(call.name),
            parent: parent.into(),
            label: positional(call.attrs, 1).unwrap_or_default(),
            fields: Vec::new(),
            styles: Vec::new(),
            attributes: attributes(call.attrs),
            span: call.span,
            wrap: false,
        }
    }
}

impl Boundary {
    fn new(call: &Call<'_, '_>, parent: &str, alias: Text) -> Self {
        Self {
            id: alias.value,
            alias_span: alias.span,
            macro_name: call.name.into(),
            macro_span: call.macro_span,
            node_type: node_type(call.name).into(),
            parent: parent.into(),
            label: positional(call.attrs, 1).unwrap_or_default(),
            fields: Vec::new(),
            styles: Vec::new(),
            attributes: attributes(call.attrs),
            span: call.span,
            wrap: false,
        }
    }
}

impl Relation {
    fn new(call: &Call<'_, '_>, endpoints: [Text; 3]) -> Self {
        let [from, to, label] = endpoints;
        Self {
            from,
            to,
            label,
            macro_name: if call.name == "RelIndex" {
                "Rel"
            } else {
                call.name
            }
            .into(),
            macro_span: call.macro_span,
            fields: Vec::new(),
            styles: Vec::new(),
            attributes: attributes(call.attrs),
            span: call.span,
            wrap: false,
        }
    }
}

fn text(token: &Token<'_>) -> Text {
    Text {
        value: token.text.trim().into(),
        span: token.span,
    }
}

fn positional(attrs: &Attributes<'_>, index: usize) -> Option<Text> {
    let attribute = attrs.items.get(index)?;
    match &attribute.kind {
        AttributeKind::Positional(token) => Some(text(token)),
        AttributeKind::Empty(_) => Some(Text {
            value: String::new(),
            span: attribute.span,
        }),
        AttributeKind::Named { .. } => None,
    }
}

fn attributes(attrs: &Attributes<'_>) -> Vec<Field> {
    attrs
        .items
        .iter()
        .enumerate()
        .map(|(index, attribute)| attribute_field(attribute, &index.to_string()))
        .collect()
}

fn attribute_field(attribute: &Attribute<'_>, name: &str) -> Field {
    let (name, value) = match &attribute.kind {
        AttributeKind::Named { key, value } => (key.text.as_ref(), text(value)),
        AttributeKind::Positional(token) => (name, text(token)),
        AttributeKind::Empty(_) => (
            name,
            Text {
                value: String::new(),
                span: attribute.span,
            },
        ),
    };
    Field {
        name: name.into(),
        value,
        span: attribute.span,
    }
}

fn apply_optional(attrs: &Attributes<'_>, start: usize, names: &[&str], fields: &mut Vec<Field>) {
    for (attribute, name) in attrs.items.iter().skip(start).zip(names) {
        set_field(fields, attribute_field(attribute, name));
    }
}

fn set_field(fields: &mut Vec<Field>, field: Field) {
    if let Some(old) = fields.iter_mut().find(|old| old.name == field.name) {
        *old = field;
    } else {
        fields.push(field);
    }
}

fn default_text_fields(fields: &mut Vec<Field>, names: &[&str]) {
    for name in names
        .iter()
        .filter(|name| matches!(**name, "techn" | "descr"))
    {
        if fields.iter().any(|field| field.name == *name) {
            continue;
        }
        fields.push(Field {
            name: (*name).into(),
            value: Text::default(),
            span: Span { start: 0, end: 0 },
        });
    }
}

fn sync_label(label: &mut Text, fields: &[Field]) {
    if let Some(field) = fields.iter().find(|field| field.name == "label") {
        label.clone_from(&field.value);
    }
}

fn boundary_fields(call: &Call<'_, '_>, fields: &mut Vec<Field>) {
    let default = boundary_type(call.name);
    set_field(
        fields,
        Field {
            name: "type".into(),
            value: Text {
                value: default.into(),
                span: call.attrs.span,
            },
            span: call.attrs.span,
        },
    );
    match call.name {
        "Enterprise_Boundary" | "System_Boundary" | "Container_Boundary" => {
            apply_optional(call.attrs, 2, &["tags", "link"], fields);
        }
        "Boundary" => apply_optional(call.attrs, 2, &["type", "tags", "link"], fields),
        _ => {
            default_text_fields(fields, &["descr"]);
            apply_optional(call.attrs, 2, &["type", "descr"], fields);
            apply_optional(call.attrs, 5, &["tags", "link"], fields);
        }
    }
}

fn boundary_type(name: &str) -> &str {
    match name {
        "Enterprise_Boundary" => "ENTERPRISE",
        "System_Boundary" => "SYSTEM",
        "Container_Boundary" => "CONTAINER",
        "Boundary" => "system",
        _ => "node",
    }
}

fn element_kind(name: &str) -> String {
    let (base, prefix) = name
        .strip_suffix("_Ext")
        .map_or((name, ""), |base| (base, "external_"));
    let (family, suffix) = base.strip_suffix("Db").map_or_else(
        || {
            base.strip_suffix("Queue")
                .map_or((base, ""), |family| (family, "_queue"))
        },
        |family| (family, "_db"),
    );
    format!("{prefix}{}{suffix}", family.to_ascii_lowercase())
}

fn node_type(name: &str) -> &str {
    match name {
        "Node_L" => "nodeL",
        "Node_R" => "nodeR",
        "Node" | "Deployment_Node" => "node",
        _ => "",
    }
}

fn leading_integer(value: &str) -> Option<i64> {
    let value = value.trim_start();
    let digits = value.strip_prefix(['+', '-']).unwrap_or(value);
    let length = digits.bytes().take_while(u8::is_ascii_digit).count();
    if length == 0 {
        return None;
    }
    let sign_length = value.len() - digits.len();
    value.get(..length + sign_length)?.parse().ok()
}

fn normalize_offsets(fields: &mut [Field]) {
    for field in fields
        .iter_mut()
        .filter(|field| matches!(field.name.as_str(), "offsetX" | "offsetY"))
    {
        if let Some(value) = leading_integer(&field.value.value) {
            field.value.value = value.to_string();
        }
    }
}

#[cfg(test)]
mod tests;
