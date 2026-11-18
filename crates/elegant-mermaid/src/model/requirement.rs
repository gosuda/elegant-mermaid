use crate::syntax::entities::decode_entities as decode_label;
use crate::{diag::Diagnostic, source::Span, syntax::requirement::ast::*};

#[derive(Debug, Clone, Default)]
pub struct Model {
    pub requirements: Vec<Requirement>,
    pub elements: Vec<Element>,
    pub relationships: Vec<Relation>,
    pub declarations: Vec<Declaration>,
    pub id_declarations: Vec<IdDeclaration>,
    pub class_definitions: Vec<ClassDefinition>,
    pub metadata: Vec<Metadata>,
    pub direction: String,
    pub title: String,
    pub acc_title: String,
    pub acc_descr: String,
    pub directives: Vec<Value>,
}
#[derive(Debug, Clone)]
pub struct Declaration {
    pub node: NodeRef,
    pub span: Span,
}
#[derive(Debug, Clone)]
pub enum IdDeclaration {
    Field { requirement: usize, field: usize },
    Discarded(Value),
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Value {
    pub value: String,
    pub span: Span,
}
#[derive(Debug, Clone)]
pub struct Field {
    pub name: String,
    pub value: Value,
    pub span: Span,
    pub keyword_span: Span,
    pub colon_span: Span,
}
#[derive(Debug, Clone)]
pub struct Requirement {
    pub name: String,
    pub kind: String,
    pub id: String,
    pub text: String,
    pub risk: String,
    pub verify_method: String,
    pub span: Span,
    pub name_span: Span,
    pub type_span: Span,
    pub delimiters: (Span, Span),
    pub fields: Vec<Field>,
    pub classes: Vec<Value>,
    pub styles: Vec<Value>,
}
#[derive(Debug, Clone)]
pub struct Element {
    pub name: String,
    pub kind: String,
    pub docref: String,
    pub span: Span,
    pub name_span: Span,
    pub delimiters: (Span, Span),
    pub fields: Vec<Field>,
    pub classes: Vec<Value>,
    pub styles: Vec<Value>,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NodeRef {
    Requirement(usize),
    Element(usize),
}
#[derive(Debug, Clone)]
pub struct Relation {
    pub from: Value,
    pub to: Value,
    pub from_node: Option<NodeRef>,
    pub to_node: Option<NodeRef>,
    pub kind: String,
    pub label: String,
    pub span: Span,
    pub type_span: Span,
    pub arrow_span: Span,
    pub line_span: Span,
}
#[derive(Debug, Clone)]
pub struct ClassDefinition {
    pub name: Value,
    pub styles: Vec<Value>,
    pub text_styles: Vec<Value>,
}
#[derive(Debug, Clone)]
pub struct Metadata {
    pub kind: &'static str,
    pub span: Span,
    pub targets: Vec<Value>,
    pub values: Vec<Value>,
    pub separator: Option<Span>,
}

pub fn resolve(_source: &str, document: &Start<'_>) -> (Model, Vec<Diagnostic>) {
    let mut model = Model {
        direction: "TB".into(),
        ..Model::default()
    };
    for directive in &document.directives {
        model.directive(directive);
    }
    for statement in &document.diagram.statements {
        model.statement(&statement.kind);
    }
    for relation in &mut model.relationships {
        relation.from_node = lookup(&model.requirements, &model.elements, &relation.from.value);
        relation.to_node = lookup(&model.requirements, &model.elements, &relation.to.value);
    }
    (model, Vec::new())
}

fn value(text: &str, span: Span) -> Value {
    Value {
        value: text.into(),
        span,
    }
}

fn lookup(requirements: &[Requirement], elements: &[Element], name: &str) -> Option<NodeRef> {
    requirements
        .iter()
        .position(|node| node.name == name)
        .map(NodeRef::Requirement)
        .or_else(|| {
            elements
                .iter()
                .position(|node| node.name == name)
                .map(NodeRef::Element)
        })
}

fn field_value(fields: &[Field], name: &str) -> String {
    fields
        .iter()
        .find(|field| field.name == name)
        .map_or_else(String::new, |field| field.value.value.clone())
}

impl Model {
    fn statement(&mut self, statement: &StatementKind<'_>) {
        match statement {
            StatementKind::Requirement(definition) => self.requirement(definition),
            StatementKind::Element(definition) => self.element(definition),
            StatementKind::Relationship(relation) => self.relationship(relation),
            StatementKind::Directive(directive) => self.directive(directive),
            StatementKind::Direction(direction) => self.direction = direction.value.into(),
            StatementKind::ClassDef(definition) => self.define_class(definition),
            StatementKind::Class(statement) => self.assign_classes(statement),
            StatementKind::Style(statement) => self.style(statement),
        }
    }

    fn requirement(&mut self, definition: &RequirementDef<'_>) {
        let index = self
            .requirements
            .iter()
            .position(|node| node.name == definition.name.value);
        let node_index = index.unwrap_or(self.requirements.len());
        self.declarations.push(Declaration {
            node: NodeRef::Requirement(node_index),
            span: definition.name.span,
        });
        for (field, item) in definition.body.fields.iter().enumerate() {
            if let RequirementFieldValue::Id(id) = &item.value {
                self.id_declarations.push(
                    if index.is_some() || decode_label(&id.value) != id.value {
                        IdDeclaration::Discarded(value(&id.value, id.span))
                    } else {
                        IdDeclaration::Field {
                            requirement: node_index,
                            field,
                        }
                    },
                );
            }
        }
        if !self
            .requirements
            .iter()
            .any(|node| node.name == definition.name.value)
        {
            let fields = requirement_fields(&definition.body);
            self.requirements.push(Requirement {
                name: definition.name.value.as_ref().into(),
                kind: definition.requirement_type.value.into(),
                id: field_value(&fields, "id"),
                text: field_value(&fields, "text"),
                risk: field_value(&fields, "risk"),
                verify_method: field_value(&fields, "verifyMethod"),
                span: definition.span,
                name_span: definition.name.span,
                type_span: definition.requirement_type.span,
                delimiters: definition.delimiters,
                fields,
                classes: vec![value("default", definition.name.span)],
                styles: Vec::new(),
            });
        }
        self.inline_classes(&definition.name.value, definition.classes.as_ref());
    }

    fn element(&mut self, definition: &ElementDef<'_>) {
        let index = self
            .elements
            .iter()
            .position(|node| node.name == definition.name.value)
            .unwrap_or(self.elements.len());
        self.declarations.push(Declaration {
            node: NodeRef::Element(index),
            span: definition.name.span,
        });
        if !self
            .elements
            .iter()
            .any(|node| node.name == definition.name.value)
        {
            let fields = element_fields(&definition.body);
            self.elements.push(Element {
                name: definition.name.value.as_ref().into(),
                kind: field_value(&fields, "type"),
                docref: field_value(&fields, "docref"),
                span: definition.span,
                name_span: definition.name.span,
                delimiters: definition.delimiters,
                fields,
                classes: vec![value("default", definition.name.span)],
                styles: Vec::new(),
            });
        }
        self.inline_classes(&definition.name.value, definition.classes.as_ref());
    }

    fn relationship(&mut self, relation: &RelationshipDef<'_>) {
        let (from, to) = if relation.reversed {
            (&relation.right, &relation.left)
        } else {
            (&relation.left, &relation.right)
        };
        self.relationships.push(Relation {
            from: value(&from.value, from.span),
            to: value(&to.value, to.span),
            from_node: None,
            to_node: None,
            kind: relation.relationship.value.into(),
            label: format!("<<{}>>", relation.relationship.value),
            span: relation.span,
            type_span: relation.relationship.span,
            arrow_span: relation.arrow.span,
            line_span: relation.line,
        });
    }

    fn directive(&mut self, directive: &Directive<'_>) {
        let text = directive.value.text.trim();
        if directive.title {
            self.acc_title = text.into();
        } else {
            self.acc_descr = text.into();
        }
        self.directives.push(value(text, directive.span));
    }

    fn node_metadata(&mut self, name: &str) -> Option<(&mut Vec<Value>, &mut Vec<Value>)> {
        if let Some(node) = self.requirements.iter_mut().find(|node| node.name == name) {
            return Some((&mut node.classes, &mut node.styles));
        }
        self.elements
            .iter_mut()
            .find(|node| node.name == name)
            .map(|node| (&mut node.classes, &mut node.styles))
    }

    fn inline_classes(&mut self, name: &str, classes: Option<&IdList<'_>>) {
        let Some(classes) = classes else { return };
        self.apply_classes(name, &names(classes));
    }

    fn apply_classes(&mut self, name: &str, classes: &[Value]) {
        let styles = classes
            .iter()
            .filter_map(|class| {
                self.class_definitions
                    .iter()
                    .find(|definition| definition.name.value == class.value)
            })
            .flat_map(|definition| definition.styles.iter().cloned())
            .collect::<Vec<_>>();
        if let Some((assigned, direct)) = self.node_metadata(name) {
            assigned.extend_from_slice(classes);
            direct.extend(styles);
        }
    }

    fn assign_classes(&mut self, statement: &ClassStatement<'_>) {
        let classes = names(&statement.classes);
        for target in &statement.targets.names {
            self.apply_classes(&target.value, &classes);
        }
        self.metadata.push(Metadata {
            kind: "class",
            span: statement.span,
            targets: names(&statement.targets),
            values: classes,
            separator: statement.separator,
        });
    }

    fn style(&mut self, statement: &StyleStatement<'_>) {
        let styles = styles(&statement.styles);
        for target in &statement.ids.names {
            let Some((_, direct)) = self.node_metadata(&target.value) else {
                break;
            };
            direct.extend(split_styles(&styles));
        }
        self.metadata.push(Metadata {
            kind: "style",
            span: statement.span,
            targets: names(&statement.ids),
            values: styles,
            separator: None,
        });
    }

    fn define_class(&mut self, statement: &ClassDefStatement<'_>) {
        let additions = styles(&statement.styles);
        for name in names(&statement.ids) {
            self.extend_definition(name, &additions);
        }
        self.metadata.push(Metadata {
            kind: "classDef",
            span: statement.span,
            targets: names(&statement.ids),
            values: additions,
            separator: None,
        });
    }

    fn extend_definition(&mut self, name: Value, additions: &[Value]) {
        let text_styles = additions
            .iter()
            .filter(|style| style.value.contains("color"))
            .map(|style| value(&style.value.replacen("fill", "bgFill", 1), style.span));
        if let Some(definition) = self
            .class_definitions
            .iter_mut()
            .find(|d| d.name.value == name.value)
        {
            definition.styles.extend_from_slice(additions);
            definition.text_styles.extend(text_styles);
        } else {
            self.class_definitions.push(ClassDefinition {
                name: name.clone(),
                styles: additions.to_vec(),
                text_styles: text_styles.collect(),
            });
        }
        for node in &mut self.requirements {
            append_class_styles(&node.classes, &mut node.styles, &name.value, additions);
        }
        for node in &mut self.elements {
            append_class_styles(&node.classes, &mut node.styles, &name.value, additions);
        }
    }
}

fn names(ids: &IdList<'_>) -> Vec<Value> {
    ids.names
        .iter()
        .map(|id| value(&id.value, id.span))
        .collect()
}

fn styles(styles: &StylesOpt<'_>) -> Vec<Value> {
    styles
        .styles
        .iter()
        .map(|style| {
            let text = style
                .components
                .iter()
                .map(|component| component.text.as_ref())
                .collect::<String>();
            value(&text, style.span)
        })
        .collect()
}

fn split_styles(styles: &[Value]) -> impl Iterator<Item = Value> + '_ {
    styles
        .iter()
        .flat_map(|style| style.value.split(',').map(|part| value(part, style.span)))
}

fn append_class_styles(
    classes: &[Value],
    direct: &mut Vec<Value>,
    name: &str,
    additions: &[Value],
) {
    if classes.iter().any(|class| class.value == name) {
        direct.extend(split_styles(additions));
    }
}

fn requirement_fields(body: &RequirementBody<'_>) -> Vec<Field> {
    body.fields
        .iter()
        .map(|field| {
            let (name, text, span) = match &field.value {
                RequirementFieldValue::Id(v) => ("id", v.value.as_ref(), v.span),
                RequirementFieldValue::Text(v) => ("text", v.value.as_ref(), v.span),
                RequirementFieldValue::Risk(v) => ("risk", v.value, v.span),
                RequirementFieldValue::Verify(v) => ("verifyMethod", v.value, v.span),
            };
            Field {
                name: name.into(),
                value: value(&decode_label(text), span),
                span: field.span,
                keyword_span: field.keyword.span,
                colon_span: field.colon,
            }
        })
        .collect()
}

fn element_fields(body: &ElementBody<'_>) -> Vec<Field> {
    body.fields
        .iter()
        .map(|field| {
            let (name, text, span) = match &field.value {
                ElementFieldValue::Type(v) => ("type", v.value.as_ref(), v.span),
                ElementFieldValue::Ref(v) => ("docref", v.value.as_ref(), v.span),
            };
            Field {
                name: name.into(),
                value: value(&decode_label(text), span),
                span: field.span,
                keyword_span: field.keyword.span,
                colon_span: field.colon,
            }
        })
        .collect()
}

impl Requirement {
    pub fn rows(&self) -> Vec<String> {
        let mut rows = vec![format!("<<{}>>", self.kind), decode_label(&self.name)];
        append_row(&mut rows, "ID", &self.id);
        append_row(&mut rows, "Text", &self.text);
        append_row(&mut rows, "Risk", &self.risk);
        append_row(&mut rows, "Verification", &self.verify_method);
        rows
    }
}

impl Element {
    pub fn rows(&self) -> Vec<String> {
        let mut rows = vec!["<<Element>>".into(), decode_label(&self.name)];
        append_row(&mut rows, "Type", &self.kind);
        append_row(&mut rows, "Doc Ref", &self.docref);
        rows
    }
}

fn append_row(rows: &mut Vec<String>, label: &str, text: &str) {
    if !text.is_empty() {
        rows.push(format!("{label}: {text}"));
    }
}

#[cfg(test)]
mod tests;
