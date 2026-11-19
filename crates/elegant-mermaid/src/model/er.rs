use crate::syntax::entities::decode_entities as decode_label;
use std::collections::BTreeSet;

use crate::{diag::Diagnostic, source::Span, syntax::er::ast::*};

#[derive(Debug, Clone, Default)]
pub struct Model {
    pub entities: Vec<Entity>,
    pub declarations: Vec<Declaration>,
    pub groups: Vec<Group>,
    pub relationships: Vec<Relationship>,
    pub definitions: Vec<ClassDefinition>,
    pub direction: String,
    pub acc_title: String,
    pub acc_descr: String,
    claimed: BTreeSet<String>,
}

#[derive(Debug, Clone)]
pub struct Declaration {
    pub entity: usize,
    pub name_span: Span,
    pub attributes: std::ops::Range<usize>,
}

#[derive(Debug, Clone)]
pub struct Entity {
    pub id: String,
    pub label: String,
    pub alias: Option<String>,
    pub span: Span,
    pub alias_span: Option<Span>,
    pub attributes: Vec<Attribute>,
    pub parent: Option<usize>,
    pub classes: Vec<String>,
    pub styles: Vec<String>,
    pub text_styles: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct Attribute {
    pub span: Span,
    pub attribute_type: String,
    pub type_span: Span,
    pub name: String,
    pub name_span: Span,
    pub keys: Vec<String>,
    pub key_spans: Vec<Span>,
    pub comment: String,
    pub comment_span: Option<Span>,
    pub nullable: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Target {
    Entity(usize),
    Group(usize),
}

#[derive(Debug, Clone)]
pub struct Group {
    pub id: String,
    pub label: String,
    pub span: Span,
    pub parent: Option<usize>,
    pub members: Vec<Target>,
    pub direction: String,
    pub direction_span: Span,
    pub classes: Vec<String>,
    pub styles: Vec<String>,
    pub text_styles: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct Relationship {
    pub from: String,
    pub to: String,
    pub from_target: Target,
    pub to_target: Target,
    pub span: Span,
    pub from_span: Span,
    pub to_span: Span,
    pub marker_start: &'static str,
    pub marker_end: &'static str,
    pub left_cardinality: CardinalityKind,
    pub right_cardinality: CardinalityKind,
    pub start_span: Span,
    pub end_span: Span,
    pub identifying: bool,
    pub label: String,
    pub label_span: Span,
    pub index: usize,
}

#[derive(Debug, Clone)]
pub struct ClassDefinition {
    pub name: String,
    pub styles: Vec<String>,
    pub text_styles: Vec<String>,
}

pub fn resolve(_source: &str, document: &Start<'_>) -> (Model, Vec<Diagnostic>) {
    let mut model = Model {
        direction: "TB".into(),
        ..Model::default()
    };
    if let Some(direction) = model.document(&document.document).1 {
        model.direction = direction.value.into();
    }
    model.compile_styles();
    (model, Vec::new())
}

impl Model {
    fn ensure(&mut self, name: &EntityName<'_>) -> usize {
        if let Some(index) = self
            .entities
            .iter()
            .position(|entity| entity.id == name.name)
        {
            return index;
        }
        let index = self.entities.len();
        self.entities.push(Entity {
            id: name.name.as_ref().into(),
            label: name.name.as_ref().into(),
            alias: None,
            span: name.span,
            alias_span: None,
            attributes: Vec::new(),
            parent: None,
            classes: vec!["default".into()],
            styles: Vec::new(),
            text_styles: Vec::new(),
        });
        index
    }

    fn target(&mut self, name: &EntityName<'_>) -> Target {
        let entity = self.ensure(name);
        self.groups
            .iter()
            .rposition(|group| group.id == name.name)
            .map_or(Target::Entity(entity), Target::Group)
    }

    fn document(&mut self, document: &Document<'_>) -> (Vec<Target>, Option<Direction>) {
        let mut members = Vec::new();
        let mut direction = None;
        for statement in document
            .lines
            .iter()
            .filter_map(|line| line.statement.as_ref())
        {
            if let StatementKind::Direction(value) = &statement.kind {
                direction = Some(*value);
                continue;
            }
            append_unique(&mut members, self.statement(statement));
        }
        (members, direction)
    }

    fn statement(&mut self, statement: &Statement<'_>) -> Vec<Target> {
        match &statement.kind {
            StatementKind::Entity {
                name,
                alias,
                classes,
                attributes,
                ..
            } => self.entity(
                name,
                (alias.as_ref(), classes.as_ref(), attributes.as_ref()),
            ),
            StatementKind::Relationship {
                from,
                from_classes,
                relation,
                to,
                to_classes,
                role,
            } => {
                let targets = self.relationship(statement.span, (from, to), (relation, role));
                self.named_classes(&from.name, from_classes.as_ref());
                self.named_classes(&to.name, to_classes.as_ref());
                targets
            }
            StatementKind::Subgraph {
                header, document, ..
            } => {
                vec![self.subgraph(statement.span, header, document)]
            }
            _ => {
                self.metadata(&statement.kind);
                Vec::new()
            }
        }
    }

    fn entity(
        &mut self,
        name: &EntityName<'_>,
        clause: (
            Option<&EntityName<'_>>,
            Option<&IdList<'_>>,
            Option<&Attributes<'_>>,
        ),
    ) -> Vec<Target> {
        let index = self.ensure(name);
        let Some(entity) = self.entities.get_mut(index) else {
            return Vec::new();
        };
        entity.apply_alias(clause.0);
        if let Some(attributes) = clause.2 {
            let start = entity.attributes.len();
            entity
                .attributes
                .extend(attributes.attributes.iter().map(Attribute::from_ast));
            self.declarations.push(Declaration {
                entity: index,
                name_span: name.span,
                attributes: start..entity.attributes.len(),
            });
        }
        self.named_classes(&name.name, clause.1);
        if clause.0.is_some() && clause.2.is_none() {
            return Vec::new();
        }
        vec![Target::Entity(index)]
    }

    fn relationship(
        &mut self,
        span: Span,
        names: (&EntityName<'_>, &EntityName<'_>),
        specification: (&RelSpec<'_>, &Role<'_>),
    ) -> Vec<Target> {
        let targets = (self.target(names.0), self.target(names.1));
        let (relation, role) = specification;
        self.relationships.push(Relationship {
            from: names.0.name.as_ref().into(),
            to: names.1.name.as_ref().into(),
            from_target: targets.0,
            to_target: targets.1,
            span,
            from_span: names.0.span,
            to_span: names.1.span,
            marker_start: cardinality(relation.right.kind),
            marker_end: cardinality(relation.left.kind),
            left_cardinality: relation.left.kind,
            right_cardinality: relation.right.kind,
            start_span: relation.right.span,
            end_span: relation.left.span,
            identifying: relation.relation_type.identifying,
            label: decode_label(&role.label),
            label_span: role.span,
            index: self.relationships.len(),
        });
        vec![targets.0, targets.1]
    }

    fn subgraph(
        &mut self,
        span: Span,
        header: &SubgraphHeader<'_>,
        document: &Document<'_>,
    ) -> Target {
        let (members, direction) = self.document(document);
        let members = members
            .into_iter()
            .filter(|target| {
                let id = self.target_id(*target).to_owned();
                self.claimed.insert(id)
            })
            .collect::<Vec<_>>();
        let index = self.groups.len();
        for member in &members {
            self.set_parent(*member, index);
        }
        let label = header.title.as_ref().map_or_else(
            || header.id.name.as_ref().into(),
            |title| {
                title
                    .parts
                    .iter()
                    .map(|part| part.name.as_ref())
                    .collect::<Vec<_>>()
                    .join(" ")
            },
        );
        self.groups.push(Group {
            id: header.id.name.as_ref().into(),
            label: decode_label(&label),
            span,
            parent: None,
            members,
            direction: direction.map_or_else(String::new, |value| value.value.into()),
            direction_span: direction.map_or(header.span, |value| value.span),
            classes: Vec::new(),
            styles: Vec::new(),
            text_styles: Vec::new(),
        });
        Target::Group(index)
    }

    fn target_id(&self, target: Target) -> &str {
        match target {
            Target::Entity(index) => self
                .entities
                .get(index)
                .map_or("", |entity| entity.id.as_str()),
            Target::Group(index) => self.groups.get(index).map_or("", |group| group.id.as_str()),
        }
    }

    fn set_parent(&mut self, target: Target, parent: usize) {
        match target {
            Target::Entity(index) => {
                if let Some(entity) = self.entities.get_mut(index) {
                    entity.parent = Some(parent);
                }
            }
            Target::Group(index) => {
                if let Some(group) = self.groups.get_mut(index) {
                    group.parent = Some(parent);
                }
            }
        }
    }

    fn existing(&self, name: &str) -> Vec<Target> {
        self.entities
            .iter()
            .position(|entity| entity.id == name)
            .map(Target::Entity)
            .into_iter()
            .chain(
                self.groups
                    .iter()
                    .rposition(|group| group.id == name)
                    .map(Target::Group),
            )
            .collect()
    }

    fn named_classes(&mut self, name: &str, classes: Option<&IdList<'_>>) {
        for target in self.existing(name) {
            self.attach_classes(target, classes);
        }
    }

    fn attach_classes(&mut self, target: Target, classes: Option<&IdList<'_>>) {
        let Some(classes) = classes else {
            return;
        };
        let names = classes.names.iter().map(|name| name.text.to_string());
        match target {
            Target::Entity(index) => {
                if let Some(entity) = self.entities.get_mut(index) {
                    entity.classes.extend(names);
                }
            }
            Target::Group(index) => {
                if let Some(group) = self.groups.get_mut(index) {
                    group.classes.extend(names);
                }
            }
        }
    }

    fn metadata(&mut self, statement: &StatementKind<'_>) {
        match statement {
            StatementKind::Accessibility { title: true, value } => {
                self.acc_title = value.text.trim().into()
            }
            StatementKind::Accessibility {
                title: false,
                value,
            } => self.acc_descr = value.text.trim().into(),
            StatementKind::ClassDef(value) => self.definition(value),
            StatementKind::Class(value) => self.class_statement(value),
            StatementKind::Style(value) => self.style_statement(value),
            _ => {}
        }
    }

    fn class_statement(&mut self, value: &ClassStatement<'_>) {
        for name in &value.targets.names {
            self.named_classes(&name.text, Some(&value.classes));
        }
    }

    fn style_statement(&mut self, value: &StyleStatement<'_>) {
        let styles = style_values(&value.styles);
        for name in &value.targets.names {
            for target in self.existing(&name.text) {
                self.attach_styles(target, &styles);
            }
        }
    }

    fn definition(&mut self, value: &ClassDefStatement<'_>) {
        let styles = style_values(&value.styles);
        for name in &value.ids.names {
            if let Some(definition) = self
                .definitions
                .iter_mut()
                .find(|row| row.name == name.text)
            {
                definition.styles.extend(styles.iter().cloned());
                definition.text_styles.extend(text_styles(&styles));
            } else {
                self.definitions.push(ClassDefinition {
                    name: name.text.as_ref().into(),
                    styles: styles.clone(),
                    text_styles: text_styles(&styles),
                });
            }
        }
    }

    fn attach_styles(&mut self, target: Target, styles: &[String]) {
        match target {
            Target::Entity(index) => {
                if let Some(entity) = self.entities.get_mut(index) {
                    entity.styles.extend_from_slice(styles);
                }
            }
            Target::Group(index) => {
                if let Some(group) = self.groups.get_mut(index) {
                    group.styles.extend_from_slice(styles);
                }
            }
        }
    }

    fn compile_styles(&mut self) {
        for entity in &mut self.entities {
            compile(
                &self.definitions,
                &entity.classes,
                &mut entity.styles,
                &mut entity.text_styles,
            );
        }
        for group in &mut self.groups {
            compile(
                &self.definitions,
                &group.classes,
                &mut group.styles,
                &mut group.text_styles,
            );
        }
    }
}

impl Entity {
    fn apply_alias(&mut self, alias: Option<&EntityName<'_>>) {
        let Some(alias) = alias.filter(|alias| !alias.name.is_empty() && self.alias.is_none())
        else {
            return;
        };
        self.alias = Some(alias.name.as_ref().into());
        self.alias_span = Some(alias.span);
        self.label = alias.name.as_ref().into();
    }

    pub fn table_rows(&self) -> Vec<Vec<String>> {
        self.attributes
            .iter()
            .map(|attribute| {
                vec![
                    decode_label(&attribute.attribute_type),
                    decode_label(&attribute.name),
                    attribute.keys.join(","),
                    decode_label(&attribute.comment),
                ]
            })
            .collect()
    }

    pub fn display_name(&self) -> String {
        decode_label(&self.label)
    }
}

fn append_unique(members: &mut Vec<Target>, targets: Vec<Target>) {
    for target in targets {
        if !members.contains(&target) {
            members.push(target);
        }
    }
}

impl Attribute {
    fn from_ast(value: &crate::syntax::er::ast::Attribute<'_>) -> Self {
        let nullable = value.attribute_type.question.is_some();
        let mut attribute_type = value.attribute_type.word.text.trim_matches('`').to_owned();
        if nullable {
            attribute_type.push('?');
        }
        Self {
            span: value.span,
            attribute_type,
            type_span: value.attribute_type.span,
            name: value.name.word.text.trim_matches('`').into(),
            name_span: value.name.span,
            keys: value.keys.as_ref().map_or_else(Vec::new, |keys| {
                keys.keys.iter().map(|key| key.value.into()).collect()
            }),
            key_spans: value.keys.as_ref().map_or_else(Vec::new, |keys| {
                keys.keys.iter().map(|key| key.span).collect()
            }),
            comment: value
                .comment
                .as_ref()
                .map_or("", |comment| comment.text.as_ref())
                .into(),
            comment_span: value.comment.as_ref().map(|comment| comment.span),
            nullable,
        }
    }
}

fn cardinality(kind: CardinalityKind) -> &'static str {
    match kind {
        CardinalityKind::OnlyOne => "only_one",
        CardinalityKind::ZeroOrOne => "zero_or_one",
        CardinalityKind::OneOrMore => "one_or_more",
        CardinalityKind::ZeroOrMore => "zero_or_more",
        CardinalityKind::MdParent => "",
    }
}

fn style_values(styles: &StylesOpt<'_>) -> Vec<String> {
    styles
        .styles
        .iter()
        .map(|style| {
            style
                .components
                .iter()
                .map(|part| part.token.text.as_ref())
                .collect::<String>()
        })
        .collect()
}

fn text_styles(styles: &[String]) -> Vec<String> {
    styles
        .iter()
        .filter(|style| style.contains("color"))
        .map(|style| style.replace("fill", "bgFill"))
        .collect()
}

fn compile(
    definitions: &[ClassDefinition],
    classes: &[String],
    styles: &mut Vec<String>,
    texts: &mut Vec<String>,
) {
    for class in classes {
        if let Some(definition) = definitions.iter().find(|row| row.name == *class) {
            styles.extend_from_slice(&definition.styles);
            texts.extend_from_slice(&definition.text_styles);
        }
    }
}

#[cfg(test)]
mod tests;
