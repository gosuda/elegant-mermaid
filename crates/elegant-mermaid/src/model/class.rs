use crate::{
    diag::Diagnostic,
    source::Span,
    syntax::class::{ast::*, diagnostic},
};

#[derive(Debug, Clone, Default)]
pub struct Model {
    pub classes: Vec<Class>,
    pub namespaces: Vec<Namespace>,
    pub relations: Vec<Relation>,
    pub notes: Vec<Note>,
    pub direction: String,
    pub acc_title: String,
    pub acc_descr: String,
    pub definitions: Vec<(String, String)>,
    interfaces: usize,
}
#[derive(Debug, Clone)]
pub struct Class {
    pub id: String,
    pub label: String,
    pub generic: String,
    pub span: Span,
    pub parent: String,
    pub css_classes: Vec<String>,
    pub annotations: Vec<String>,
    pub attributes: Vec<Member>,
    pub methods: Vec<Member>,
    pub styles: Vec<String>,
    pub interaction: Vec<String>,
    pub interface_owner: String,
}
#[derive(Debug, Clone)]
pub struct Member {
    pub text: String,
    pub span: Span,
    pub visibility: String,
    pub is_static: bool,
    pub is_abstract: bool,
}
#[derive(Debug, Clone)]
pub struct Namespace {
    pub id: String,
    pub label: String,
    pub parent: String,
    pub explicit: bool,
}
#[derive(Debug, Clone)]
pub struct Note {
    pub id: String,
    pub target: String,
    pub text: String,
    pub parent: String,
    pub span: Span,
}
#[derive(Debug, Clone)]
pub struct Relation {
    pub from: String,
    pub to: String,
    pub span: Span,
    pub from_span: Span,
    pub to_span: Span,
    pub marker_start: String,
    pub marker_end: String,
    pub multiplicity_start: Option<String>,
    pub multiplicity_end: Option<String>,
    pub dashed: bool,
    pub label: String,
}

pub fn resolve(_source: &str, document: &Start<'_>) -> (Model, Vec<Diagnostic>) {
    let mut model = Model {
        direction: "TB".into(),
        ..Model::default()
    };
    let mut diagnostics = Vec::new();
    model.statements(&document.statements, "", &mut diagnostics);
    (model, diagnostics)
}

impl Model {
    fn ensure(&mut self, name: &ClassName<'_>) -> usize {
        if let Some(index) = self.classes.iter().position(|class| class.id == name.value) {
            return index;
        }
        let index = self.classes.len();
        self.classes.push(Class {
            id: name.value.clone(),
            label: name.value.clone(),
            generic: name.generic.clone(),
            span: name.span,
            parent: String::new(),
            css_classes: vec!["default".into()],
            annotations: Vec::new(),
            attributes: Vec::new(),
            methods: Vec::new(),
            styles: Vec::new(),
            interaction: Vec::new(),
            interface_owner: String::new(),
        });
        index
    }
    fn statements(
        &mut self,
        statements: &[Statement<'_>],
        parent: &str,
        diagnostics: &mut Vec<Diagnostic>,
    ) {
        for statement in statements {
            self.statement(statement, parent, diagnostics);
        }
    }
    fn statement(
        &mut self,
        statement: &Statement<'_>,
        parent: &str,
        diagnostics: &mut Vec<Diagnostic>,
    ) {
        match statement {
            Statement::Class(class) => self.class(class, parent),
            Statement::Namespace(namespace) => self.namespace(namespace, parent, diagnostics),
            Statement::Member {
                name,
                member: Some(member),
            } => {
                let index = self.ensure(name);
                self.classes[index].add_member(member);
            }
            Statement::Member { member: None, .. } => {}
            Statement::Relation(relation) => self.relation(relation),
            Statement::Annotation { name, annotation } => {
                self.annotation(name, annotation, diagnostics)
            }
            Statement::Note { span, target, text } => {
                self.note(*span, target.as_ref(), text, parent)
            }
            Statement::Direction(direction) => self.direction = (*direction).into(),
            Statement::Accessibility { title, text } => {
                if *title {
                    self.acc_title = text.trim().into();
                } else {
                    self.acc_descr = text.trim().into();
                }
            }
            _ => self.metadata(statement),
        }
    }
    fn class(&mut self, statement: &ClassStatement<'_>, parent: &str) {
        let index = self.ensure(&statement.name);
        let class = &mut self.classes[index];
        if let Some(label) = statement.label {
            class.label = label.into();
        }
        class.parent = parent.into();
        if let Some(css) = statement.css_class {
            class.css_classes.push(css.into());
        }
        if let Some(annotation) = &statement.annotation {
            class.annotations.push(annotation.clone());
        }
        for member in &statement.members {
            class.add_member(member);
        }
    }
    fn annotation(
        &mut self,
        name: &ClassName<'_>,
        annotation: &str,
        diagnostics: &mut Vec<Diagnostic>,
    ) {
        if let Some(class) = self.classes.iter_mut().find(|class| class.id == name.value) {
            class.annotations.push(annotation.into());
        } else {
            diagnostics.push(diagnostic(
                "class/annotation-target-unknown",
                format!("annotation references unknown class {}", name.value),
                name.span,
            ));
        }
    }
    fn namespace(
        &mut self,
        statement: &NamespaceStatement<'_>,
        parent: &str,
        diagnostics: &mut Vec<Diagnostic>,
    ) {
        let qualified = if parent.is_empty() {
            statement.name.value.clone()
        } else {
            format!("{parent}.{}", statement.name.value)
        };
        let mut id = String::new();
        let mut ancestor = String::new();
        for segment in qualified.split('.') {
            if !id.is_empty() {
                id.push('.');
            }
            id.push_str(segment);
            if !self.namespaces.iter().any(|namespace| namespace.id == id) {
                self.namespaces.push(Namespace {
                    id: id.clone(),
                    label: segment.into(),
                    parent: ancestor,
                    explicit: false,
                });
            }
            ancestor = id.clone();
        }
        if let Some(namespace) = self
            .namespaces
            .iter_mut()
            .find(|namespace| namespace.id == qualified)
        {
            namespace.explicit = true;
            if let Some(label) = statement.label.filter(|s| !s.is_empty()) {
                namespace.label = label.into();
            }
        }
        self.statements(&statement.children, &qualified, diagnostics);
    }
    fn note(&mut self, span: Span, target: Option<&ClassName<'_>>, text: &str, parent: &str) {
        let target = target
            .filter(|name| self.classes.iter().any(|class| class.id == name.value))
            .map_or_else(String::new, |name| name.value.clone());
        self.notes.push(Note {
            id: format!("note{}", self.notes.len()),
            target,
            text: text.into(),
            parent: parent.into(),
            span,
        });
    }
    fn relation(&mut self, relation: &RelationStatement<'_>) {
        let mut from = relation.from.clone();
        let mut to = relation.to.clone();
        if relation.marker_start == Some("lollipop") && relation.marker_end.is_none() {
            from = self.interface(&from, &to);
        }
        if relation.marker_end == Some("lollipop") && relation.marker_start.is_none() {
            to = self.interface(&to, &from);
        }
        self.ensure(&from);
        self.ensure(&to);
        self.relations.push(Relation {
            from: from.value,
            to: to.value,
            span: relation.span,
            from_span: relation.from.span,
            to_span: relation.to.span,
            marker_start: relation.marker_start.unwrap_or("none").into(),
            marker_end: relation.marker_end.unwrap_or("none").into(),
            multiplicity_start: relation.multiplicity_start.map(|s| s.trim().into()),
            multiplicity_end: relation.multiplicity_end.map(|s| s.trim().into()),
            dashed: relation.dashed,
            label: relation.label.unwrap_or("").trim().into(),
        });
    }
    fn interface<'a>(&mut self, name: &ClassName<'a>, owner: &ClassName<'_>) -> ClassName<'a> {
        let mut interface = name.clone();
        interface.value = format!("interface{}", self.interfaces);
        self.interfaces += 1;
        let index = self.ensure(&interface);
        self.classes[index].label = name.value.clone();
        self.classes[index].interface_owner = owner.value.clone();
        interface
    }
    fn metadata(&mut self, statement: &Statement<'_>) {
        match statement {
            Statement::Style { target, text } => {
                for class in self.classes.iter_mut().filter(|class| class.id == *target) {
                    class.styles.push((*text).into());
                }
            }
            Statement::CssClass { target, name } => {
                for class in self
                    .classes
                    .iter_mut()
                    .filter(|class| target.split(',').any(|id| id.trim() == class.id))
                {
                    class.css_classes.push((*name).into());
                }
            }
            Statement::ClassDef { target, text } => {
                self.definitions.push((target.clone(), (*text).into()));
                for class in self
                    .classes
                    .iter_mut()
                    .filter(|class| class.css_classes.iter().any(|name| name.contains(target)))
                {
                    class.styles.push((*text).into());
                }
            }
            Statement::Click { target, values } => {
                for class in self.classes.iter_mut().filter(|class| class.id == *target) {
                    class
                        .interaction
                        .extend(values.iter().map(|value| (*value).into()));
                }
            }
            _ => {}
        }
    }
}

impl Class {
    fn add_member(&mut self, member: &MemberStatement<'_>) {
        let text = member.text.trim();
        if text.is_empty() {
            return;
        }
        if let Some(annotation) = text
            .strip_prefix("<<")
            .and_then(|text| text.strip_suffix(">>"))
        {
            self.annotations.push(annotation.into());
            return;
        }
        let parsed = Member::parse(text, member.span);
        if text.find(')').is_some_and(|index| index > 0) {
            self.methods.push(parsed);
        } else {
            self.attributes.push(parsed);
        }
    }
    pub fn rows(&self) -> Vec<Vec<String>> {
        let mut heading = self
            .annotations
            .iter()
            .map(|annotation| format!("«{annotation}»"))
            .collect::<Vec<_>>();
        heading.push(if self.generic.is_empty() {
            self.label.clone()
        } else {
            format!("{}<{}>", self.label, self.generic)
        });
        vec![
            heading,
            self.attributes
                .iter()
                .map(|member| member.text.clone())
                .collect(),
            self.methods
                .iter()
                .map(|member| member.text.clone())
                .collect(),
        ]
    }
}

impl Member {
    fn parse(text: &str, span: Span) -> Self {
        let visibility = text
            .chars()
            .next()
            .filter(|c| matches!(c, '#' | '+' | '~' | '-'))
            .map_or_else(String::new, |c| c.to_string());
        let mut is_static = text.ends_with('$');
        let mut is_abstract = text.ends_with('*');
        let mut display = text.trim_end_matches(['$', '*']).to_owned();
        if let Some((method, classifier)) = method_display(&display) {
            is_static |= classifier == Some('$');
            is_abstract |= classifier == Some('*');
            display = method;
        }
        let mut generic = String::new();
        let mut open = false;
        for character in display.chars() {
            if character == '~' {
                generic.push(if open { '>' } else { '<' });
                open = !open;
            } else {
                generic.push(character);
            }
        }
        display = generic;
        Self {
            text: display,
            span,
            visibility,
            is_static,
            is_abstract,
        }
    }
}

fn method_display(text: &str) -> Option<(String, Option<char>)> {
    let close = text.rfind(')')?;
    let open = text[..close].rfind('(')?;
    let parameters = text[open + 1..close].trim();
    let suffix = &text[close + 1..];
    let classifier = suffix
        .chars()
        .next()
        .filter(|character| matches!(character, '$' | '*'));
    let returns = if classifier.is_some() {
        &suffix[1..]
    } else {
        suffix
    };
    let returns = returns.trim().trim_end_matches(['$', '*']);
    let mut display = format!("{}({parameters})", &text[..open]);
    if !returns.is_empty() {
        display.push_str(" : ");
        display.push_str(returns);
    }
    Some((display, classifier))
}
