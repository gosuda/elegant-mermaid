use std::collections::{BTreeMap, BTreeSet};

use crate::{
    diag::{Diagnostic, Severity},
    source::Span,
    syntax::state::{ast::*, lexer::Token},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Text {
    pub value: String,
    pub span: Span,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StateKind {
    Default,
    Fork,
    Join,
    Choice,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EndpointRole {
    Ordinary,
    Start,
    End,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Parent {
    State(usize),
    Region(usize),
}
#[derive(Debug, Clone)]
pub struct Occurrence {
    pub span: Span,
    pub id_span: Span,
    pub scope: usize,
    pub role: EndpointRole,
}
#[derive(Debug, Clone)]
pub struct State {
    pub id: String,
    pub id_span: Span,
    pub span: Span,
    pub kind: StateKind,
    pub descriptions: Vec<Text>,
    pub parent: Option<Parent>,
    pub scope: usize,
    pub composite: Option<usize>,
    pub classes: Vec<Text>,
    pub styles: Vec<Text>,
    pub note: Option<usize>,
    pub occurrences: Vec<Occurrence>,
}
#[derive(Debug, Clone)]
pub struct Endpoint {
    pub state: usize,
    pub span: Span,
    pub id_span: Span,
    pub scope: usize,
    pub role: EndpointRole,
}
#[derive(Debug, Clone)]
pub struct Transition {
    pub from: Endpoint,
    pub to: Endpoint,
    pub label: Option<Text>,
    pub span: Span,
    pub arrow_span: Span,
    pub scope: usize,
}
#[derive(Debug, Clone)]
pub struct Composite {
    pub state: usize,
    pub scope: usize,
    pub span: Span,
    pub open_span: Span,
    pub close_span: Span,
    pub children: Vec<usize>,
    pub regions: Vec<usize>,
}
#[derive(Debug, Clone)]
pub struct Region {
    pub id: String,
    pub parent: usize,
    pub scope: usize,
    pub span: Span,
    pub separator: Option<Span>,
    pub children: Vec<usize>,
}
#[derive(Debug, Clone)]
pub struct Scope {
    pub id: String,
    pub parent: Option<usize>,
    pub direction: String,
    pub direction_span: Option<Span>,
}
#[derive(Debug, Clone)]
pub struct Note {
    pub target: usize,
    pub position: String,
    pub text: Text,
    pub span: Span,
    pub target_span: Span,
    pub position_span: Span,
    pub scope: usize,
}
#[derive(Debug, Clone)]
pub struct ClassDefinition {
    pub id: String,
    pub id_span: Span,
    pub span: Span,
    pub styles: Vec<Text>,
    pub text_styles: Vec<Text>,
}
#[derive(Debug, Clone)]
pub struct Link {
    pub target: String,
    pub target_span: Span,
    pub url: Text,
    pub tooltip: Option<Text>,
    pub span: Span,
    pub scope: usize,
}
#[derive(Debug, Clone)]
pub struct Directive {
    pub span: Span,
    pub scope: usize,
    pub token_spans: Vec<Span>,
}
#[derive(Debug, Clone)]
pub struct StatementOccurrence {
    pub id: usize,
    pub from: usize,
    pub to: usize,
    pub label: usize,
    pub pseudostate: bool,
    pub span: Span,
    pub body: Option<Vec<StatementOccurrence>>,
    pub statement_count: usize,
}

#[derive(Debug, Clone, Default)]
pub struct Model {
    pub states: Vec<State>,
    pub composites: Vec<Composite>,
    pub regions: Vec<Region>,
    pub transitions: Vec<Transition>,
    pub notes: Vec<Note>,
    pub class_definitions: Vec<ClassDefinition>,
    pub scopes: Vec<Scope>,
    pub links: Vec<Link>,
    pub acc_title: Option<Text>,
    pub acc_descr: Option<Text>,
    pub directives: Vec<Directive>,
    pub occurrences: Vec<StatementOccurrence>,
}

pub fn resolve(_source: &str, document: &Start<'_>) -> (Model, Vec<Diagnostic>) {
    let mut resolver = Resolver {
        model: Model::default(),
        states: BTreeMap::new(),
        classes: BTreeMap::new(),
        links: BTreeMap::new(),
        memberships: BTreeSet::new(),
        divider: 0,
        interaction_diagnostics: Vec::new(),
    };
    resolver.model.scopes.push(Scope {
        id: "root".into(),
        parent: None,
        direction: "TB".into(),
        direction_span: None,
    });
    resolver.model.occurrences = occurrences(&document.document, &mut BTreeMap::new());
    resolver.document(&document.document, 0, None);
    let mut diagnostics: Vec<Diagnostic> = resolver
        .model
        .composites
        .iter()
        .filter_map(|group| {
            let state = &resolver.model.states[group.state];
            state.descriptions.get(1).map(|row| Diagnostic {
                code: "state/group-description",
                severity: Severity::Error,
                message: format!(
                    "composite state {} cannot have additional descriptions",
                    state.id
                ),
                span: row.span,
                related: Vec::new(),
                help: String::new(),
                fixes: Vec::new(),
            })
        })
        .collect();
    diagnostics.extend(resolver.interaction_diagnostics);
    (resolver.model, diagnostics)
}

struct Resolver {
    model: Model,
    states: BTreeMap<String, usize>,
    classes: BTreeMap<String, usize>,
    links: BTreeMap<String, usize>,
    memberships: BTreeSet<(Parent, usize)>,
    divider: usize,
    interaction_diagnostics: Vec<Diagnostic>,
}
impl Resolver {
    fn state(
        &mut self,
        id: &str,
        spans: (Span, Span),
        kind: StateKind,
        location: (usize, Option<Parent>),
    ) -> usize {
        let (id_span, span) = spans;
        let (scope, parent) = location;
        if let Some(&index) = self.states.get(id) {
            return index;
        }
        let index = self.model.states.len();
        self.states.insert(id.into(), index);
        self.model.states.push(State {
            id: id.into(),
            id_span,
            span,
            kind,
            descriptions: Vec::new(),
            parent,
            scope,
            composite: None,
            classes: Vec::new(),
            styles: Vec::new(),
            note: None,
            occurrences: Vec::new(),
        });
        index
    }
    fn endpoint(
        &mut self,
        id: &IdStatement<'_>,
        role: EndpointRole,
        scope: usize,
        parent: Option<Parent>,
    ) -> Endpoint {
        let raw = id.id.text.trim();
        let role = if raw == "[*]" {
            role
        } else {
            EndpointRole::Ordinary
        };
        let name = match role {
            EndpointRole::Ordinary => raw.to_owned(),
            EndpointRole::Start => format!("{}_start", self.model.scopes[scope].id),
            EndpointRole::End => format!("{}_end", self.model.scopes[scope].id),
        };
        let state = self.state(
            &name,
            (id.id.span, id.span),
            StateKind::Default,
            (scope, parent),
        );
        self.model.states[state].occurrences.push(Occurrence {
            span: id.span,
            id_span: id.id.span,
            scope,
            role,
        });
        if let Some(class) = &id.css_class {
            self.model.states[state].classes.push(text(class));
        }
        self.member(state, parent);
        Endpoint {
            state,
            span: id.span,
            id_span: id.id.span,
            scope,
            role,
        }
    }
    fn member(&mut self, state: usize, parent: Option<Parent>) {
        let Some(parent) = parent else {
            return;
        };
        self.model.states[state].parent = Some(parent);
        if !self.memberships.insert((parent, state)) {
            return;
        }
        match parent {
            Parent::State(owner) => {
                if let Some(group) = self.model.states[owner].composite {
                    self.model.composites[group].children.push(state);
                }
            }
            Parent::Region(region) => self.model.regions[region].children.push(state),
        }
    }
    fn description(&mut self, state: usize, token: &Token<'_>) {
        let value = token
            .text
            .trim()
            .strip_prefix(':')
            .unwrap_or(token.text.trim())
            .trim();
        if !value.is_empty() {
            self.model.states[state].descriptions.push(Text {
                value: value.into(),
                span: token.span,
            });
        }
    }
    fn document(&mut self, document: &Document<'_>, scope: usize, parent: Option<Parent>) {
        for line in &document.lines {
            if let Some(statement) = &line.statement {
                self.statement(statement, scope, parent);
            }
        }
    }
    fn statement(&mut self, statement: &Statement<'_>, scope: usize, parent: Option<Parent>) {
        match &statement.kind {
            StatementKind::Id { id, description } => {
                let endpoint = self.endpoint(id, EndpointRole::Start, scope, parent);
                if let Some(value) = description {
                    self.description(endpoint.state, value);
                }
            }
            StatementKind::Transition {
                from,
                arrow,
                to,
                description,
            } => {
                let from = self.endpoint(from, EndpointRole::Start, scope, parent);
                let to = self.endpoint(to, EndpointRole::End, scope, parent);
                self.model.transitions.push(Transition {
                    from,
                    to,
                    label: description.as_ref().map(|token| Text {
                        value: token.text.trim().trim_start_matches(':').trim().into(),
                        span: token.span,
                    }),
                    span: statement.span,
                    arrow_span: arrow.span,
                    scope,
                });
            }
            StatementKind::Composite { .. } => self.composite(statement, (scope, parent)),
            StatementKind::Stereotype { id, stereotype } => {
                let kind = match stereotype {
                    Stereotype::Fork => StateKind::Fork,
                    Stereotype::Join => StateKind::Join,
                    Stereotype::Choice => StateKind::Choice,
                };
                let index = self.state(
                    id.text.trim(),
                    (id.span, statement.span),
                    kind,
                    (scope, parent),
                );
                self.member(index, parent);
                self.model.states[index].occurrences.push(Occurrence {
                    span: statement.span,
                    id_span: id.span,
                    scope,
                    role: EndpointRole::Ordinary,
                });
            }
            StatementKind::Note {
                position,
                target,
                text: value,
            } => {
                let index = self.state(
                    target.text.trim(),
                    (target.span, statement.span),
                    StateKind::Default,
                    (scope, parent),
                );
                self.member(index, parent);
                let note = self.model.notes.len();
                self.model.notes.push(Note {
                    target: index,
                    position: position.value.replace('_', " "),
                    text: text(value),
                    span: statement.span,
                    target_span: target.span,
                    position_span: position.span,
                    scope,
                });
                self.model.states[index].note = Some(note);
            }
            _ => self.directive(statement, scope, parent),
        }
    }
    fn directive(&mut self, statement: &Statement<'_>, scope: usize, parent: Option<Parent>) {
        let token_spans = directive_token_spans(statement);
        self.model.directives.push(Directive {
            span: statement.span,
            scope,
            token_spans,
        });
        match &statement.kind {
            StatementKind::ClassDef(value) => self.class_definition(value),
            StatementKind::Style(value) => {
                for (id, span) in components(&value.targets) {
                    let index = self.state(
                        &id,
                        (span, statement.span),
                        StateKind::Default,
                        (scope, parent),
                    );
                    self.member(index, parent);
                    self.model.states[index].styles = styles(&value.styles);
                }
            }
            StatementKind::CssClass(value) => {
                for (id, span) in components(&value.targets) {
                    let index = self.state(
                        &id,
                        (span, statement.span),
                        StateKind::Default,
                        (scope, parent),
                    );
                    self.member(index, parent);
                    self.model.states[index].classes.push(text(&value.class));
                }
            }
            StatementKind::Direction(direction) => {
                self.model.scopes[scope].direction = direction.value.into();
                self.model.scopes[scope].direction_span = Some(direction.span);
            }
            StatementKind::Click {
                target,
                url,
                tooltip,
            } => {
                if crate::interaction::SafeUrl::new(&url.text).is_none() {
                    self.interaction_diagnostics.push(Diagnostic {
                        code: "interaction/unsafe-url",
                        severity: Severity::Warning,
                        message: "link URL is not allowed".into(),
                        span: url.span,
                        related: Vec::new(),
                        help: "Use an http, https, or mailto link.".into(),
                        fixes: Vec::new(),
                    });
                }
                let name = target.id.text.trim();
                let link = Link {
                    target: name.into(),
                    target_span: target.span,
                    url: Text {
                        value: url.text.to_string(),
                        span: url.span,
                    },
                    tooltip: tooltip.as_ref().map(|value| Text {
                        value: value.text.to_string(),
                        span: value.span,
                    }),
                    span: statement.span,
                    scope,
                };
                if let Some(&index) = self.links.get(name) {
                    self.model.links[index] = link;
                } else {
                    self.links.insert(name.into(), self.model.links.len());
                    self.model.links.push(link);
                }
            }
            StatementKind::Accessibility { title, value } => {
                if *title {
                    self.model.acc_title = Some(text(value));
                } else {
                    self.model.acc_descr = Some(text(value));
                }
            }
            _ => {}
        }
    }
    fn composite(&mut self, statement: &Statement<'_>, location: (usize, Option<Parent>)) {
        let StatementKind::Composite {
            id,
            description,
            body,
            delimiters,
        } = &statement.kind
        else {
            return;
        };
        let (scope, parent) = location;
        let span = statement.span;
        let description = description.as_ref();
        let body = body.as_ref();
        self.model.directives.push(Directive {
            span,
            scope,
            token_spans: std::iter::once(id.span)
                .chain(description.iter().map(|value| value.span))
                .chain(delimiters.iter().flat_map(|(open, close)| [*open, *close]))
                .collect(),
        });
        if description.is_none() && body.is_none() {
            return;
        }
        let mut segments = id.text.trim().split(':');
        let name = if body.is_some() {
            id.text.trim()
        } else {
            segments.next().unwrap_or("").trim()
        };
        let index = self.state(name, (id.span, span), StateKind::Default, (scope, parent));
        self.member(index, parent);
        self.model.states[index].occurrences.push(Occurrence {
            span,
            id_span: id.span,
            scope,
            role: EndpointRole::Ordinary,
        });
        if let Some(value) = description {
            self.description(index, value);
        }
        if body.is_none()
            && let Some(value) = segments.next().filter(|value| !value.trim().is_empty())
        {
            let start = id.span.start + id.text.find(':').map_or(0, |at| at + 1);
            self.model.states[index].descriptions.push(Text {
                value: value.trim().into(),
                span: Span {
                    start,
                    end: start + value.len(),
                },
            });
        }
        let Some(body) = body else {
            return;
        };
        if self.model.states[index].composite.is_some() {
            return;
        }
        let child_scope = self.model.scopes.len();
        self.model.scopes.push(Scope {
            id: name.into(),
            parent: Some(scope),
            direction: "TB".into(),
            direction_span: None,
        });
        let group = self.model.composites.len();
        let (open_span, close_span) = delimiters.unwrap_or((body.span, body.span));
        self.model.composites.push(Composite {
            state: index,
            scope: child_scope,
            span,
            open_span,
            close_span,
            children: Vec::new(),
            regions: Vec::new(),
        });
        self.model.states[index].composite = Some(group);
        let has_regions = body.lines.iter().any(|line| {
            line.statement
                .as_ref()
                .is_some_and(|s| matches!(&s.kind, StatementKind::Concurrent))
        });
        if !has_regions {
            self.document(body, child_scope, Some(Parent::State(index)));
            return;
        }
        let mut region = self.region(group, child_scope, open_span.end, None);
        for line in &body.lines {
            let Some(statement) = &line.statement else {
                continue;
            };
            if matches!(&statement.kind, StatementKind::Concurrent) {
                self.model.regions[region].span.end = statement.span.start;
                region = self.region(group, child_scope, statement.span.end, Some(statement.span));
            } else {
                self.statement(statement, child_scope, Some(Parent::Region(region)));
            }
        }
        self.model.regions[region].span.end = close_span.start;
    }
    fn region(
        &mut self,
        group: usize,
        scope: usize,
        start: usize,
        separator: Option<Span>,
    ) -> usize {
        let index = self.model.regions.len();
        let id = format!("{}_region_{}", self.model.scopes[scope].id, self.divider);
        self.divider += 1;
        self.model.regions.push(Region {
            id,
            parent: group,
            scope,
            span: Span { start, end: start },
            separator,
            children: Vec::new(),
        });
        self.model.composites[group].regions.push(index);
        index
    }
    fn class_definition(&mut self, value: &ClassDefStatement<'_>) {
        let id = value.id.text.trim();
        let index = if let Some(&index) = self.classes.get(id) {
            index
        } else {
            let index = self.model.class_definitions.len();
            self.classes.insert(id.into(), index);
            self.model.class_definitions.push(ClassDefinition {
                id: id.into(),
                id_span: value.id.span,
                span: value.span,
                styles: Vec::new(),
                text_styles: Vec::new(),
            });
            index
        };
        for component in styles(&value.styles) {
            if component.value.contains("color") {
                self.model.class_definitions[index].text_styles.push(Text {
                    value: component
                        .value
                        .replacen("fill", "bgFill", 1)
                        .replacen("color", "fill", 1),
                    span: component.span,
                });
            }
            self.model.class_definitions[index].styles.push(component);
        }
    }
}
fn text(token: &Token<'_>) -> Text {
    Text {
        value: token.text.trim().into(),
        span: token.span,
    }
}
fn components(token: &Token<'_>) -> Vec<(String, Span)> {
    let mut offset = token.span.start;
    token
        .text
        .split(',')
        .map(|component| {
            let start = offset;
            offset += component.len() + 1;
            (
                component.trim().into(),
                Span {
                    start,
                    end: start + component.len(),
                },
            )
        })
        .collect()
}
fn styles(token: &Token<'_>) -> Vec<Text> {
    components(token)
        .into_iter()
        .map(|(value, span)| Text {
            value: value.replace(';', "").trim().into(),
            span,
        })
        .collect()
}

#[cfg(test)]
#[path = "state/tests.rs"]
mod tests;

fn directive_token_spans(statement: &Statement<'_>) -> Vec<Span> {
    match &statement.kind {
        StatementKind::ClassDef(value) => vec![value.id.span, value.styles.span],
        StatementKind::Style(value) => vec![value.targets.span, value.styles.span],
        StatementKind::CssClass(value) => vec![value.targets.span, value.class.span],
        StatementKind::Direction(value) => vec![value.span],
        StatementKind::Click {
            target,
            url,
            tooltip,
        } => {
            let mut spans = vec![target.span, target.id.span, url.span];
            spans.extend(target.css_class.iter().map(|value| value.span));
            spans.extend(tooltip.iter().map(|value| value.span));
            spans
        }
        StatementKind::Accessibility { value, .. } | StatementKind::Scale(value) => {
            vec![value.span]
        }
        StatementKind::FloatingNote { text, id } => vec![text.span, id.span],
        _ => Vec::new(),
    }
}

fn occurrences<'a>(
    document: &'a Document<'_>,
    identities: &mut BTreeMap<&'a str, usize>,
) -> Vec<StatementOccurrence> {
    let mut out = Vec::new();
    for s in document
        .lines
        .iter()
        .filter_map(|line| line.statement.as_ref())
    {
        let mut occurrence = StatementOccurrence {
            id: 0,
            from: 0,
            to: 0,
            label: 0,
            pseudostate: false,
            span: s.span,
            body: None,
            statement_count: 0,
        };
        match &s.kind {
            StatementKind::Id { id, .. } => {
                occurrence.id = identity(identities, id.id.text.as_ref())
            }
            StatementKind::Composite { id, body, .. } => {
                occurrence.id = identity(identities, id.text.as_ref());
                occurrence.body = body.as_ref().map(|body| occurrences(body, identities));
                occurrence.statement_count = body.as_ref().map_or(0, |body| {
                    body.lines
                        .iter()
                        .filter(|line| line.statement.is_some())
                        .count()
                });
            }
            StatementKind::Transition {
                from,
                to,
                description,
                ..
            } => {
                occurrence.from = identity(identities, from.id.text.as_ref());
                occurrence.to = identity(identities, to.id.text.as_ref());
                occurrence.pseudostate = from.id.text == "[*]";
                occurrence.label = identity(
                    identities,
                    description.as_ref().map_or("", |token| token.text.as_ref()),
                );
            }
            _ => continue,
        }
        out.push(occurrence);
    }
    out
}

fn identity<'a>(identities: &mut BTreeMap<&'a str, usize>, text: &'a str) -> usize {
    let next = identities.len() + 1;
    *identities.entry(text).or_insert(next)
}
