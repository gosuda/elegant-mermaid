use super::metadata::{apply_metadata, edge_metadata};
use super::*;
impl Model {
    pub(super) fn collect(&mut self, statement: &Statement<'_>, diagnostics: &mut Vec<Diagnostic>) {
        match &statement.kind {
            StatementKind::Actor(value) => {
                for item in &value.items {
                    self.actor(item, "", diagnostics);
                }
                if let Some(relation) = &value.relation {
                    self.endpoint_declaration(&relation.endpoint, diagnostics);
                }
            }
            StatementKind::Entity(value) => {
                if value.relation.is_none() || explicit(&value.name) {
                    self.declare_entity(&value.name, "", diagnostics);
                }
                if let Some(relation) = &value.relation {
                    self.endpoint_declaration(&relation.endpoint, diagnostics);
                }
            }
            StatementKind::SystemBoundary(value) => self.boundary(value, diagnostics),
            StatementKind::Json(value) => {
                let mut node = node(&value.id, None, Kind::Json, value.span);
                node.shape = "rect".into();
                node.json = Some(json_object(&value.object));
                node.classes = classes(value.classes.as_ref());
                self.declare(node, diagnostics);
            }
            _ => {}
        }
    }
    fn endpoint_declaration(&mut self, name: &EntityName<'_>, diagnostics: &mut Vec<Diagnostic>) {
        if explicit(name) {
            self.declare_entity(name, "", diagnostics);
        }
    }
    pub(super) fn reserve_edge(
        &mut self,
        statement: &Statement<'_>,
        diagnostics: &mut Vec<Diagnostic>,
    ) {
        let tail = match &statement.kind {
            StatementKind::Actor(value) => value.relation.as_ref(),
            StatementKind::Entity(value) => value.relation.as_ref(),
            _ => None,
        };
        let Some(token) = tail.and_then(|tail| tail.id.as_ref()) else {
            return;
        };
        let earlier = self
            .nodes
            .iter()
            .find(|node| node.id == token.text)
            .map(|node| node.span)
            .or_else(|| {
                self.edge_symbols
                    .iter()
                    .find(|(id, _)| id == &*token.text)
                    .map(|(_, span)| *span)
            });
        if let Some(previous) = earlier {
            let (later, first) = if token.span.start < previous.start {
                (previous, token.span)
            } else {
                (token.span, previous)
            };
            diagnostics.push(conflict(&token.text, "duplicate symbol id", later, first));
        }
        self.edge_symbols
            .push((token.text.as_ref().into(), token.span));
    }
    fn declare(&mut self, incoming: Node, diagnostics: &mut Vec<Diagnostic>) {
        let Some(previous) = self.nodes.iter_mut().find(|node| node.id == incoming.id) else {
            self.nodes.push(incoming);
            return;
        };
        let reason = declaration_difference(previous, &incoming);
        if let Some(reason) = reason {
            diagnostics.push(conflict(&incoming.id, reason, incoming.span, previous.span));
        } else {
            append_unique(&mut previous.classes, incoming.classes);
        }
    }
    fn actor(&mut self, item: &ActorItem<'_>, parent: &str, diagnostics: &mut Vec<Diagnostic>) {
        let mut node = node(
            &item.name.id,
            item.name.label.as_ref(),
            Kind::Actor,
            item.span,
        );
        node.shape = "usecaseActor".into();
        node.parent = parent.into();
        node.classes = classes(item.classes.as_ref());
        node.stereotype = item
            .stereotype
            .as_ref()
            .map_or("", |value| value.content.text.trim())
            .into();
        apply_metadata(&mut node, item.metadata.as_ref(), diagnostics);
        self.declare(node, diagnostics);
    }
    fn declare_entity(
        &mut self,
        name: &EntityName<'_>,
        parent: &str,
        diagnostics: &mut Vec<Diagnostic>,
    ) {
        let mut node = entity(name, parent);
        apply_metadata(
            &mut node,
            name.metadata.as_ref().map(|value| &value.metadata),
            diagnostics,
        );
        self.declare(node, diagnostics);
    }
    fn boundary(&mut self, value: &SystemBoundaryStatement<'_>, diagnostics: &mut Vec<Diagnostic>) {
        let mut node = node(
            &value.name.id,
            value.name.label.as_ref(),
            Kind::Boundary,
            value.span,
        );
        node.shape = "rect".into();
        node.classes = classes(value.classes.as_ref());
        apply_metadata(&mut node, value.metadata.as_ref(), diagnostics);
        let id = node.id.clone();
        for element in &value.content.elements {
            boundary_members(&mut node.members, &element.kind);
        }
        self.declare(node, diagnostics);
        for element in &value.content.elements {
            self.boundary_element(&element.kind, &id, diagnostics);
        }
    }
    fn boundary_element(
        &mut self,
        element: &BoundaryElementKind<'_>,
        parent: &str,
        diagnostics: &mut Vec<Diagnostic>,
    ) {
        match element {
            BoundaryElementKind::Actor(value) => {
                for item in &value.items {
                    self.actor(item, parent, diagnostics);
                }
            }
            BoundaryElementKind::Entity(name, _) => self.declare_entity(name, parent, diagnostics),
            _ => {}
        }
    }
    fn occurrence(&mut self, id: &str, span: Span) {
        if let Some(node) = self.nodes.iter_mut().find(|node| node.id == id)
            && span.start < node.first_span.start
        {
            node.first_span = span;
        }
    }
    fn reference(&mut self, name: &EntityName<'_>, diagnostics: &mut Vec<Diagnostic>) -> String {
        let id = identity(&name.id);
        if !explicit(name) && name.classes.is_some() {
            diagnostics.push(diagnostic(
                "usecase/reference-class-suffix",
                format!("endpoint {id} uses classes without a declaration"),
                name.span,
            ));
        }
        if let Some(node) = self.nodes.iter_mut().find(|node| node.id == id) {
            if name.span.start < node.first_span.start {
                node.first_span = name.span;
            }
        } else if !self.edge_symbols.iter().any(|(edge, _)| edge == &id) {
            self.nodes.push(entity(name, ""));
        }
        id
    }
    pub(super) fn connect(&mut self, statement: &Statement<'_>, diagnostics: &mut Vec<Diagnostic>) {
        match &statement.kind {
            StatementKind::Actor(value) => {
                if let (Some(item), Some(tail)) = (value.items.first(), &value.relation) {
                    self.relation(identity(&item.name.id), tail, statement.span, diagnostics);
                }
            }
            StatementKind::Entity(value) => {
                if let Some(tail) = &value.relation {
                    let from = self.reference(&value.name, diagnostics);
                    self.relation(from, tail, statement.span, diagnostics);
                }
            }
            _ => {}
        }
    }
    fn relation(
        &mut self,
        from: String,
        tail: &RelationTail<'_>,
        span: Span,
        diagnostics: &mut Vec<Diagnostic>,
    ) {
        let to = self.reference(&tail.endpoint, diagnostics);
        let id = tail.id.as_ref().map_or_else(
            || {
                format!(
                    "edge-{}",
                    self.relations.iter().filter(|edge| !edge.explicit).count()
                )
            },
            |token| token.text.as_ref().into(),
        );
        if self.relations.iter().any(|edge| edge.id == id) {
            return;
        }
        let mut relation = Relation {
            id,
            explicit: tail.id.is_some(),
            from,
            to,
            kind: "association".into(),
            label: String::new(),
            marker_start: "none".into(),
            marker_end: "none".into(),
            min_length: 1,
            animate: false,
            animation: String::new(),
            span,
            classes: Vec::new(),
            styles: Vec::new(),
        };
        arrow(&mut relation, &tail.arrow.kind);
        self.relations.push(relation);
    }
    pub(super) fn configure(
        &mut self,
        source: &str,
        statement: &Statement<'_>,
        diagnostics: &mut Vec<Diagnostic>,
    ) {
        match &statement.kind {
            StatementKind::Direction(value) => {
                self.direction = if value.direction.text == "TD" {
                    "TB"
                } else {
                    value.direction.text.as_ref()
                }
                .into()
            }
            StatementKind::AccTitle(value) => self.acc_title = value.value.trim().into(),
            StatementKind::AccDescr(value) => self.acc_descr = value.value.trim().into(),
            StatementKind::MetadataAssignment(value) => self.assignment(value, diagnostics),
            StatementKind::Note(value) => self.note(value, diagnostics),
            StatementKind::ClassDef(value) => self.definition(source, value),
            StatementKind::Class(value) => {
                for target in &value.targets {
                    self.apply_classes(target, &value.classes, diagnostics);
                }
            }
            StatementKind::Style(value) => self.apply_style(source, value, diagnostics),
            _ => {}
        }
    }
    fn assignment(
        &mut self,
        value: &MetadataAssignmentStatement<'_>,
        diagnostics: &mut Vec<Diagnostic>,
    ) {
        let id = identity(&value.target.token);
        self.occurrence(&id, value.target.span);
        if let Some(node) = self.nodes.iter_mut().find(|node| node.id == id) {
            apply_metadata(node, Some(&value.metadata), diagnostics);
            return;
        }
        if let Some(edge) = self
            .relations
            .iter_mut()
            .find(|edge| edge.explicit && edge.id == id)
        {
            for property in &value.metadata.properties {
                edge_metadata(edge, property, diagnostics);
            }
            return;
        }
        diagnostics.push(unresolved("metadata", &id, value.target.span));
    }
    fn note(&mut self, value: &NoteStatement<'_>, diagnostics: &mut Vec<Diagnostic>) {
        let target = value.target.text.as_ref();
        self.occurrence(target, value.target.span);
        if !self
            .nodes
            .iter()
            .any(|node| node.id == target && matches!(node.kind, Kind::Actor | Kind::Usecase))
        {
            diagnostics.push(unresolved("note", target, value.target.span));
            return;
        }
        let mut ordinal = self.notes.len();
        let id = loop {
            let id = format!("note-{ordinal}");
            ordinal += 1;
            if !self.nodes.iter().any(|node| node.id == id)
                && !self.relations.iter().any(|edge| edge.id == id)
                && !self.notes.iter().any(|note| note.id == id)
            {
                break id;
            }
        };
        self.notes.push(Note {
            id,
            target: target.into(),
            text: value.label.text.as_ref().into(),
            span: value.span,
        });
    }
    fn definition(&mut self, source: &str, value: &ClassDefStatement<'_>) {
        let text = source
            .get(value.styles.span.start..value.styles.span.end)
            .unwrap_or("");
        for class in &value.classes {
            if let Some(existing) = self
                .definitions
                .iter_mut()
                .find(|(name, _)| name == &*class.text)
            {
                existing.1 = text.into();
            } else {
                self.definitions
                    .push((class.text.as_ref().into(), text.into()));
            }
        }
    }
    fn apply_classes(
        &mut self,
        target: &Token<'_>,
        values: &[Token<'_>],
        diagnostics: &mut Vec<Diagnostic>,
    ) {
        self.occurrence(&target.text, target.span);
        let values = || values.iter().map(|token| token.text.to_string());
        if let Some(node) = self
            .nodes
            .iter_mut()
            .find(|node| node.id == target.text && !node.generated)
        {
            append_unique(&mut node.classes, values());
            return;
        }
        if let Some(edge) = self
            .relations
            .iter_mut()
            .find(|edge| edge.explicit && edge.id == target.text)
        {
            append_unique(&mut edge.classes, values());
            return;
        }
        diagnostics.push(unresolved("class", &target.text, target.span));
    }
    fn apply_style(
        &mut self,
        source: &str,
        value: &StyleStatement<'_>,
        diagnostics: &mut Vec<Diagnostic>,
    ) {
        self.occurrence(&value.target.text, value.target.span);
        let text = source
            .get(value.styles.span.start..value.styles.span.end)
            .unwrap_or("");
        if let Some(node) = self
            .nodes
            .iter_mut()
            .find(|node| node.id == value.target.text && !node.generated)
        {
            node.styles.push(text.into());
            return;
        }
        if let Some(edge) = self
            .relations
            .iter_mut()
            .find(|edge| edge.explicit && edge.id == value.target.text)
        {
            edge.styles.push(text.into());
            return;
        }
        diagnostics.push(unresolved("style", &value.target.text, value.target.span));
    }
    pub(super) fn validate_relation(&self, edge: &Relation, diagnostics: &mut Vec<Diagnostic>) {
        let from = self.nodes.iter().find(|node| node.id == edge.from);
        let to = self.nodes.iter().find(|node| node.id == edge.to);
        let reason = relationship_error(edge, from, to);
        let Some(reason) = reason else {
            return;
        };
        let mut value = diagnostic(
            "usecase/invalid-relationship",
            format!("invalid {} relationship: {reason}", edge.kind),
            edge.span,
        );
        if let Some(node) = from.filter(|node| node.kind == Kind::Boundary).or(to) {
            value.related.push(Related {
                span: node.span,
                message: "endpoint declared here".into(),
            });
        }
        diagnostics.push(value);
    }
}
