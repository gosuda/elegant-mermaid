use super::*;

impl Model {
    pub(super) fn directive(&mut self, statement: &Statement<'_>) {
        match &statement.kind {
            StatementKind::ClassDef(value) => self.class_defs.push(ClassDefinition {
                id: id_text(&value.id),
                styles: styles(&value.styles),
                span: value.span,
            }),
            StatementKind::Class(value) => {
                for id in id_text(&value.targets).split(',').map(str::trim) {
                    if let Some(appearance) = self.appearance(id) {
                        appearance.classes.push(id_text(&value.class));
                    }
                }
            }
            StatementKind::Style(value) => {
                for id in id_text(&value.targets).split(',').map(str::trim) {
                    if let Some(appearance) = self.appearance(id) {
                        appearance.styles.extend(styles(&value.styles));
                    }
                }
            }
            StatementKind::LinkStyle(value) => self.link_style(value),
            StatementKind::Click(value) => self.click(value),
            _ => {}
        }
    }
    pub(super) fn appearance(&mut self, id: &str) -> Option<&mut Appearance> {
        if let Some(node) = self.nodes.iter_mut().find(|n| n.id == id) {
            return Some(&mut node.appearance);
        }
        if let Some(group) = self.groups.iter_mut().find(|g| g.id == id) {
            return Some(&mut group.appearance);
        }
        self.edges
            .iter_mut()
            .find(|e| e.id == id)
            .map(|e| &mut e.appearance)
    }
    fn link_style(&mut self, value: &LinkStyleStatement<'_>) {
        let appearance = value.styles.as_ref().map_or_else(Vec::new, styles);
        let interpolation = value
            .interpolation
            .as_ref()
            .map(|v| tokens(v.tokens.iter().map(|t| &*t.text)));
        if value.default.is_some() {
            self.edge_defaults(&appearance, interpolation.as_deref());
        }
        for token in value.indices.iter().flat_map(|list| &list.indices) {
            let index = token.text.parse::<usize>().unwrap_or(usize::MAX);
            let Some(edge) = self.edges.get_mut(index) else {
                let last = self.edges.len().saturating_sub(1);
                self.diagnostics.push(report(
                    "agentflow/link-style-index",
                    format!("linkStyle index {} is outside 0..{last}", token.text),
                    token.span,
                ));
                continue;
            };
            edge.appearance.styles.extend(appearance.clone());
            if !appearance
                .iter()
                .any(|s| s.trim_start().starts_with("fill:"))
            {
                edge.appearance.styles.push("fill:none".into());
            }
            if let Some(curve) = &interpolation {
                edge.interpolation = curve.clone();
            }
        }
    }
    fn edge_defaults(&mut self, appearance: &[String], interpolation: Option<&str>) {
        self.default_edge_styles.extend_from_slice(appearance);
        if let Some(curve) = interpolation {
            self.default_interpolation = curve.into();
        }
        for edge in &mut self.edges {
            edge.appearance.styles.extend_from_slice(appearance);
            if let Some(curve) = interpolation {
                edge.interpolation = curve.into();
            }
        }
    }
    fn click(&mut self, value: &ClickStatement<'_>) {
        if let Some(url) = &value.url {
            let safe = url.text.trim().split_once(':').is_some_and(|(scheme, _)| {
                matches!(
                    scheme.to_ascii_lowercase().as_str(),
                    "http" | "https" | "mailto"
                )
            });
            if !safe {
                self.diagnostics.push(report(
                    "interaction/unsafe-url",
                    "link URL is not allowed".into(),
                    url.span,
                ));
            }
        }
        if let Some(callback) = &value.callback {
            self.diagnostics.push(report(
                "interaction/callback-ignored",
                format!(
                    "callback {} is ignored",
                    tokens(callback.tokens.iter().map(|t| &*t.text))
                ),
                callback.span,
            ));
        }
        self.links.push(Interaction {
            id: value.id.text.to_string(),
            url: value.url.as_ref().map(|v| v.text.to_string()),
            callback: value
                .callback
                .as_ref()
                .map(|v| tokens(v.tokens.iter().map(|t| &*t.text))),
            arguments: value.arguments.as_ref().map(|v| v.text.to_string()),
            tooltip: value.tooltip.as_ref().map(|v| v.text.to_string()),
            target: value.target.as_ref().map(|v| v.text.to_string()),
            span: value.span,
        });
    }
    pub(super) fn finish_classes(&mut self) {
        let definitions = &self.class_defs;
        for appearance in self
            .nodes
            .iter_mut()
            .map(|n| &mut n.appearance)
            .chain(self.groups.iter_mut().map(|g| &mut g.appearance))
            .chain(self.edges.iter_mut().map(|e| &mut e.appearance))
        {
            let mut applied = Vec::new();
            for definition in definitions {
                if definition
                    .id
                    .split(',')
                    .any(|id| id == "default" || appearance.classes.iter().any(|class| class == id))
                {
                    applied.extend(definition.styles.clone());
                }
            }
            applied.append(&mut appearance.styles);
            appearance.styles = applied;
        }
    }
}
