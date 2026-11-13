pub mod class;
pub mod flowchart;
pub mod state;

#[derive(Debug)]
pub enum Resolved {
    Flowchart(flowchart::Model),
    Class(class::Model),
    State(state::Model),
}

impl Resolved {
    pub fn parse(
        kind: crate::DiagramKind,
        source: &str,
        removed: &[crate::Span],
    ) -> (Option<Self>, Vec<crate::Diagnostic>) {
        match kind {
            crate::DiagramKind::Flowchart => {
                let parsed = crate::syntax::flowchart::parse(source, removed);
                let (model, mut diagnostics) = flowchart::resolve(source, &parsed.document);
                diagnostics.extend(parsed.diagnostics);
                (Some(Self::Flowchart(model)), diagnostics)
            }
            crate::DiagramKind::Class => {
                let parsed = crate::syntax::class::parse(source, removed);
                let (model, mut diagnostics) = class::resolve(source, &parsed.document);
                diagnostics.extend(parsed.diagnostics);
                (Some(Self::Class(model)), diagnostics)
            }
            crate::DiagramKind::State => {
                let parsed = crate::syntax::state::parse(source, removed);
                let (model, mut diagnostics) = state::resolve(source, &parsed.document);
                diagnostics.extend(parsed.diagnostics);
                (Some(Self::State(model)), diagnostics)
            }
            _ => (None, Vec::new()),
        }
    }

    pub fn input(
        &self,
        profile: crate::scene::Profile,
        options: crate::scene::DumpOptions,
    ) -> Result<crate::layout::input::Input, crate::geom::GeomError> {
        match self {
            Self::Flowchart(model) => Ok(crate::layout::flowchart::from_flowchart(
                model, profile, options,
            )),
            Self::Class(model) => crate::layout::class::from_class(model, profile, options),
            Self::State(model) => crate::layout::state::from_state(model, profile, options),
        }
    }

    pub fn accessibility(&self) -> (&str, &str, &'static str) {
        match self {
            Self::Flowchart(model) => (&model.acc_title, &model.acc_descr, "flowchart"),
            Self::Class(model) => (&model.acc_title, &model.acc_descr, "class"),
            Self::State(model) => (
                model
                    .acc_title
                    .as_ref()
                    .map_or("", |text| text.value.as_str()),
                model
                    .acc_descr
                    .as_ref()
                    .map_or("", |text| text.value.as_str()),
                "state",
            ),
        }
    }

    pub fn links(&self) -> Vec<crate::interaction::OwnerLink<'_>> {
        match self {
            Self::State(model) => model
                .links
                .iter()
                .filter_map(|link| {
                    crate::interaction::SafeUrl::new(&link.url.value).map(|url| {
                        crate::interaction::OwnerLink {
                            owner: &link.target,
                            url,
                            tooltip: link.tooltip.as_ref().map(|text| text.value.as_str()),
                        }
                    })
                })
                .collect(),
            Self::Flowchart(_) | Self::Class(_) => Vec::new(),
        }
    }
}
