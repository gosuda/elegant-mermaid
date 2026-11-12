pub mod class;
pub mod flowchart;

#[derive(Debug)]
pub enum Resolved {
    Flowchart(flowchart::Model),
    Class(class::Model),
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
        }
    }

    pub fn accessibility(&self) -> (&str, &str, &'static str) {
        match self {
            Self::Flowchart(model) => (&model.acc_title, &model.acc_descr, "flowchart"),
            Self::Class(model) => (&model.acc_title, &model.acc_descr, "class"),
        }
    }
}
