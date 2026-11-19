use crate::{Diagnostic, DiagramKind, Position, Severity, Span};
use std::borrow::Cow;

/// Immutable parsed source. Valid UTF-8 borrows the caller's text.
#[derive(Debug)]
pub struct Document<'src> {
    source: Cow<'src, str>,
    kind: Option<DiagramKind>,
    diagnostics: Vec<Diagnostic>,
    starts: Vec<usize>,
    look: crate::look::Look,
    pub(crate) model: Option<crate::model::Resolved>,
}

pub fn parse(source: &str) -> Document<'_> {
    parse_bytes(source.as_bytes())
}

pub fn parse_bytes(bytes: &[u8]) -> Document<'_> {
    let (source, bad) = crate::source::repair_utf8(bytes);
    let prep = crate::syntax::preprocess::preprocess(&source);
    let detection = crate::syntax::detect::detect(&source, &prep.removed);
    let mut diagnostics = prep.diagnostics;
    diagnostics.extend(detection.diagnostics);
    let (model, resolved) = detection.kind.map_or_else(
        || (None, Vec::new()),
        |kind| crate::model::Resolved::parse(kind, &source, &prep.removed),
    );
    diagnostics.extend(resolved);
    let layers: Vec<&crate::syntax::config_value::ConfigValue> = prep
        .frontmatter
        .iter()
        .filter_map(|f| f.config.as_ref())
        .chain(prep.init_config.iter())
        .collect();
    let (look, look_diagnostics) = crate::look::Look::read(&layers);
    diagnostics.extend(look_diagnostics);
    if let Some(start) = bad {
        diagnostics.push(Diagnostic {
            code: "source/invalid-utf8",
            severity: Severity::Error,
            message: format!("invalid UTF-8 at byte {start}"),
            span: Span {
                start,
                end: start + '\u{fffd}'.len_utf8(),
            },
            related: Vec::new(),
            help: "Save the source as UTF-8.".into(),
            fixes: Vec::new(),
        });
    }
    crate::diag::sort(&mut diagnostics);
    let starts = crate::source::line_starts(&source);
    Document {
        source,
        kind: detection.kind,
        diagnostics,
        starts,
        look,
        model,
    }
}

impl Document<'_> {
    pub fn resolved(&self) -> Option<&crate::model::Resolved> {
        self.model.as_ref()
    }
    pub fn into_resolved(self) -> Option<crate::model::Resolved> {
        self.model
    }
    pub fn look(&self) -> crate::look::Look {
        self.look
    }
    pub fn source(&self) -> &str {
        &self.source
    }
    pub fn kind(&self) -> Option<DiagramKind> {
        self.kind
    }
    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }
    pub fn has_errors(&self) -> bool {
        self.diagnostics
            .iter()
            .any(|d| d.severity == Severity::Error)
    }
    pub fn position(&self, offset: usize) -> Position {
        crate::source::line_position(&self.source, &self.starts, offset)
    }
}
