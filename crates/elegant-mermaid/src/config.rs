use crate::error::RenderError;
use crate::look::Look;
use crate::syntax::config_value::{ConfigValue, parse_yaml_doc};
use crate::{Diagnostic, Severity, Span};

mod keys;

/// Shared source limits and rendering choices after applying config layers.
///
/// Config layers override fields independently. A configuration belongs to a
/// parse or render call and never changes the parsed document it was derived from.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EffectiveConfig {
    look: Look,
    max_text_size: u32,
    max_edges: u32,
    font_family: String,
    font_span: Span,
    site_diagnostics: Vec<Diagnostic>,
}

impl Default for EffectiveConfig {
    fn default() -> Self {
        Self {
            look: Look::default(),
            max_text_size: 50_000,
            max_edges: 500,
            font_family: String::new(),
            font_span: Span { start: 0, end: 0 },
            site_diagnostics: Vec::new(),
        }
    }
}

impl EffectiveConfig {
    /// Resolve source layers in increasing precedence and keep every invalid entry.
    pub fn read(layers: &[&ConfigValue]) -> (Self, Vec<Diagnostic>) {
        let mut config = Self::default();
        let mut diagnostics = Vec::new();
        for layer in layers {
            config.overlay(layer, &mut diagnostics);
        }
        (config, diagnostics)
    }

    /// Apply an optional layout config without modifying the source configuration.
    pub fn with_text(&self, text: Option<&str>) -> Result<Self, RenderError> {
        let Some(text) = text else {
            return Ok(self.clone());
        };
        let value = parse_text(text)?;
        let mut config = self.clone();
        let mut diagnostics = Vec::new();
        config.overlay(&value, &mut diagnostics);
        let errors = diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.severity == Severity::Error)
            .count();
        if errors != 0 {
            return Err(RenderError::InvalidConfig { errors });
        }
        if let ConfigValue::Mapping(entries) = &value
            && entries.iter().any(|entry| entry.key == "fontFamily")
        {
            config.font_span = Span { start: 0, end: 0 };
        }
        for diagnostic in &mut diagnostics {
            diagnostic.span = Span { start: 0, end: 0 };
        }
        config.site_diagnostics = diagnostics;
        Ok(config)
    }

    pub fn look(&self) -> Look {
        self.look
    }

    pub fn font_family(&self) -> &str {
        &self.font_family
    }

    /// Add effective shared layout keys to the canonical dump options.
    pub fn apply_to(&self, options: &mut crate::scene::DumpOptions) {
        if self.font_family.is_empty() {
            options.config.remove("fontFamily");
        } else {
            options.config.insert(
                "fontFamily".into(),
                crate::scene::DumpValue::String(self.font_family.clone()),
            );
        }
    }

    fn overlay(&mut self, value: &ConfigValue, diagnostics: &mut Vec<Diagnostic>) {
        diagnostics.extend(keys::diagnostics(value));
        self.look = self.look.overlay(value, diagnostics);
        let ConfigValue::Mapping(entries) = value else {
            return;
        };
        for entry in entries {
            match entry.key.as_str() {
                "maxTextSize" => match cap(&entry.value) {
                    Some(value) => self.max_text_size = value,
                    None => diagnostics.push(crate::look::malformed(entry)),
                },
                "maxEdges" => match cap(&entry.value) {
                    Some(value) => self.max_edges = value,
                    None => diagnostics.push(crate::look::malformed(entry)),
                },
                "fontFamily" => match &entry.value {
                    ConfigValue::String(value) => {
                        self.font_family.clone_from(value);
                        self.font_span = entry.key_span;
                    }
                    _ => diagnostics.push(crate::look::malformed(entry)),
                },
                _ => {}
            }
        }
    }

    pub(crate) fn diagnostics(&self, source_len: usize, edge_spans: &[Span]) -> Vec<Diagnostic> {
        let mut diagnostics = self.site_diagnostics.clone();
        let limit = self.max_text_size as usize;
        if source_len > limit {
            diagnostics.push(diagnostic(
                "limit/max-text-size",
                Severity::Error,
                format!("source has {source_len} bytes; the limit is {limit} bytes"),
                Span {
                    start: limit,
                    end: source_len,
                },
                "Shorten the source, or raise maxTextSize.",
            ));
        }
        let limit = self.max_edges as usize;
        if let Some(span) = edge_spans.get(limit) {
            diagnostics.push(diagnostic(
                "limit/max-edges",
                Severity::Error,
                format!(
                    "diagram has {} edges; the limit is {limit}",
                    edge_spans.len()
                ),
                *span,
                "Reduce the number of edges, or raise maxEdges.",
            ));
        }
        if !self.font_family.is_empty() {
            diagnostics.push(diagnostic(
                "config/font-metrics-approximate",
                Severity::Info,
                format!(
                    "text width is measured with Inter; fontFamily is {}",
                    self.font_family
                ),
                self.font_span,
                "Text widths may differ from the font named in fontFamily.",
            ));
        }
        diagnostics
    }
}

fn cap(value: &ConfigValue) -> Option<u32> {
    let ConfigValue::Integer(text) = value else {
        return None;
    };
    text.parse::<i32>()
        .ok()
        .and_then(|value| u32::try_from(value).ok())
}

fn diagnostic(
    code: &'static str,
    severity: Severity,
    message: String,
    span: Span,
    help: &str,
) -> Diagnostic {
    Diagnostic {
        code,
        severity,
        message,
        span,
        related: Vec::new(),
        help: help.into(),
        fixes: Vec::new(),
    }
}

pub(crate) fn parse_text(text: &str) -> Result<ConfigValue, RenderError> {
    let parsed = parse_yaml_doc(text, 0, text.len());
    if parsed.stop {
        return Err(RenderError::InvalidConfig { errors: 1 });
    }
    if !parsed.diagnostics.is_empty() {
        return Err(RenderError::InvalidConfig {
            errors: parsed.diagnostics.len(),
        });
    }
    if !matches!(parsed.value, ConfigValue::Mapping(_)) {
        return Err(RenderError::InvalidConfig { errors: 1 });
    }
    Ok(parsed.value)
}

pub(crate) fn look_with(base: Look, text: Option<&str>) -> Result<Look, RenderError> {
    EffectiveConfig {
        look: base,
        ..EffectiveConfig::default()
    }
    .with_text(text)
    .map(|config| config.look)
}

#[cfg(test)]
mod tests {
    use super::{look_with, parse_text};
    use crate::look::{Look, LookKind};

    #[test]
    fn options_config_overrides_document_look_and_rejects_bad_seed() {
        let base = Look {
            kind: LookKind::Neo,
            seed: 1,
        };
        assert_eq!(look_with(base, None), Ok(base));
        assert_eq!(
            look_with(base, Some("look: handDrawn\nhandDrawnSeed: 9\n")),
            Ok(Look {
                kind: LookKind::HandDrawn,
                seed: 9
            })
        );
        assert!(look_with(base, Some("handDrawnSeed: -3\n")).is_err());
        for config in ["fontFamily: 1\n", "maxEdges: -1\n", "maxTextSize: false\n"] {
            assert!(matches!(
                base.with_config(config),
                Err(crate::error::RenderError::InvalidConfig { errors: 1 })
            ));
        }
        assert!(parse_text("- a\n").is_err());
        assert!(parse_text("").is_ok());
        assert!(parse_text("null").is_err());
    }
}
