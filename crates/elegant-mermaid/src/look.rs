use crate::diag::{Diagnostic, Severity};
use crate::syntax::config_value::{ConfigValue, Entry};

const SEED_KEY: &str = "handDrawnSeed";
const LOOK_KEY: &str = "look";

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum LookKind {
    #[default]
    Classic,
    HandDrawn,
    Neo,
}

impl LookKind {
    fn from_name(name: &str) -> Option<LookKind> {
        match name {
            "classic" => Some(LookKind::Classic),
            "handDrawn" => Some(LookKind::HandDrawn),
            "neo" => Some(LookKind::Neo),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Look {
    pub kind: LookKind,
    pub seed: u32,
}

impl Look {
    /// Overlay look fields from a complete configuration document.
    ///
    /// Every supported field is validated at this boundary, including font and
    /// resource-limit fields. Malformed configuration returns `InvalidConfig`.
    pub fn with_config(self, text: &str) -> Result<Look, crate::error::RenderError> {
        crate::config::look_with(self, Some(text))
    }

    pub fn read(layers: &[&ConfigValue]) -> (Look, Vec<Diagnostic>) {
        let mut look = Look::default();
        let mut diagnostics = Vec::new();
        for layer in layers {
            look = look.overlay(layer, &mut diagnostics);
        }
        (look, diagnostics)
    }

    pub fn overlay(mut self, layer: &ConfigValue, diagnostics: &mut Vec<Diagnostic>) -> Look {
        let ConfigValue::Mapping(entries) = layer else {
            return self;
        };
        for entry in entries {
            match entry.key.as_str() {
                LOOK_KEY => {
                    if let ConfigValue::String(name) = &entry.value
                        && let Some(kind) = LookKind::from_name(name)
                    {
                        self.kind = kind;
                    }
                }
                SEED_KEY => match seed(&entry.value) {
                    Some(value) => self.seed = value,
                    None => diagnostics.push(malformed(entry)),
                },
                _ => {}
            }
        }
        self
    }
}

fn seed(value: &ConfigValue) -> Option<u32> {
    let ConfigValue::Integer(text) = value else {
        return None;
    };
    text.parse::<u64>()
        .ok()
        .and_then(|value| u32::try_from(value).ok())
}

pub(crate) fn malformed(entry: &Entry) -> Diagnostic {
    let shown = match &entry.value {
        ConfigValue::Null => "null".to_owned(),
        ConfigValue::Bool(value) => value.to_string(),
        ConfigValue::Integer(text) | ConfigValue::Decimal(text) | ConfigValue::String(text) => {
            text.clone()
        }
        ConfigValue::Sequence(_) => "[...]".to_owned(),
        ConfigValue::Mapping(_) => "{...}".to_owned(),
    };
    Diagnostic {
        code: "config/malformed",
        severity: Severity::Error,
        message: format!("invalid config value {shown} for {}", entry.key),
        span: entry.key_span,
        related: Vec::new(),
        help: "Write a value that the config key accepts.".into(),
        fixes: Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::{Look, LookKind};
    use crate::syntax::config_value::{ConfigValue, parse_config_yaml};

    fn value(text: &str) -> ConfigValue {
        let (value, parse) = parse_config_yaml(text, 0, text.len());
        assert!(parse.is_empty(), "{parse:?}");
        value
    }

    fn read(text: &str) -> (Look, usize) {
        let value = value(text);
        let (look, diagnostics) = Look::read(&[&value]);
        (look, diagnostics.len())
    }

    fn look(kind: LookKind, seed: u32) -> Look {
        Look { kind, seed }
    }

    #[test]
    fn look_kinds_and_seed_resolve() {
        assert_eq!(read("look: neo\n"), (look(LookKind::Neo, 0), 0));
        assert_eq!(
            read("look: handDrawn\nhandDrawnSeed: 7\n"),
            (look(LookKind::HandDrawn, 7), 0)
        );
        assert_eq!(
            read("handDrawnSeed: 4294967295\n"),
            (look(LookKind::Classic, u32::MAX), 0)
        );
        assert_eq!(read("look: other\n"), (Look::default(), 0));
    }

    #[test]
    fn invalid_seed_values_are_malformed() {
        for text in [
            "handDrawnSeed: 4294967296\n",
            "handDrawnSeed: -1\n",
            "handDrawnSeed: 1.5\n",
            "handDrawnSeed: abc\n",
            "handDrawnSeed: true\n",
        ] {
            let (resolved, errors) = read(text);
            assert_eq!(resolved, Look::default(), "{text}");
            assert_eq!(errors, 1, "{text}");
        }
    }

    #[test]
    fn later_layers_replace_earlier_layers() {
        let first = value("look: neo\nhandDrawnSeed: 3\n");
        let second = value("look: handDrawn\n");
        let (resolved, diagnostics) = Look::read(&[&first, &second]);
        assert!(diagnostics.is_empty());
        assert_eq!(resolved, look(LookKind::HandDrawn, 3));
    }
}
