use crate::error::RenderError;
use crate::look::Look;
use crate::syntax::config_value::{ConfigValue, parse_yaml_doc};

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
    let Some(text) = text else {
        return Ok(base);
    };
    let value = parse_text(text)?;
    let mut diagnostics = Vec::new();
    let look = base.overlay(&value, &mut diagnostics);
    if diagnostics.is_empty() {
        Ok(look)
    } else {
        Err(RenderError::InvalidConfig {
            errors: diagnostics.len(),
        })
    }
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
        assert!(parse_text("- a\n").is_err());
        assert!(parse_text("").is_ok());
        assert!(parse_text("null").is_err());
    }
}
