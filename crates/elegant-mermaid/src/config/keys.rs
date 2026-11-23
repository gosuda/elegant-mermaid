use crate::r#gen::configkeys::CONFIG_KEYS;
use crate::syntax::config_value::ConfigValue;
use crate::{Diagnostic, Severity};

pub(super) fn diagnostics(value: &ConfigValue) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    check(value, "", "", "", &mut diagnostics);
    diagnostics
}

fn check(
    value: &ConfigValue,
    kind: &str,
    prefix: &str,
    display: &str,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let ConfigValue::Mapping(entries) = value else {
        return;
    };
    for entry in entries {
        let key = path(prefix, &entry.key);
        let shown = path(display, &entry.key);
        let row =
            CONFIG_KEYS.binary_search_by(|row| (row.kind, row.key).cmp(&(kind, key.as_str())));
        let Ok(index) = row else {
            diagnostics.push(super::diagnostic(
                "config/unknown-key",
                Severity::Warning,
                format!("unknown config key {shown}"),
                entry.key_span,
                "Check the spelling of the key, or remove it.",
            ));
            continue;
        };
        if CONFIG_KEYS[index].class == "rejected" {
            diagnostics.push(super::diagnostic(
                "config/unsupported-key",
                Severity::Warning,
                format!("config key {shown} is not supported by this project"),
                entry.key_span,
                "Remove the key; this project cannot produce the output it asks for.",
            ));
        }
        if kind.is_empty() {
            let child_kind = key.to_ascii_lowercase();
            if CONFIG_KEYS.iter().any(|row| row.kind == child_kind) {
                check(&entry.value, &child_kind, "", &shown, diagnostics);
            }
        } else {
            let child_prefix = format!("{key}.");
            if CONFIG_KEYS
                .iter()
                .any(|row| row.kind == kind && row.key.starts_with(&child_prefix))
            {
                check(&entry.value, kind, &key, &shown, diagnostics);
            }
        }
    }
}

fn path(prefix: &str, key: &str) -> String {
    if prefix.is_empty() {
        key.into()
    } else {
        format!("{prefix}.{key}")
    }
}
