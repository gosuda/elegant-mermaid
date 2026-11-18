use super::*;
use crate::syntax::config_value::parse_config_yaml;

impl Model {
    pub(super) fn reference(
        &mut self,
        id: &str,
        entries: &[Entry],
        styled: &StyledVertex<'_>,
    ) -> bool {
        if let Some(group) = self.groups.iter_mut().find(|g| g.id == id) {
            merge(&mut group.appearance.metadata, entries.to_vec());
            if let Some(label) = metadata_label(entries) {
                group.title = label;
            }
            return true;
        }
        if styled.metadata.is_empty() && styled.class.is_none() {
            return false;
        }
        if let Some(edge) = self.edges.iter_mut().find(|e| e.id == id) {
            merge(&mut edge.appearance.metadata, entries.to_vec());
            if let Some(label) = metadata_label(entries) {
                edge.label = label;
            }
            return true;
        }
        false
    }
    pub(super) fn metadata(&mut self, data: &[ShapeData<'_>]) -> Vec<Entry> {
        let mut entries = Vec::new();
        for block in data {
            let (value, error) = metadata_entries(block);
            if let Some(span) = error {
                self.diagnostics.push(report(
                    "agentflow/metadata-malformed",
                    "invalid metadata value".into(),
                    span,
                ));
            }
            merge(&mut entries, value);
        }
        entries
    }
    pub(super) fn node_metadata(
        &mut self,
        index: usize,
        entries: &[Entry],
        metadata: &[ShapeData<'_>],
    ) {
        let shape = entries
            .iter()
            .find(|e| e.key == "shape" && truthy(&e.value))
            .map(|entry| {
                let value = value_text(&entry.value);
                let span = metadata
                    .iter()
                    .rev()
                    .find(|block| block.value.contains("shape"))
                    .map_or(entry.key_span, |block| metadata_value_span(block, "shape"));
                if !matches!(&entry.value, ConfigValue::String(_))
                    || value.contains('_')
                    || value.bytes().any(|b| b.is_ascii_uppercase())
                {
                    self.diagnostics.push(report(
                        "agentflow/shape-unknown",
                        format!("unknown shape {value}"),
                        span,
                    ));
                    return "roundedRect".into();
                }
                self.normalize(&value, span)
            });
        if let Some(node) = self.nodes.get_mut(index) {
            if let Some(shape) = shape {
                node.shape = shape;
            }
            if let Some(label) = metadata_label(entries) {
                node.label = label;
            }
            if let Some(entry) = entries.iter().find(|e| e.key == "labelType") {
                node.label_kind = match value_text(&entry.value).as_str() {
                    "markdown" => TextKind::Markdown,
                    "string" => TextKind::String,
                    _ => TextKind::Plain,
                };
            }
        }
    }
    pub(super) fn normalize(&mut self, shape: &str, span: Span) -> String {
        let normalized = match shape {
            "task" | "square" | "squareRect" | "rect" | "" => "roundedRect",
            "tool" => "subroutine",
            "input" | "lean_right" => "lean-right",
            "decision" => "diamond",
            "refdoc" => "lin-doc",
            "action" => "hexagon",
            "round" => "roundedRect",
            other => other,
        };
        if matches!(
            normalized,
            "roundedRect"
                | "subroutine"
                | "subprocess"
                | "subproc"
                | "framed-rectangle"
                | "lean-right"
                | "diamond"
                | "lin-doc"
                | "lined-document"
                | "hexagon"
                | "hex"
                | "connector"
                | "collapsedGroup"
        ) {
            return normalized.into();
        }
        let removed = matches!(
            normalized,
            "doc"
                | "stadium"
                | "terminal"
                | "circle"
                | "trapezoid"
                | "inv_trapezoid"
                | "inv-trapezoid"
                | "doublecircle"
                | "double-circle"
                | "typeDeclaration"
                | "procs"
                | "lean_left"
                | "lean-left"
                | "in-out"
                | "cylinder"
                | "ellipse"
                | "odd"
                | "tag-rect"
                | "tagged-rectangle"
                | "delay"
                | "half-rounded-rectangle"
                | "lin-rect"
                | "lined-rectangle"
                | "win-pane"
                | "window-pane"
                | "curv-trap"
                | "curved-trapezoid"
        );
        let registered = crate::r#gen::shapes::SHAPES
            .iter()
            .any(|row| row.id == normalized || row.aliases.contains(&normalized));
        let (code, message) = if removed {
            (
                "agentflow/shape-removed",
                format!("shape {normalized} was removed; using roundedRect"),
            )
        } else if registered {
            (
                "agentflow/shape-unsupported",
                format!("shape {normalized} is not supported; using roundedRect"),
            )
        } else {
            ("agentflow/shape-unknown", format!("unknown shape {shape}"))
        };
        self.diagnostics.push(report(code, message, span));
        "roundedRect".into()
    }
}
fn truthy(value: &ConfigValue) -> bool {
    match value {
        ConfigValue::Null | ConfigValue::Bool(false) => false,
        ConfigValue::String(s) => !s.is_empty(),
        ConfigValue::Integer(s) | ConfigValue::Decimal(s) => s
            .split(['e', 'E'])
            .next()
            .is_some_and(|mantissa| mantissa.bytes().any(|b| matches!(b, b'1'..=b'9'))),
        _ => true,
    }
}
pub(super) fn value_text(value: &ConfigValue) -> String {
    match value {
        ConfigValue::String(s) | ConfigValue::Integer(s) | ConfigValue::Decimal(s) => s.clone(),
        ConfigValue::Bool(b) => b.to_string(),
        ConfigValue::Null => String::new(),
        other => format!("{other:?}"),
    }
}
fn metadata_label(entries: &[Entry]) -> Option<String> {
    entries
        .iter()
        .find(|e| e.key == "label" && truthy(&e.value))
        .map(|e| decode(value_text(&e.value).trim()))
}
pub(super) fn merge(target: &mut Vec<Entry>, entries: Vec<Entry>) {
    for mut entry in entries
        .into_iter()
        .filter(|e| !matches!(e.key.as_str(), "__proto__" | "prototype" | "constructor"))
    {
        sanitize_metadata(&mut entry.value);
        if let Some(old) = target.iter_mut().find(|old| old.key == entry.key) {
            *old = entry;
        } else {
            target.push(entry);
        }
    }
}
fn sanitize_metadata(value: &mut ConfigValue) {
    match value {
        ConfigValue::Mapping(entries) => {
            entries.retain(|entry| {
                !matches!(
                    entry.key.as_str(),
                    "__proto__" | "prototype" | "constructor"
                )
            });
            for entry in entries {
                sanitize_metadata(&mut entry.value);
            }
        }
        ConfigValue::Sequence(values) => {
            for value in values {
                sanitize_metadata(value);
            }
        }
        _ => {}
    }
}
pub(super) fn metadata_entries(data: &ShapeData<'_>) -> (Vec<Entry>, Option<Span>) {
    let normalized = data.normalized_value();
    let body = normalized.as_ref();
    let inline = !body.contains(['\r', '\n']);
    let input = if inline {
        format!("{{{body}}}")
    } else {
        body.into()
    };
    let (mut value, errors) = parse_config_yaml(&input, 0, input.len());
    if !errors.is_empty() && !inline {
        let retry = input
            .lines()
            .map(|line| line.trim_end().strip_suffix(',').unwrap_or(line))
            .collect::<Vec<_>>()
            .join("\n");
        let (retried, failures) = parse_config_yaml(&retry, 0, retry.len());
        if failures.is_empty() {
            value = retried;
        } else {
            return (
                Vec::new(),
                Some(metadata_error(data, errors.first().map(|e| e.span), inline)),
            );
        }
    } else if !errors.is_empty() {
        return (
            Vec::new(),
            Some(metadata_error(data, errors.first().map(|e| e.span), inline)),
        );
    }
    let ConfigValue::Mapping(mut entries) = value else {
        return (Vec::new(), None);
    };
    for entry in &mut entries {
        let start = data
            .value
            .find(&entry.key)
            .map_or(data.span.end, |offset| data.span.start + 2 + offset);
        entry.key_span = Span {
            start,
            end: start.saturating_add(entry.key.len()).min(data.span.end),
        };
    }
    (entries, None)
}
fn metadata_error(data: &ShapeData<'_>, span: Option<Span>, inline: bool) -> Span {
    let span = span.unwrap_or(Span {
        start: data.value.len(),
        end: data.value.len(),
    });
    let offset = data.span.start + 2;
    Span {
        start: (offset + span.start.saturating_sub(usize::from(inline))).min(data.span.end),
        end: (offset + span.end.saturating_sub(usize::from(inline))).min(data.span.end),
    }
}
fn metadata_value_span(data: &ShapeData<'_>, key: &str) -> Span {
    let Some(at) = data.value.find(key).and_then(|at| {
        data.value
            .get(at + key.len()..)
            .and_then(|tail| tail.find(':').map(|colon| at + key.len() + colon + 1))
    }) else {
        return data.span;
    };
    let tail = data.value.get(at..).unwrap_or("");
    let value = tail.trim_start();
    let start = data.span.start + 2 + at + tail.len() - value.len();
    let end = if let Some(quote) = value.chars().next().filter(|c| matches!(c, '\'' | '"')) {
        value
            .get(1..)
            .and_then(|s| s.find(quote))
            .map_or(value.len(), |n| n + 2)
    } else {
        value.find([',', '\r', '\n', '}']).unwrap_or(value.len())
    };
    Span {
        start: start.min(data.span.end),
        end: (start + value.get(..end).unwrap_or("").trim_end().len()).min(data.span.end),
    }
}
