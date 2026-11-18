use crate::diag::document::ordered;
use crate::diag::json::push_json_string;
use crate::diag::{Diagnostic, Related, Severity, push_decimal};
use crate::r#gen::diagnostics::DIAGNOSTICS;
use crate::r#gen::lintrules::LINT_RULES;
use crate::source::{LineIndex, Span};

pub struct SarifFile<'a> {
    pub path: &'a str,
    pub index: &'a LineIndex,
    pub diagnostics: &'a [Diagnostic],
}

pub fn push_sarif(out: &mut String, version: &str, files: &[SarifFile<'_>]) {
    let mut files: Vec<&SarifFile<'_>> = files.iter().collect();
    files.sort_by(|left, right| left.path.cmp(right.path));
    out.push_str(
        "{\"$schema\":\"https://json.schemastore.org/sarif-2.1.0.json\",\"version\":\"2.1.0\",\"runs\":[{\"tool\":{\"driver\":{\"name\":\"emd\",\"version\":",
    );
    push_json_string(out, version);
    out.push_str(",\"rules\":[");
    push_rules(out, &files);
    out.push_str("]}},\"results\":[");
    let mut first = true;
    for file in &files {
        for &at in &ordered(file.diagnostics) {
            if !first {
                out.push(',');
            }
            first = false;
            push_result(out, file, &file.diagnostics[at]);
        }
    }
    out.push_str("]}]}\n");
}

fn push_rules(out: &mut String, files: &[&SarifFile<'_>]) {
    let mut codes: Vec<&'static str> = Vec::new();
    for file in files {
        for diagnostic in file.diagnostics {
            if !codes.contains(&diagnostic.code) {
                codes.push(diagnostic.code);
            }
        }
    }
    let mut ordered_codes: Vec<&'static str> = Vec::new();
    for rule in LINT_RULES {
        if codes.contains(&rule.code) && !ordered_codes.contains(&rule.code) {
            ordered_codes.push(rule.code);
        }
    }
    for diagnostic in DIAGNOSTICS {
        if codes.contains(&diagnostic.code) && !ordered_codes.contains(&diagnostic.code) {
            ordered_codes.push(diagnostic.code);
        }
    }
    let mut unknown: Vec<&'static str> = codes
        .iter()
        .copied()
        .filter(|code| !ordered_codes.contains(code))
        .collect();
    unknown.sort_unstable();
    ordered_codes.extend(unknown);
    for (position, code) in ordered_codes.iter().enumerate() {
        if position > 0 {
            out.push(',');
        }
        let (summary, help) = row_text(code);
        out.push_str("{\"id\":");
        push_json_string(out, code);
        out.push_str(",\"shortDescription\":{\"text\":");
        push_json_string(out, summary);
        out.push_str("},\"help\":{\"text\":");
        push_json_string(out, help);
        out.push_str("}}");
    }
}

fn row_text(code: &str) -> (&'static str, &'static str) {
    if let Some(rule) = LINT_RULES.iter().find(|rule| rule.code == code) {
        return (rule.summary, rule.help);
    }
    if let Some(row) = DIAGNOSTICS.iter().find(|row| row.code == code) {
        return (row.summary, row.help);
    }
    ("", "")
}

fn level(severity: Severity) -> &'static str {
    match severity {
        Severity::Error => "error",
        Severity::Warning => "warning",
        Severity::Info => "note",
    }
}

fn push_result(out: &mut String, file: &SarifFile<'_>, d: &Diagnostic) {
    out.push_str("{\"ruleId\":");
    push_json_string(out, d.code);
    out.push_str(",\"level\":");
    push_json_string(out, level(d.severity));
    out.push_str(",\"message\":{\"text\":");
    push_json_string(out, &d.message);
    out.push_str("},\"locations\":[{\"physicalLocation\":");
    push_location(out, file, d.span);
    out.push_str("}]");
    if !d.related.is_empty() {
        out.push_str(",\"relatedLocations\":[");
        for (position, related) in d.related.iter().enumerate() {
            if position > 0 {
                out.push(',');
            }
            push_related(out, file, related);
        }
        out.push(']');
    }
    out.push('}');
}

fn push_related(out: &mut String, file: &SarifFile<'_>, related: &Related) {
    out.push_str("{\"physicalLocation\":");
    push_location(out, file, related.span);
    out.push_str(",\"message\":{\"text\":");
    push_json_string(out, &related.message);
    out.push_str("}}");
}

fn push_location(out: &mut String, file: &SarifFile<'_>, span: Span) {
    out.push_str("{\"artifactLocation\":{\"uri\":");
    push_json_string(out, file.path);
    out.push_str("},\"region\":{\"startLine\":");
    push_decimal(out, file.index.position(span.start).line);
    out.push_str(",\"startColumn\":");
    push_decimal(out, file.index.utf16_column(span.start));
    out.push_str(",\"endLine\":");
    push_decimal(out, file.index.position(span.end).line);
    out.push_str(",\"endColumn\":");
    push_decimal(out, file.index.utf16_column(span.end));
    out.push_str("}}");
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diag::Fix;

    fn diagnostic(code: &'static str, span: Span, related: Vec<Related>) -> Diagnostic {
        Diagnostic {
            code,
            severity: Severity::Warning,
            message: String::from("msg"),
            span,
            related,
            help: String::from("h"),
            fixes: Vec::<Fix>::new(),
        }
    }

    #[test]
    fn sarif_region_uses_utf16_columns() {
        let text = "ab\u{1F600}\ncd\n";
        let index = LineIndex::new(text);
        let d = diagnostic(
            "common/empty-source",
            Span { start: 2, end: 6 },
            vec![Related {
                span: Span { start: 7, end: 9 },
                message: String::from("first here"),
            }],
        );
        let files = [SarifFile {
            path: "<stdin>",
            index: &index,
            diagnostics: std::slice::from_ref(&d),
        }];
        let mut out = String::new();
        push_sarif(&mut out, "0.1.0", &files);
        let expected = concat!(
            "{\"$schema\":\"https://json.schemastore.org/sarif-2.1.0.json\",",
            "\"version\":\"2.1.0\",\"runs\":[{\"tool\":{\"driver\":{\"name\":\"emd\",",
            "\"version\":\"0.1.0\",\"rules\":[",
            "{\"id\":\"common/empty-source\",\"shortDescription\":{\"text\":\"source is empty\"},",
            "\"help\":{\"text\":\"add a diagram header, for example flowchart\"}}]}},",
            "\"results\":[{\"ruleId\":\"common/empty-source\",\"level\":\"warning\",",
            "\"message\":{\"text\":\"msg\"},\"locations\":[{\"physicalLocation\":",
            "{\"artifactLocation\":{\"uri\":\"<stdin>\"},",
            "\"region\":{\"startLine\":1,\"startColumn\":3,\"endLine\":1,\"endColumn\":5}}}],",
            "\"relatedLocations\":[{\"physicalLocation\":",
            "{\"artifactLocation\":{\"uri\":\"<stdin>\"},",
            "\"region\":{\"startLine\":2,\"startColumn\":1,\"endLine\":2,\"endColumn\":3}},",
            "\"message\":{\"text\":\"first here\"}}]}]}]}\n",
        );
        assert_eq!(out, expected);
    }

    #[test]
    fn sarif_orders_rules_by_registry_and_maps_levels() {
        let index = LineIndex::new("abcd\n");
        let list = [
            diagnostic(
                "flowchart/duplicate-ids",
                Span { start: 0, end: 1 },
                Vec::new(),
            ),
            diagnostic("common/empty-source", Span { start: 1, end: 2 }, Vec::new()),
        ];
        let files = [SarifFile {
            path: "p.mmd",
            index: &index,
            diagnostics: &list,
        }];
        let mut out = String::new();
        push_sarif(&mut out, "1.2.3", &files);
        let rules_at = out.find("\"rules\":[").unwrap_or(0);
        let first_rule = out[rules_at..]
            .find("\"id\":\"")
            .map(|at| at + rules_at + 6)
            .unwrap_or(0);
        assert!(
            out[first_rule..].starts_with("flowchart/duplicate-ids"),
            "sarif orders rules by registry and maps levels: contract out[first_rule..].starts_with(\"flowchart/duplicate-ids\") failed; observed out={:?}",
            out
        );
        assert_eq!(level(Severity::Info), "note");
        assert_eq!(level(Severity::Error), "error");
    }

    #[test]
    fn sarif_omits_related_locations_when_empty() {
        let index = LineIndex::new("x\n");
        let d = diagnostic("common/empty-source", Span { start: 0, end: 0 }, Vec::new());
        let files = [SarifFile {
            path: "p",
            index: &index,
            diagnostics: std::slice::from_ref(&d),
        }];
        let mut out = String::new();
        push_sarif(&mut out, "v", &files);
        assert!(
            !out.contains("relatedLocations"),
            "sarif omits related locations when empty: contract !out.contains(\"relatedLocations\") failed; observed out={:?}",
            out
        );
    }
}

#[cfg(test)]
mod ordering_tests {
    use super::*;

    #[test]
    fn sarif_orders_files_and_unknown_rules_and_handles_empty() {
        let index = LineIndex::new("😀");
        let a = Diagnostic {
            code: "unknown/a",
            severity: Severity::Error,
            message: "a".into(),
            span: Span { start: 0, end: 4 },
            related: vec![],
            help: String::new(),
            fixes: vec![],
        };
        let z = Diagnostic {
            code: "unknown/z",
            message: "z".into(),
            ..a.clone()
        };
        let files = [
            SarifFile {
                path: "z",
                index: &index,
                diagnostics: std::slice::from_ref(&z),
            },
            SarifFile {
                path: "a",
                index: &index,
                diagnostics: std::slice::from_ref(&a),
            },
        ];
        let mut out = String::new();
        push_sarif(&mut out, "v", &files);
        assert!(out.contains("\"rules\":[{\"id\":\"unknown/a\",\"shortDescription\":{\"text\":\"\"},\"help\":{\"text\":\"\"}},{\"id\":\"unknown/z\""), "sarif orders files and unknown rules and handles empty: contract out.contains(\"\\\"rules\\\":[{{\\\"id\\\":\\\"unknown/a\\\",\\\"shortDescription\\\":{{\\\"text\\\":\\\"\\\"}},\\\"help\\\":{{\\\"text\\\":\\\"\\\"}}}},{{\\\"id\\\":\\\"unknown/z\\\"\") failed; observed out={:?}", out);
        assert!(
            out.contains("\"results\":[{\"ruleId\":\"unknown/a\""),
            "sarif orders files and unknown rules and handles empty: contract out.contains(\"\\\"results\\\":[{{\\\"ruleId\\\":\\\"unknown/a\\\"\") failed; observed out={:?}",
            out
        );
        assert!(
            out.contains("\"startColumn\":1,\"endLine\":1,\"endColumn\":3"),
            "sarif orders files and unknown rules and handles empty: contract out.contains(\"\\\"startColumn\\\":1,\\\"endLine\\\":1,\\\"endColumn\\\":3\") failed; observed out={:?}",
            out
        );
        out.clear();
        push_sarif(&mut out, "v", &[]);
        assert_eq!(
            out,
            "{\"$schema\":\"https://json.schemastore.org/sarif-2.1.0.json\",\"version\":\"2.1.0\",\"runs\":[{\"tool\":{\"driver\":{\"name\":\"emd\",\"version\":\"v\",\"rules\":[]}},\"results\":[]}]}\n"
        );
    }

    #[test]
    fn sarif_lists_unknown_rules_in_byte_order_after_registry_rules() {
        let index = LineIndex::new("abc");
        let diagnostic = |code: &'static str| Diagnostic {
            code,
            severity: Severity::Info,
            message: code.to_owned(),
            span: Span { start: 0, end: 1 },
            related: vec![],
            help: String::new(),
            fixes: vec![],
        };
        let diagnostics = [
            diagnostic("custom/zeta"),
            diagnostic("custom/alpha"),
            diagnostic("flowchart/duplicate-ids"),
            diagnostic("custom/mid"),
        ];
        let files = [SarifFile {
            path: "a",
            index: &index,
            diagnostics: &diagnostics,
        }];
        let mut out = String::new();
        push_sarif(&mut out, "v", &files);
        let rules = out
            .split("\"rules\":[")
            .nth(1)
            .and_then(|rest| rest.split("]}},\"results\"").next())
            .unwrap_or("");
        let ids: Vec<&str> = rules
            .split("{\"id\":\"")
            .skip(1)
            .filter_map(|part| part.split('"').next())
            .collect();
        assert_eq!(
            ids,
            [
                "flowchart/duplicate-ids",
                "custom/alpha",
                "custom/mid",
                "custom/zeta"
            ]
        );
    }
}
