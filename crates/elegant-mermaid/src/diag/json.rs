use crate::diag::{Diagnostic, Edit, Fix, Related, push_decimal};
use crate::source::{LineIndex, Span};

pub fn push_diagnostic_json(out: &mut String, index: &LineIndex, d: &Diagnostic) {
    let start = index.position(d.span.start);
    let end = index.position(d.span.end);
    out.push_str("{\"code\":");
    push_json_string(out, d.code);
    out.push_str(",\"severity\":");
    push_json_string(out, d.severity.as_str());
    out.push_str(",\"message\":");
    push_json_string(out, &d.message);
    out.push_str(",\"span\":");
    push_span(out, d.span);
    out.push_str(",\"line\":");
    push_decimal(out, start.line);
    out.push_str(",\"column\":");
    push_decimal(out, start.column);
    out.push_str(",\"end_line\":");
    push_decimal(out, end.line);
    out.push_str(",\"end_column\":");
    push_decimal(out, end.column);
    out.push_str(",\"related\":");
    push_related_list(out, index, &d.related);
    out.push_str(",\"help\":");
    push_json_string(out, &d.help);
    out.push_str(",\"fixes\":");
    push_fix_list(out, &d.fixes);
    out.push('}');
}

pub fn push_json_string(out: &mut String, s: &str) {
    out.push('"');
    for ch in s.chars() {
        push_escaped(out, ch);
    }
    out.push('"');
}

fn push_escaped(out: &mut String, ch: char) {
    match ch {
        '"' => out.push_str("\\\""),
        '\\' => out.push_str("\\\\"),
        '\u{8}' => out.push_str("\\b"),
        '\t' => out.push_str("\\t"),
        '\n' => out.push_str("\\n"),
        '\u{c}' => out.push_str("\\f"),
        '\r' => out.push_str("\\r"),
        _ if u32::from(ch) < 0x20 => push_control_escape(out, ch),
        _ => out.push(ch),
    }
}

fn push_control_escape(out: &mut String, ch: char) {
    let code = u32::from(ch);
    out.push_str("\\u00");
    out.push(hex_digit(u8::try_from(code >> 4).unwrap_or(0)));
    out.push(hex_digit(u8::try_from(code & 0xF).unwrap_or(0)));
}

fn hex_digit(v: u8) -> char {
    if v < 10 {
        char::from(b'0' + v)
    } else {
        char::from(b'a' + (v - 10))
    }
}

fn push_span(out: &mut String, span: Span) {
    out.push_str("{\"start\":");
    push_decimal(out, span.start);
    out.push_str(",\"end\":");
    push_decimal(out, span.end);
    out.push('}');
}

fn push_related_list(out: &mut String, index: &LineIndex, rs: &[Related]) {
    out.push('[');
    for (position, related) in rs.iter().enumerate() {
        if position > 0 {
            out.push(',');
        }
        push_related(out, index, related);
    }
    out.push(']');
}

fn push_related(out: &mut String, index: &LineIndex, related: &Related) {
    let position = index.position(related.span.start);
    out.push_str("{\"span\":");
    push_span(out, related.span);
    out.push_str(",\"line\":");
    push_decimal(out, position.line);
    out.push_str(",\"column\":");
    push_decimal(out, position.column);
    out.push_str(",\"message\":");
    push_json_string(out, &related.message);
    out.push('}');
}

fn push_fix_list(out: &mut String, fs: &[Fix]) {
    out.push('[');
    for (position, fix) in fs.iter().enumerate() {
        if position > 0 {
            out.push(',');
        }
        push_fix(out, fix);
    }
    out.push(']');
}

fn push_fix(out: &mut String, fix: &Fix) {
    out.push_str("{\"title\":");
    push_json_string(out, &fix.title);
    out.push_str(",\"safety\":");
    push_json_string(out, fix.safety.as_str());
    out.push_str(",\"edits\":");
    push_edit_list(out, &fix.edits);
    out.push('}');
}

fn push_edit_list(out: &mut String, es: &[Edit]) {
    out.push('[');
    for (position, edit) in es.iter().enumerate() {
        if position > 0 {
            out.push(',');
        }
        push_edit(out, edit);
    }
    out.push(']');
}

fn push_edit(out: &mut String, edit: &Edit) {
    out.push_str("{\"span\":");
    push_span(out, edit.span);
    out.push_str(",\"new_text\":");
    push_json_string(out, &edit.new_text);
    out.push('}');
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diag::{FixSafety, Severity};

    fn index(text: &str) -> LineIndex {
        LineIndex::new(text)
    }

    #[test]
    fn diagnostic_keys_follow_schema_v1_order() {
        let text = "abc\ndef\n";
        let d = Diagnostic {
            code: "flowchart/duplicate-ids",
            severity: Severity::Error,
            message: String::from("node id declared twice"),
            span: Span { start: 5, end: 6 },
            related: vec![Related {
                span: Span { start: 0, end: 1 },
                message: String::from("first declared here"),
            }],
            help: String::from("give each node one label"),
            fixes: vec![Fix {
                title: String::from("keep the first label"),
                safety: FixSafety::Unsafe,
                edits: vec![Edit {
                    span: Span { start: 5, end: 6 },
                    new_text: String::from("f"),
                }],
            }],
        };
        let mut out = String::new();
        push_diagnostic_json(&mut out, &index(text), &d);
        assert_eq!(
            out,
            "{\"code\":\"flowchart/duplicate-ids\",\"severity\":\"error\",\"message\":\"node id declared twice\",\"span\":{\"start\":5,\"end\":6},\"line\":2,\"column\":2,\"end_line\":2,\"end_column\":3,\"related\":[{\"span\":{\"start\":0,\"end\":1},\"line\":1,\"column\":1,\"message\":\"first declared here\"}],\"help\":\"give each node one label\",\"fixes\":[{\"title\":\"keep the first label\",\"safety\":\"unsafe\",\"edits\":[{\"span\":{\"start\":5,\"end\":6},\"new_text\":\"f\"}]}]}"
        );
    }

    #[test]
    fn empty_lists_and_help_are_compact() {
        let d = Diagnostic {
            code: "c/x",
            severity: Severity::Info,
            message: String::new(),
            span: Span { start: 0, end: 0 },
            related: Vec::new(),
            help: String::new(),
            fixes: Vec::new(),
        };
        let mut out = String::new();
        push_diagnostic_json(&mut out, &index(""), &d);
        assert!(out.contains("\"related\":[]"));
        assert!(out.ends_with("\"help\":\"\",\"fixes\":[]}"));
        assert!(!out.contains(' '));
    }

    #[test]
    fn json_string_escapes_the_fixed_set() {
        let mut out = String::new();
        push_json_string(&mut out, "a\"b\\c\td\ne\rf\u{8}g\u{c}h\u{1}\u{1f}i/j\u{7f}");
        assert_eq!(
            out,
            "\"a\\\"b\\\\c\\td\\ne\\rf\\bg\\fh\\u0001\\u001fi/j\u{7f}\""
        );
    }

    #[test]
    fn json_string_keeps_non_ascii_raw() {
        let mut out = String::new();
        push_json_string(&mut out, "é世😀");
        assert_eq!(out, "\"é世😀\"");
    }

    #[test]
    fn span_end_maps_as_an_offset() {
        let d = Diagnostic {
            code: "c/x",
            severity: Severity::Warning,
            message: String::from("m"),
            span: Span { start: 0, end: 3 },
            related: Vec::new(),
            help: String::new(),
            fixes: Vec::new(),
        };
        let mut out = String::new();
        push_diagnostic_json(&mut out, &index("é\nx"), &d);
        assert!(out.contains("\"line\":1,\"column\":1,\"end_line\":2,\"end_column\":1"));
    }
}
