use crate::options::OptionError;

pub struct Response {
    pub ok: bool,
    pub output: String,
    pub diagnostics: String,
    pub applied: usize,
}

impl Response {
    pub fn rejected(error: &OptionError) -> Response {
        Response {
            ok: false,
            output: error.to_string(),
            diagnostics: "[]".to_owned(),
            applied: 0,
        }
    }

    pub fn encode(&self) -> String {
        let mut out = String::with_capacity(self.output.len() + self.diagnostics.len() + 64);
        out.push_str(if self.ok {
            "{\"ok\":true,\"output\":"
        } else {
            "{\"ok\":false,\"output\":"
        });
        push_string(&mut out, &self.output);
        out.push_str(",\"diagnostics\":");
        out.push_str(&self.diagnostics);
        out.push_str(",\"applied\":");
        out.push_str(&self.applied.to_string());
        out.push('}');
        out
    }
}

fn push_string(out: &mut String, text: &str) {
    out.push('"');
    for ch in text.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\u{8}' => out.push_str("\\b"),
            '\u{c}' => out.push_str("\\f"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\u{2028}' => out.push_str("\\u2028"),
            '\u{2029}' => out.push_str("\\u2029"),
            _ if u32::from(ch) < 0x20 => out.push_str(&format!("\\u{:04x}", u32::from(ch))),
            _ => out.push(ch),
        }
    }
    out.push('"');
}
