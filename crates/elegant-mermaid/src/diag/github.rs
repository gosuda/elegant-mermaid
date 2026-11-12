use crate::diag::document::ordered;
use crate::diag::{Diagnostic, Severity, push_decimal};
use crate::source::LineIndex;

pub fn push_github(out: &mut String, path: &str, index: &LineIndex, diagnostics: &[Diagnostic]) {
    for &at in &ordered(diagnostics) {
        push_command(out, path, index, &diagnostics[at]);
    }
}

fn push_command(out: &mut String, path: &str, index: &LineIndex, d: &Diagnostic) {
    out.push_str("::");
    out.push_str(command(d.severity));
    out.push_str(" file=");
    push_property(out, path);
    out.push_str(",line=");
    push_decimal(out, index.position(d.span.start).line);
    out.push_str(",col=");
    push_decimal(out, index.position(d.span.start).column);
    out.push_str(",endLine=");
    push_decimal(out, index.position(d.span.end).line);
    out.push_str(",endColumn=");
    push_decimal(out, index.position(d.span.end).column);
    out.push_str(",title=");
    push_property(out, d.code);
    out.push_str("::");
    push_data(out, &d.message);
    out.push('\n');
}

fn command(severity: Severity) -> &'static str {
    match severity {
        Severity::Error => "error",
        Severity::Warning => "warning",
        Severity::Info => "notice",
    }
}

fn push_data(out: &mut String, message: &str) {
    for ch in message.chars() {
        escape_common(out, ch);
    }
}

fn push_property(out: &mut String, value: &str) {
    for ch in value.chars() {
        match ch {
            ':' => out.push_str("%3A"),
            ',' => out.push_str("%2C"),
            _ => escape_common(out, ch),
        }
    }
}

fn escape_common(out: &mut String, ch: char) {
    match ch {
        '%' => out.push_str("%25"),
        '\r' => out.push_str("%0D"),
        '\n' => out.push_str("%0A"),
        _ => out.push(ch),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source::Span;

    fn diagnostic(code: &'static str, severity: Severity, span: Span) -> Diagnostic {
        Diagnostic {
            code,
            severity,
            message: String::from("50% done\r\nnext"),
            span,
            related: Vec::new(),
            help: String::new(),
            fixes: Vec::new(),
        }
    }

    #[test]
    fn github_escapes_data_and_properties() {
        let index = LineIndex::new("abcd\nef\n");
        let list = [diagnostic(
            "flowchart/a:b,c",
            Severity::Error,
            Span { start: 1, end: 7 },
        )];
        let mut out = String::new();
        push_github(&mut out, "dir:name,x.mmd", &index, &list);
        assert_eq!(
            out,
            "::error file=dir%3Aname%2Cx.mmd,line=1,col=2,endLine=2,endColumn=3,title=flowchart/a%3Ab%2Cc::50%25 done%0D%0Anext\n"
        );
    }

    #[test]
    fn github_maps_levels_and_orders_diagnostics() {
        let index = LineIndex::new("xy\n");
        let list = [
            diagnostic("b/one", Severity::Info, Span { start: 1, end: 2 }),
            diagnostic("a/two", Severity::Warning, Span { start: 0, end: 1 }),
        ];
        let mut out = String::new();
        push_github(&mut out, "p", &index, &list);
        let lines: Vec<&str> = out.lines().collect();
        assert_eq!(lines.len(), 2);
        assert!(lines[0].starts_with("::warning file=p,line=1,col=1,"));
        assert!(lines[1].starts_with("::notice file=p,line=1,col=2,"));
    }
}
