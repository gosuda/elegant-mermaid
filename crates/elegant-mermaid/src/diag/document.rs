use crate::diag::json::{push_diagnostic_json, push_json_string};
use crate::diag::{Diagnostic, Severity, push_decimal};
use crate::source::LineIndex;

pub struct FileDiagnostics<'a> {
    pub path: &'a str,
    pub kind: Option<&'a str>,
    pub index: &'a LineIndex,
    pub diagnostics: &'a [Diagnostic],
}

pub(crate) fn sort_files(files: &mut [FileDiagnostics<'_>]) {
    files.sort_by(|left, right| left.path.as_bytes().cmp(right.path.as_bytes()));
}

pub(crate) fn ordered(ds: &[Diagnostic]) -> Vec<usize> {
    let mut order: Vec<usize> = (0..ds.len()).collect();
    order.sort_by(|&left, &right| {
        ds[left]
            .span
            .start
            .cmp(&ds[right].span.start)
            .then_with(|| ds[left].code.as_bytes().cmp(ds[right].code.as_bytes()))
    });
    order
}

pub fn push_document(out: &mut String, files: &mut [FileDiagnostics<'_>]) {
    sort_files(files);
    let counts = SeverityCounts::of(files);
    out.push_str("{\"version\":1,\"files\":[");
    for (position, file) in files.iter().enumerate() {
        if position > 0 {
            out.push(',');
        }
        push_file(out, file);
    }
    out.push_str("],\"summary\":{\"files\":");
    push_decimal(out, files.len());
    out.push_str(",\"errors\":");
    push_decimal(out, counts.errors);
    out.push_str(",\"warnings\":");
    push_decimal(out, counts.warnings);
    out.push_str(",\"info\":");
    push_decimal(out, counts.info);
    out.push_str("}}\n");
}

fn push_file(out: &mut String, file: &FileDiagnostics<'_>) {
    out.push_str("{\"path\":");
    push_json_string(out, file.path);
    out.push_str(",\"kind\":");
    match file.kind {
        Some(kind) => push_json_string(out, kind),
        None => out.push_str("null"),
    }
    out.push_str(",\"diagnostics\":[");
    let order = ordered(file.diagnostics);
    for (position, &at) in order.iter().enumerate() {
        if position > 0 {
            out.push(',');
        }
        push_diagnostic_json(out, file.index, &file.diagnostics[at]);
    }
    out.push_str("]}");
}

struct SeverityCounts {
    errors: usize,
    warnings: usize,
    info: usize,
}

impl SeverityCounts {
    fn of(files: &[FileDiagnostics<'_>]) -> SeverityCounts {
        let mut counts = SeverityCounts {
            errors: 0,
            warnings: 0,
            info: 0,
        };
        for diagnostic in files.iter().flat_map(|file| file.diagnostics) {
            counts.add(diagnostic.severity);
        }
        counts
    }

    fn add(&mut self, severity: Severity) {
        match severity {
            Severity::Error => self.errors += 1,
            Severity::Warning => self.warnings += 1,
            Severity::Info => self.info += 1,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source::Span;

    fn diagnostic(code: &'static str, severity: Severity, start: usize, end: usize) -> Diagnostic {
        Diagnostic {
            code,
            severity,
            message: String::from("m"),
            span: Span { start, end },
            related: Vec::new(),
            help: String::new(),
            fixes: Vec::new(),
        }
    }

    #[test]
    fn document_orders_files_and_counts_severities() {
        let first = diagnostic("common/empty-source", Severity::Error, 0, 0);
        let list = [
            diagnostic("flowchart/x", Severity::Warning, 0, 9),
            diagnostic("flowchart/x", Severity::Info, 0, 9),
        ];
        let index_a = LineIndex::new("x\n");
        let index_b = LineIndex::new("flowchart LR\nA\n");
        let mut files = [
            FileDiagnostics {
                path: "b.mmd",
                kind: Some("flowchart"),
                index: &index_b,
                diagnostics: &list,
            },
            FileDiagnostics {
                path: "a.mmd",
                kind: None,
                index: &index_a,
                diagnostics: std::slice::from_ref(&first),
            },
        ];
        let mut out = String::new();
        push_document(&mut out, &mut files);
        let expected = concat!(
            "{\"version\":1,\"files\":[",
            "{\"path\":\"a.mmd\",\"kind\":null,\"diagnostics\":[",
            "{\"code\":\"common/empty-source\",\"severity\":\"error\",",
            "\"message\":\"m\",\"span\":{\"start\":0,\"end\":0},",
            "\"line\":1,\"column\":1,\"end_line\":1,\"end_column\":1,",
            "\"related\":[],\"help\":\"\",\"fixes\":[]}]},",
            "{\"path\":\"b.mmd\",\"kind\":\"flowchart\",\"diagnostics\":[",
            "{\"code\":\"flowchart/x\",\"severity\":\"warning\",",
            "\"message\":\"m\",\"span\":{\"start\":0,\"end\":9},",
            "\"line\":1,\"column\":1,\"end_line\":1,\"end_column\":10,",
            "\"related\":[],\"help\":\"\",\"fixes\":[]},",
            "{\"code\":\"flowchart/x\",\"severity\":\"info\",",
            "\"message\":\"m\",\"span\":{\"start\":0,\"end\":9},",
            "\"line\":1,\"column\":1,\"end_line\":1,\"end_column\":10,",
            "\"related\":[],\"help\":\"\",\"fixes\":[]}]}],",
            "\"summary\":{\"files\":2,\"errors\":1,\"warnings\":1,\"info\":1}}\n",
        );
        assert_eq!(out, expected);
    }

    #[test]
    fn document_sorts_diagnostics_by_start_then_code() {
        let index = LineIndex::new("abcd\n");
        let list = [
            diagnostic("b/code", Severity::Error, 2, 3),
            diagnostic("a/code", Severity::Error, 2, 3),
            diagnostic("c/code", Severity::Error, 0, 1),
        ];
        let mut files = [FileDiagnostics {
            path: "one.mmd",
            kind: Some("flowchart"),
            index: &index,
            diagnostics: &list,
        }];
        let mut out = String::new();
        push_document(&mut out, &mut files);
        let codes: Vec<&str> = out
            .match_indices("\"code\":\"")
            .map(|(at, _)| &out[at + 8..at + 14])
            .collect();
        assert_eq!(codes, ["c/code", "a/code", "b/code"]);
    }

    #[test]
    fn document_emits_empty_file_list() {
        let mut files: [FileDiagnostics<'_>; 0] = [];
        let mut out = String::new();
        push_document(&mut out, &mut files);
        assert_eq!(
            out,
            "{\"version\":1,\"files\":[],\"summary\":{\"files\":0,\"errors\":0,\"warnings\":0,\"info\":0}}\n"
        );
    }
}

#[cfg(test)]
mod machine_golden {
    use super::*;
    use crate::diag::{Edit, Fix, FixSafety, Related};
    use crate::diag::{
        github::push_github,
        sarif::{SarifFile, push_sarif},
    };
    use crate::source::Span;
    const GOLDEN_JSON: &str = concat!(
        r#"{"version":1,"files":[{"path":"<stdin>","kind":"flowchart","diagnostics":[{"code":"common/empty-source","severity":"error","message":"error","span":{"start":0,"end":1},"line":1,"column":1,"end_line":1,"end_column":2,"related":[{"span":{"start":5,"end":6},"line":1,"column":3,"message":"related"}],"help":"","fixes":[]},{"code":"common/empty-source","severity":"warning","message":"50%,:\r\né😀","span":{"start":1,"end":5},"line":1,"column":2,"end_line":1,"end_column":3,"related":[],"help":"","fixes":[{"title":"Replace","safety":"safe","edits":[{"span":{"start":1,"end":5},"new_text":"x"}]}]},{"code":"common/empty-source","severity":"info","message":"info","span":{"start":5,"end":6},"line":1,"column":3,"end_line":1,"end_column":4,"related":[],"help":"","fixes":[]}]},{"path":"z.mmd","kind":null,"diagnostics":[]}],"summary":{"files":2,"errors":1,"warnings":1,"info":1}}"#,
        "\n"
    );
    const GOLDEN_SARIF: &str = concat!(
        r#"{"$schema":"https://json.schemastore.org/sarif-2.1.0.json","version":"2.1.0","runs":[{"tool":{"driver":{"name":"emd","version":"0.1.0","rules":[{"id":"common/empty-source","shortDescription":{"text":"source is empty"},"help":{"text":"add a diagram header, for example flowchart"}}]}},"results":[{"ruleId":"common/empty-source","level":"error","message":{"text":"error"},"locations":[{"physicalLocation":{"artifactLocation":{"uri":"<stdin>"},"region":{"startLine":1,"startColumn":1,"endLine":1,"endColumn":2}}}],"relatedLocations":[{"physicalLocation":{"artifactLocation":{"uri":"<stdin>"},"region":{"startLine":1,"startColumn":4,"endLine":1,"endColumn":5}},"message":{"text":"related"}}]},{"ruleId":"common/empty-source","level":"warning","message":{"text":"50%,:\r\né😀"},"locations":[{"physicalLocation":{"artifactLocation":{"uri":"<stdin>"},"region":{"startLine":1,"startColumn":2,"endLine":1,"endColumn":4}}}]},{"ruleId":"common/empty-source","level":"note","message":{"text":"info"},"locations":[{"physicalLocation":{"artifactLocation":{"uri":"<stdin>"},"region":{"startLine":1,"startColumn":4,"endLine":1,"endColumn":5}}}]}]}]}"#,
        "\n"
    );
    const GOLDEN_GITHUB: &str = r#"::error file=<stdin>,line=1,col=1,endLine=1,endColumn=2,title=common/empty-source::error
::warning file=<stdin>,line=1,col=2,endLine=1,endColumn=3,title=common/empty-source::50%25,:%0D%0Aé😀
::notice file=<stdin>,line=1,col=3,endLine=1,endColumn=4,title=common/empty-source::info
"#;
    #[test]
    fn document_sarif_github_match_go_goldens() {
        let index = LineIndex::new("a😀b\n");
        let empty = LineIndex::new("");
        let mut list = vec![
            Diagnostic {
                code: "common/empty-source",
                severity: Severity::Info,
                message: "info".into(),
                span: Span { start: 5, end: 6 },
                related: vec![],
                help: String::new(),
                fixes: vec![],
            },
            Diagnostic {
                code: "common/empty-source",
                severity: Severity::Warning,
                message: "50%,:\r\né😀".into(),
                span: Span { start: 1, end: 5 },
                related: vec![],
                help: String::new(),
                fixes: vec![Fix {
                    title: "Replace".into(),
                    safety: FixSafety::Safe,
                    edits: vec![Edit {
                        span: Span { start: 1, end: 5 },
                        new_text: "x".into(),
                    }],
                }],
            },
            Diagnostic {
                code: "common/empty-source",
                severity: Severity::Error,
                message: "error".into(),
                span: Span { start: 0, end: 1 },
                related: vec![Related {
                    span: Span { start: 5, end: 6 },
                    message: "related".into(),
                }],
                help: String::new(),
                fixes: vec![],
            },
        ];
        let mut files = [
            FileDiagnostics {
                path: "z.mmd",
                kind: None,
                index: &empty,
                diagnostics: &[],
            },
            FileDiagnostics {
                path: "<stdin>",
                kind: Some("flowchart"),
                index: &index,
                diagnostics: &list,
            },
        ];
        let mut out = String::new();
        push_document(&mut out, &mut files);
        assert_eq!(out, GOLDEN_JSON);
        out.clear();
        let files = [
            SarifFile {
                path: "z.mmd",
                index: &empty,
                diagnostics: &[],
            },
            SarifFile {
                path: "<stdin>",
                index: &index,
                diagnostics: &list,
            },
        ];
        push_sarif(&mut out, "0.1.0", &files);
        assert_eq!(out, GOLDEN_SARIF);
        out.clear();
        push_github(&mut out, "<stdin>", &index, &list);
        assert_eq!(out, GOLDEN_GITHUB);
        list.clear();
        out.clear();
        push_github(&mut out, "empty", &index, &list);
        assert_eq!(out, "");
    }
}
