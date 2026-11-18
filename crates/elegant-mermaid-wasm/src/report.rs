use elegant_mermaid::diag::document::{FileDiagnostics, push_document};
use elegant_mermaid::source::LineIndex;
use elegant_mermaid::{Diagnostic, DiagramKind, Document, LintConfig, Severity};

const PATH: &str = "<stdin>";
const KEY: &str = "\"diagnostics\":";
const TAIL: &str = "]}],\"summary\"";

pub struct Report {
    pub document: String,
    pub diagnostics: String,
    pub failed: bool,
}

pub fn syntax(document: &Document<'_>) -> Report {
    report(document, document.diagnostics())
}

pub fn linted(document: &Document<'_>, config: &LintConfig) -> Report {
    report(document, &elegant_mermaid::lint_document(document, config))
}

fn report(document: &Document<'_>, diagnostics: &[Diagnostic]) -> Report {
    let index = LineIndex::new(document.source());
    let mut files = [FileDiagnostics {
        path: PATH,
        kind: document.kind().map(DiagramKind::id),
        index: &index,
        diagnostics,
    }];
    let mut json = String::new();
    push_document(&mut json, &mut files);
    Report {
        diagnostics: first_file_diagnostics(&json),
        failed: diagnostics.iter().any(|d| d.severity == Severity::Error),
        document: json,
    }
}

fn first_file_diagnostics(json: &str) -> String {
    let start = json.find(KEY).map(|at| at + KEY.len());
    let end = json.rfind(TAIL).map(|at| at + 1);
    match (start, end) {
        (Some(start), Some(end)) if start <= end => json[start..end].to_owned(),
        _ => "[]".to_owned(),
    }
}
