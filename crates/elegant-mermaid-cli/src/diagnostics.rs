use elegant_mermaid::{DiagramKind, diag, model};

pub struct Parsed {
    pub source: String,
    pub kind: Option<DiagramKind>,
    pub diagnostics: Vec<diag::Diagnostic>,
    pub model: Option<model::Resolved>,
}
pub fn parse(bytes: &[u8]) -> Parsed {
    let document = elegant_mermaid::parse_bytes(bytes);
    let source = document.source().to_owned();
    let kind = document.kind();
    let diagnostics = document.diagnostics().to_vec();
    let model = document.into_resolved();
    Parsed {
        source,
        kind,
        diagnostics,
        model,
    }
}
pub fn has_errors(ds: &[diag::Diagnostic]) -> bool {
    ds.iter().any(|d| d.severity == diag::Severity::Error)
}
pub fn text(path: &str, source: &str, ds: &[diag::Diagnostic], colour: bool) -> String {
    let mut out = String::new();
    diag::text::render_text(
        &mut out,
        path,
        source,
        ds,
        &diag::text::TextFrameOptions {
            colour,
            width: |_| 1,
        },
    );
    out
}
