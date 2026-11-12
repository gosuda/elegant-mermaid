use elegant_mermaid::{DiagramKind, diag, model, source::Span, syntax};

pub struct Parsed {
    pub source: String,
    pub kind: Option<DiagramKind>,
    pub diagnostics: Vec<diag::Diagnostic>,
    pub model: model::flowchart::Model,
}
pub fn parse(bytes: &[u8]) -> Result<Parsed, String> {
    let (source, first_bad) = elegant_mermaid::source::repair_utf8(bytes);
    let prep = syntax::preprocess::preprocess(&source);
    let detection = syntax::detect::detect(&source, &prep.removed);
    if let Some(kind) = detection.kind.filter(|k| *k != DiagramKind::Flowchart) {
        return Err(format!("unsupported diagram kind: {}", kind.id()));
    }
    let parsed = syntax::flowchart::parse(&source, &prep.removed);
    let (model, resolved) = model::flowchart::resolve(&source, &parsed.document);
    let mut diagnostics = prep.diagnostics;
    diagnostics.extend(detection.diagnostics);
    if detection.kind.is_some() {
        diagnostics.extend(parsed.diagnostics);
        diagnostics.extend(resolved);
    }
    if let Some(start) = first_bad {
        diagnostics.push(diag::Diagnostic {
            code: "source/invalid-utf8",
            severity: diag::Severity::Error,
            message: format!("invalid UTF-8 at byte {start}"),
            span: Span {
                start,
                end: start + '\u{fffd}'.len_utf8(),
            },
            related: Vec::new(),
            help: "Save the source as UTF-8.".into(),
            fixes: Vec::new(),
        });
    }
    diag::sort(&mut diagnostics);
    Ok(Parsed {
        source: source.into_owned(),
        kind: detection.kind,
        diagnostics,
        model,
    })
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
