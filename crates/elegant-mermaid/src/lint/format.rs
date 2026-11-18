use crate::diag::Diagnostic;
use crate::diag::document::{FileDiagnostics, push_document};
use crate::diag::github;
use crate::diag::sarif::{SarifFile, push_sarif};
use crate::diag::text::{TextFrameOptions, render_text};
use crate::source::LineIndex;

pub fn text(out: &mut String, path: &str, source: &str, diagnostics: &[Diagnostic], colour: bool) {
    render_text(
        out,
        path,
        source,
        diagnostics,
        &TextFrameOptions {
            colour,
            width: |_| 1,
        },
    );
}

pub fn json(
    out: &mut String,
    path: &str,
    kind: Option<&str>,
    source: &str,
    diagnostics: &[Diagnostic],
) {
    let index = LineIndex::new(source);
    let mut files = [FileDiagnostics {
        path,
        kind,
        index: &index,
        diagnostics,
    }];
    push_document(out, &mut files);
}

pub fn sarif(out: &mut String, path: &str, source: &str, diagnostics: &[Diagnostic]) {
    let index = LineIndex::new(source);
    let files = [SarifFile {
        path,
        index: &index,
        diagnostics,
    }];
    push_sarif(out, env!("CARGO_PKG_VERSION"), &files);
}

pub fn github(out: &mut String, path: &str, source: &str, diagnostics: &[Diagnostic]) {
    let index = LineIndex::new(source);
    github::push_github(out, path, &index, diagnostics);
}
