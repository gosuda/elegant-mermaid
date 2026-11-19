//! The output formats of `check` and `lint` for a list of files: text, JSON,
//! SARIF, and GitHub workflow commands.

use elegant_mermaid::{
    Diagnostic, diag,
    diag::document::{FileDiagnostics, push_document},
    diag::sarif::{SarifFile, push_sarif},
    source::LineIndex,
};

/// One checked or linted file. `diagnostics` hold spans into `source`.
pub struct File<'a> {
    pub path: &'a str,
    pub kind: Option<&'a str>,
    pub source: &'a str,
    pub diagnostics: &'a [Diagnostic],
}

fn indexes(files: &[File<'_>]) -> Vec<LineIndex> {
    files.iter().map(|f| LineIndex::new(f.source)).collect()
}

pub fn json(files: &[File<'_>]) -> String {
    let indexes = indexes(files);
    let mut entries: Vec<FileDiagnostics<'_>> = files
        .iter()
        .zip(&indexes)
        .map(|(f, index)| FileDiagnostics {
            path: f.path,
            kind: f.kind,
            index,
            diagnostics: f.diagnostics,
        })
        .collect();
    let mut out = String::new();
    push_document(&mut out, &mut entries);
    out
}

pub fn sarif(files: &[File<'_>]) -> String {
    let indexes = indexes(files);
    let entries: Vec<SarifFile<'_>> = files
        .iter()
        .zip(&indexes)
        .map(|(f, index)| SarifFile {
            path: f.path,
            index,
            diagnostics: f.diagnostics,
        })
        .collect();
    let mut out = String::new();
    push_sarif(&mut out, env!("CARGO_PKG_VERSION"), &entries);
    out
}

pub fn github(files: &[File<'_>]) -> String {
    let indexes = indexes(files);
    let mut order: Vec<usize> = (0..files.len()).collect();
    order.sort_by(|&a, &b| files[a].path.as_bytes().cmp(files[b].path.as_bytes()));
    let mut out = String::new();
    for at in order {
        diag::github::push_github(
            &mut out,
            files[at].path,
            &indexes[at],
            files[at].diagnostics,
        );
    }
    out
}

/// The `lint` text format: files in byte-wise path order, files without
/// diagnostics skipped, one blank line between files.
pub fn text(files: &[File<'_>], colour: bool) -> String {
    let mut order: Vec<&File<'_>> = files.iter().collect();
    order.sort_by(|a, b| a.path.as_bytes().cmp(b.path.as_bytes()));
    let mut out = String::new();
    for file in order {
        if file.diagnostics.is_empty() {
            continue;
        }
        if !out.is_empty() {
            out.push('\n');
        }
        let mut sorted = file.diagnostics.to_vec();
        diag::sort(&mut sorted);
        out.push_str(&crate::diagnostics::text(
            file.path,
            file.source,
            &sorted,
            colour,
        ));
    }
    out
}
