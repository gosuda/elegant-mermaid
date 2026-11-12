use crate::{diagnostics, input, options};
use elegant_mermaid::{
    DiagramKind, diag, markdown,
    source::{LineIndex, Span},
};
use std::path::Path;

struct Checked {
    source: String,
    kind: Option<DiagramKind>,
    diagnostics: Vec<diag::Diagnostic>,
}

fn markdown_host(path: &Path) -> bool {
    path.extension()
        .is_some_and(|e| e == "md" || e == "markdown" || e == "mdx")
}

fn check_input(path: &str, bytes: &[u8]) -> Result<Checked, String> {
    if !markdown_host(Path::new(path)) {
        let parsed = diagnostics::parse(bytes)?;
        return Ok(Checked {
            source: parsed.source,
            kind: parsed.kind,
            diagnostics: parsed.diagnostics,
        });
    }
    let (source, first_bad) = elegant_mermaid::source::repair_utf8(bytes);
    let mut checked = Checked {
        source: source.into_owned(),
        kind: None,
        diagnostics: Vec::new(),
    };
    if let Some(start) = first_bad {
        checked.diagnostics.push(diag::Diagnostic {
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
    for block in markdown::blocks(checked.source.as_bytes()) {
        let parsed = diagnostics::parse(&block.source)?;
        for mut diagnostic in parsed.diagnostics {
            let map = |span: Span| Span {
                start: block.host_offset(span.start),
                end: block.host_offset(span.end),
            };
            diagnostic.span = map(diagnostic.span);
            for related in &mut diagnostic.related {
                related.span = map(related.span);
            }
            for fix in &mut diagnostic.fixes {
                for edit in &mut fix.edits {
                    edit.span = map(edit.span);
                }
            }
            checked.diagnostics.push(diagnostic);
        }
    }
    diag::sort(&mut checked.diagnostics);
    Ok(checked)
}

pub fn run(args: &[String]) -> (String, String, i32) {
    match check(args) {
        Ok(result) => result,
        Err(error) => (String::new(), format!("{error}\n"), 2),
    }
}
fn check(args: &[String]) -> Result<(String, String, i32), String> {
    let (o, paths) = options::parse("check", args)?;
    options::choice(&o.format, "--output-format", &["text", "json"])?;
    options::choice(&o.color, "--color", &["auto", "always", "never"])?;
    let inputs = collect(&paths)?;
    if inputs.is_empty() {
        return Ok((String::new(), "no Mermaid files found in .\n".into(), 0));
    }
    let mut parsed = Vec::new();
    for path in &inputs {
        parsed.push(check_input(path, &input::read(path)?)?);
    }
    let failed = parsed
        .iter()
        .any(|p| diagnostics::has_errors(&p.diagnostics));
    let output = if o.format == "json" {
        json(&inputs, &parsed)
    } else {
        inputs
            .iter()
            .zip(&parsed)
            .map(|(path, p)| {
                diagnostics::text(
                    input::label(path),
                    &p.source,
                    &p.diagnostics,
                    options::colour(&o.color),
                )
            })
            .collect()
    };
    Ok((output, String::new(), i32::from(failed)))
}
fn json(paths: &[String], parsed: &[Checked]) -> String {
    let indexes: Vec<_> = parsed.iter().map(|p| LineIndex::new(&p.source)).collect();
    let mut files: Vec<_> = paths
        .iter()
        .zip(parsed)
        .zip(&indexes)
        .map(|((path, p), index)| diag::document::FileDiagnostics {
            path: input::label(path),
            kind: p.kind.map(|k| k.id()),
            index,
            diagnostics: &p.diagnostics,
        })
        .collect();
    let mut output = String::new();
    diag::document::push_document(&mut output, &mut files);
    output
}
fn collect(paths: &[String]) -> Result<Vec<String>, String> {
    let implicit = paths.is_empty();
    let defaults = [String::from(".")];
    let roots = if implicit { &defaults[..] } else { paths };
    let mut inputs = Vec::new();
    for root in roots {
        let mut found = Vec::new();
        if root == "-" {
            found.push(root.clone());
        } else {
            walk(Path::new(root), &mut found)?;
        }
        if found.is_empty() && !implicit {
            return Err(format!("no Mermaid files found in {root}"));
        }
        inputs.extend(found);
    }
    inputs.sort();
    Ok(inputs)
}
fn walk(path: &Path, out: &mut Vec<String>) -> Result<(), String> {
    let metadata = std::fs::symlink_metadata(path)
        .map_err(|e| input::read_error(&path.to_string_lossy(), &e, "lstat"))?;
    if metadata.file_type().is_symlink() {
        return Ok(());
    }
    if metadata.is_dir() {
        return walk_dir(path, out);
    }
    if markdown_host(path)
        || path
            .extension()
            .is_some_and(|e| e == "mmd" || e == "mermaid")
    {
        out.push(path.to_string_lossy().into_owned());
    }
    Ok(())
}
fn walk_dir(path: &Path, out: &mut Vec<String>) -> Result<(), String> {
    let entries = std::fs::read_dir(path)
        .map_err(|e| input::read_error(&path.to_string_lossy(), &e, "open"))?;
    let mut entries = entries
        .collect::<Result<Vec<_>, _>>()
        .map_err(|e| input::read_error(&path.to_string_lossy(), &e, "readdirent"))?;
    entries.sort_by_key(|entry| entry.file_name());
    for entry in entries {
        let name = entry.file_name();
        if entry.file_type().map_err(|e| e.to_string())?.is_dir()
            && (name.to_string_lossy().starts_with('.')
                || name == "node_modules"
                || name == "target")
        {
            continue;
        }
        walk(&entry.path(), out)?;
    }
    Ok(())
}
