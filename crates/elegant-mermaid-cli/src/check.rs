use crate::error::CliError;
use crate::{diagnostics, input, options, report};
use elegant_mermaid::{DiagramKind, diag, markdown, source::Span};
use std::path::Path;

struct Checked {
    source: String,
    kind: Option<DiagramKind>,
    diagnostics: Vec<diag::Diagnostic>,
}

pub(crate) fn markdown_host(path: &Path) -> bool {
    path.extension()
        .is_some_and(|e| e == "md" || e == "markdown" || e == "mdx")
}

fn check_input(path: &str, bytes: &[u8]) -> Checked {
    if !markdown_host(Path::new(path)) {
        let parsed = diagnostics::parse(bytes);
        return Checked {
            source: parsed.source,
            kind: parsed.kind,
            diagnostics: parsed.diagnostics,
        };
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
        let parsed = diagnostics::parse(&block.source);
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
    checked
}

pub fn run(args: &[String], environment: &crate::view::Environment) -> (String, String, i32) {
    match check(args, environment) {
        Ok(result) => result,
        Err(error) => (String::new(), format!("{error}\n"), 2),
    }
}
fn check(
    args: &[String],
    environment: &crate::view::Environment,
) -> Result<(String, String, i32), CliError> {
    let (o, paths) = options::parse("check", args)?;
    options::choice(
        &o.format,
        "--output-format",
        &["text", "json", "sarif", "github"],
    )?;
    options::choice(&o.color, "--color", &["auto", "always", "never"])?;
    let inputs = collect(&paths)?;
    if inputs.is_empty() {
        return Ok((String::new(), "no Mermaid files found in .\n".into(), 0));
    }
    let mut parsed = Vec::new();
    for path in &inputs {
        parsed.push(check_input(path, &input::read(path)?));
    }
    let failed = parsed
        .iter()
        .any(|p| diagnostics::has_errors(&p.diagnostics));
    let output = if o.format == "text" {
        inputs
            .iter()
            .zip(&parsed)
            .map(|(path, p)| {
                diagnostics::text(
                    input::label(path),
                    &p.source,
                    &p.diagnostics,
                    options::colour(&o.color, environment),
                )
            })
            .collect()
    } else {
        machine(&o.format, &inputs, &parsed)
    };
    Ok((output, String::new(), i32::from(failed)))
}
fn machine(format: &str, paths: &[String], parsed: &[Checked]) -> String {
    let files: Vec<report::File<'_>> = paths
        .iter()
        .zip(parsed)
        .map(|(path, p)| report::File {
            path: input::label(path),
            kind: p.kind.map(DiagramKind::id),
            source: &p.source,
            diagnostics: &p.diagnostics,
        })
        .collect();
    match format {
        "json" => report::json(&files),
        "sarif" => report::sarif(&files),
        _ => report::github(&files),
    }
}
pub(crate) fn collect(paths: &[String]) -> Result<Vec<String>, CliError> {
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
            return Err(CliError::NoFiles { root: root.clone() });
        }
        inputs.extend(found);
    }
    inputs.sort();
    Ok(inputs)
}
fn walk(path: &Path, out: &mut Vec<String>) -> Result<(), CliError> {
    let metadata = std::fs::symlink_metadata(path)
        .map_err(|e| input::read_error(&path.to_string_lossy(), e))?;
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
fn walk_dir(path: &Path, out: &mut Vec<String>) -> Result<(), CliError> {
    let entries =
        std::fs::read_dir(path).map_err(|e| input::read_error(&path.to_string_lossy(), e))?;
    let mut entries = entries
        .collect::<Result<Vec<_>, _>>()
        .map_err(|e| input::read_error(&path.to_string_lossy(), e))?;
    entries.sort_by_key(|entry| entry.file_name());
    for entry in entries {
        let name = entry.file_name();
        if entry.file_type()?.is_dir()
            && (name.to_string_lossy().starts_with('.')
                || name == "node_modules"
                || name == "target")
        {
            continue;
        }
        let child = crate::paths::join(&path.to_string_lossy(), &name.to_string_lossy());
        walk(Path::new(&child), out)?;
    }
    Ok(())
}
