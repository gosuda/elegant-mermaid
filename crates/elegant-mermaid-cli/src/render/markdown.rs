//! Render each block before committing any host or image output.

mod links;
mod output;

use crate::error::CliError;
use crate::{diagnostics, options};
use elegant_mermaid::config::EffectiveConfig;
use elegant_mermaid::markdown::{self, Block};
use elegant_mermaid::{Document, LayoutOptions, RasterError, RenderError, diag, source::Span};

struct Prepared<'src> {
    document: Document<'src>,
    config: EffectiveConfig,
}

struct Encoded {
    bytes: Vec<u8>,
    title: String,
}

pub(super) fn render(
    path: &str,
    bytes: &[u8],
    options: &options::Options,
    layout: &LayoutOptions,
    environment: &crate::view::Environment,
) -> Result<(Vec<u8>, String, i32), CliError> {
    let raw_blocks = markdown::blocks(bytes);
    if raw_blocks.is_empty() {
        return Ok((
            Vec::new(),
            format!(
                "no Mermaid blocks found in {path}; add a fenced code block labelled mermaid\n"
            ),
            1,
        ));
    }
    let (source, _) = elegant_mermaid::source::repair_utf8(bytes);
    let mapped_blocks = markdown::blocks(source.as_bytes());
    if raw_blocks.len() != mapped_blocks.len() {
        return Err(boundary_error(path));
    }

    // Documents own repaired text when needed. The repaired host supplies the
    // corresponding line maps; raw spans remain reserved for the final splice.
    let mut found = Vec::new();
    let prepared = prepare_blocks(path, &raw_blocks, &mapped_blocks, layout, &mut found)?;
    if diagnostics::has_errors(&found) {
        return Ok((
            Vec::new(),
            report(path, &source, &mut found, options, environment),
            1,
        ));
    }

    let encoded = encode_blocks(
        &prepared,
        &mapped_blocks,
        options,
        layout,
        environment,
        &mut found,
    );
    let mut stderr = report(path, &source, &mut found, options, environment);
    if diagnostics::has_errors(&found) {
        return Ok((Vec::new(), stderr, 1));
    }
    let encoded = match encoded {
        Ok(value) => value,
        Err(error) => {
            let code = if matches!(
                error,
                CliError::Render(RenderError::InvalidConfig { .. })
                    | CliError::Raster(RasterError::InvalidConfig { .. })
                    | CliError::UnsupportedKind
            ) {
                2
            } else {
                1
            };
            stderr.push_str(&format!("{error}\n"));
            return Ok((Vec::new(), stderr, code));
        }
    };
    if let Err(error) = output::write(path, bytes, &raw_blocks, options, &encoded) {
        stderr.push_str(&format!("{error}\n"));
        return Ok((Vec::new(), stderr, 2));
    }
    Ok((Vec::new(), stderr, 0))
}

fn prepare_blocks<'src>(
    path: &str,
    raw: &'src [Block<'_>],
    mapped: &[Block<'_>],
    layout: &LayoutOptions,
    found: &mut Vec<diag::Diagnostic>,
) -> Result<Vec<Prepared<'src>>, CliError> {
    let mut prepared = Vec::with_capacity(raw.len());
    for (raw, mapped) in raw.iter().zip(mapped) {
        let document = elegant_mermaid::parse_bytes(&raw.source);
        if document.source().as_bytes() != mapped.source.as_ref() {
            return Err(boundary_error(path));
        }
        let config = document.effective_config(layout.config.as_deref())?;
        found.extend(
            document
                .diagnostics_for(&config)
                .into_iter()
                .map(|diagnostic| host_diagnostic(mapped, diagnostic)),
        );
        prepared.push(Prepared { document, config });
    }
    Ok(prepared)
}

fn encode_blocks(
    prepared: &[Prepared<'_>],
    mapped: &[Block<'_>],
    options: &options::Options,
    layout: &LayoutOptions,
    environment: &crate::view::Environment,
    found: &mut Vec<diag::Diagnostic>,
) -> Result<Vec<Encoded>, CliError> {
    let mut encoded = Vec::with_capacity(prepared.len());
    for (prepared, mapped) in prepared.iter().zip(mapped) {
        let (scene, additional) =
            elegant_mermaid::layout_with_diagnostics(&prepared.document, layout)?;
        found.extend(
            additional
                .into_iter()
                .map(|diagnostic| host_diagnostic(mapped, diagnostic)),
        );
        let bytes = super::encoded_output(
            &scene,
            options,
            &prepared.document,
            &prepared.config,
            environment,
        )?;
        let model = prepared
            .document
            .resolved()
            .ok_or(CliError::UnsupportedKind)?;
        encoded.push(Encoded {
            bytes,
            title: model.accessibility().0.to_owned(),
        });
    }
    Ok(encoded)
}

fn boundary_error(path: &str) -> CliError {
    std::io::Error::new(
        std::io::ErrorKind::InvalidData,
        format!("cannot render {path}: Markdown block boundaries changed during UTF-8 repair"),
    )
    .into()
}

fn report(
    path: &str,
    source: &str,
    diagnostics: &mut [diag::Diagnostic],
    options: &options::Options,
    environment: &crate::view::Environment,
) -> String {
    diag::sort(diagnostics);
    crate::diagnostics::text(
        path,
        source,
        diagnostics,
        options::colour(&options.color, environment),
    )
}

fn host_diagnostic(block: &Block<'_>, mut diagnostic: diag::Diagnostic) -> diag::Diagnostic {
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
    diagnostic
}
