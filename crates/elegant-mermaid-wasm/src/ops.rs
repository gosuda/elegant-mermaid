use crate::options::{Op, Options};
use crate::report::{self, Report};
use crate::response::Response;
use elegant_mermaid::{
    Document, FixSafety, LayoutOptions, Profile, Scene, cells, layout, model, scene, svg,
};

pub fn run(op: Op, source: &str, options: &Options) -> Response {
    match op {
        Op::Version => version(),
        Op::Check => check(source),
        Op::Lint => lint(source, options),
        Op::Fix => fix(source, options),
        Op::RenderSvg => rendered(source, |document| svg_output(document, options)),
        Op::RenderText => rendered(source, |document| text_output(document, options)),
        Op::Layout => rendered(source, |document| layout_output(document, options)),
    }
}

fn version() -> Response {
    Response {
        ok: true,
        output: format!("emd {}\n", env!("CARGO_PKG_VERSION")),
        diagnostics: "[]".to_owned(),
        applied: 0,
    }
}

fn check(source: &str) -> Response {
    let document = elegant_mermaid::parse(source);
    reported(report::syntax(&document))
}

fn lint(source: &str, options: &Options) -> Response {
    let document = elegant_mermaid::parse(source);
    reported(report::linted(&document, &options.lint))
}

fn fix(source: &str, options: &Options) -> Response {
    let max = if options.unsafe_fixes {
        FixSafety::Unsafe
    } else {
        FixSafety::Safe
    };
    let outcome = elegant_mermaid::apply_fixes(source.as_bytes(), &options.lint, max);
    let document = elegant_mermaid::parse(&outcome.text);
    let report = report::linted(&document, &options.lint);
    Response {
        ok: true,
        output: outcome.text,
        diagnostics: report.diagnostics,
        applied: outcome.applied,
    }
}

fn reported(report: Report) -> Response {
    Response {
        ok: !report.failed,
        output: report.document,
        diagnostics: report.diagnostics,
        applied: 0,
    }
}

fn rendered(source: &str, produce: impl FnOnce(&Document<'_>) -> Option<String>) -> Response {
    let document = elegant_mermaid::parse(source);
    let report = report::syntax(&document);
    let output = if report.failed {
        None
    } else {
        produce(&document)
    };
    Response {
        ok: output.is_some(),
        output: output.unwrap_or_default(),
        diagnostics: report.diagnostics,
        applied: 0,
    }
}

fn laid_out(document: &Document<'_>, options: &Options, profile: Profile) -> Option<Scene> {
    document.resolved()?;
    let layout_options = LayoutOptions {
        profile,
        theme: options.theme.clone(),
        max_width: options.width,
        ..LayoutOptions::default()
    };
    elegant_mermaid::layout_with_diagnostics(document, &layout_options)
        .ok()
        .map(|(scene, _)| scene)
}

fn background_valid(background: &str) -> bool {
    let Some(digits) = background.strip_prefix('#') else {
        return background.is_empty();
    };
    matches!(digits.len(), 3 | 6) && digits.bytes().all(|byte| byte.is_ascii_hexdigit())
}

fn svg_output(document: &Document<'_>, options: &Options) -> Option<String> {
    if !background_valid(&options.background) {
        return None;
    }
    let scene = laid_out(document, options, Profile::Vector)?;
    let resolved = document.resolved()?;
    let (title, description, kind) = resolved.accessibility();
    let links = resolved.links();
    let mut output = String::new();
    svg::write(
        &mut output,
        &scene,
        &svg::Options {
            theme: &options.theme,
            background: &options.background,
            kind,
            text: svg::TextMode::Font,
            outlines: None,
            title,
            description,
            links: &links,
            look: document.look(),
            ..svg::Options::default()
        },
    )
    .ok()?;
    Some(output)
}

fn text_output(document: &Document<'_>, options: &Options) -> Option<String> {
    let scene = laid_out(document, options, Profile::Cell)?;
    let charset = if options.ascii {
        cells::Charset::Ascii
    } else {
        cells::Charset::Unicode
    };
    cells::render(
        &scene,
        &cells::render::Options {
            charset,
            color: cells::ColorMode::None,
            theme: options.theme.clone(),
        },
    )
    .ok()
    .map(|rendered| rendered.text)
}

fn layout_output(document: &Document<'_>, options: &Options) -> Option<String> {
    let resolved: &model::Resolved = document.resolved()?;
    let profile = if options.cell {
        scene::Profile::Cell
    } else {
        scene::Profile::Vector
    };
    let input = resolved
        .input(profile, scene::DumpOptions::default())
        .ok()?;
    if options.model {
        return Some(layout::modeldump::model_dump(&input));
    }
    let (laid, _) = layout::families::layout(&input).ok()?;
    Some(laid.dump())
}
