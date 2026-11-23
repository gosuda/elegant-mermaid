use crate::error::{CliError, UsageError};
use crate::{diagnostics, input, options};
use elegant_mermaid::syntax::config_value::{ConfigValue, parse_config_yaml};
use elegant_mermaid::{
    IconPack, IconPackError, LayoutOptions, Profile, RasterError, RenderError, cells,
    parse_icon_pack, raster, scene, svg,
};
use std::io::IsTerminal;

mod markdown;

pub fn run(args: &[String], environment: &crate::view::Environment) -> (Vec<u8>, String, i32) {
    match prepare(args, environment) {
        Ok(result) => result,
        Err(error) => (Vec::new(), format!("{error}\n"), 2),
    }
}
fn prepare(
    args: &[String],
    environment: &crate::view::Environment,
) -> Result<(Vec<u8>, String, i32), CliError> {
    let (o, paths) = options::parse("render", args)?;
    if paths.len() > 1 {
        return Err(UsageError::ExtraInput { command: "render" }.into());
    }
    if !paths.is_empty() && !o.input.is_empty() {
        return Err(UsageError::InputTwice.into());
    }
    let path = paths.first().cloned().unwrap_or_else(|| {
        if o.input.is_empty() {
            "-".into()
        } else {
            o.input.clone()
        }
    });
    let host = crate::check::markdown_host(std::path::Path::new(&path));
    let o = resolve_options(o, host, environment)?;
    if o.format == "png"
        && o.output.is_empty()
        && o.artefact_dir.is_none()
        && std::io::stdout().is_terminal()
    {
        return Err(UsageError::PngToTerminal.into());
    }
    let config = read_config(&o.config)?;
    let icon_packs = read_icon_packs(&o.icon_packs)?;
    let bytes = input::read(&path)?;
    let layout_options = LayoutOptions {
        profile: if o.format == "text" {
            Profile::Cell
        } else {
            Profile::Vector
        },
        theme: o.theme.clone(),
        max_width: o.width.unsigned_abs(),
        icon_packs,
        config,
        ..LayoutOptions::default()
    };
    if host {
        return markdown::render(&path, &bytes, &o, &layout_options, environment);
    }
    render_input(&path, &bytes, &o, &layout_options, environment)
}

fn render_input(
    path: &str,
    bytes: &[u8],
    options: &options::Options,
    layout_options: &LayoutOptions,
    environment: &crate::view::Environment,
) -> Result<(Vec<u8>, String, i32), CliError> {
    let document = elegant_mermaid::parse_bytes(bytes);
    let effective = document.effective_config(layout_options.config.as_deref())?;
    let source_diagnostics = document.diagnostics_for(&effective);
    let path = input::label(path);
    let mut stderr = diagnostics::text(
        path,
        document.source(),
        &source_diagnostics,
        options::colour(&options.color, environment),
    );
    if diagnostics::has_errors(&source_diagnostics) {
        return Ok((Vec::new(), stderr, 1));
    }
    if document.resolved().is_none() {
        return Err(CliError::UnsupportedKind);
    }
    let (scene, ds) = match elegant_mermaid::layout_with_diagnostics(&document, layout_options) {
        Ok(value) => value,
        Err(error @ RenderError::InvalidConfig { .. }) => return Err(error.into()),
        Err(error) => {
            stderr.push_str(&format!("{error}\n"));
            return Ok((Vec::new(), stderr, 1));
        }
    };
    stderr.push_str(&diagnostics::text(path, document.source(), &ds, false));
    let output = match encoded_output(&scene, options, &document, &effective, environment) {
        Ok(value) => value,
        Err(error @ CliError::Raster(RasterError::InvalidConfig { .. })) => return Err(error),
        Err(error) => {
            stderr.push_str(&format!("{error}\n"));
            return Ok((Vec::new(), stderr, 1));
        }
    };
    if options.output.is_empty() {
        return Ok((output, stderr, 0));
    }
    if let Err(source) =
        crate::output::write_file(std::path::Path::new(&options.output), &output, None)
    {
        let error = CliError::Write {
            path: options.output.clone(),
            source,
        };
        stderr.push_str(&format!("{error}\n"));
        return Ok((Vec::new(), stderr, 2));
    }
    Ok((Vec::new(), stderr, 0))
}
fn read_config(path: &str) -> Result<Option<String>, CliError> {
    if path.is_empty() {
        return Ok(None);
    }
    let bytes = std::fs::read(path).map_err(|error| input::read_error(path, error))?;
    let text = String::from_utf8(bytes).map_err(|error| CliError::InvalidConfig {
        path: path.to_owned(),
        message: format!("invalid UTF-8 at byte {}", error.utf8_error().valid_up_to()),
    })?;
    match site_config_failure(&text) {
        Some(message) => Err(CliError::InvalidConfig {
            path: path.to_owned(),
            message,
        }),
        None => Ok(Some(text)),
    }
}
fn site_config_failure(text: &str) -> Option<String> {
    if text.trim().is_empty() {
        return None;
    }
    let (value, diagnostics) = parse_config_yaml(text, 0, text.len());
    if let Some(first) = diagnostics.first() {
        return Some(first.message.clone());
    }
    if !matches!(value, ConfigValue::Mapping(_)) {
        return Some("config must be a mapping".to_owned());
    }
    elegant_mermaid::config::EffectiveConfig::read(&[&value])
        .1
        .into_iter()
        .find(|diagnostic| diagnostic.severity == elegant_mermaid::Severity::Error)
        .map(|diagnostic| diagnostic.message)
}
fn read_icon_packs(paths: &[String]) -> Result<Vec<IconPack>, CliError> {
    paths
        .iter()
        .map(|path| {
            let bytes = std::fs::read(path).map_err(|error| input::read_error(path, error))?;
            let malformed = |source: IconPackError| CliError::MalformedIconPack {
                path: path.clone(),
                source,
            };
            let text = String::from_utf8(bytes).map_err(|_| {
                malformed(IconPackError::Malformed {
                    reason: "invalid UTF-8".to_owned(),
                })
            })?;
            parse_icon_pack(&text).map_err(malformed)
        })
        .collect()
}
fn resolve_options(
    mut options: options::Options,
    host: bool,
    environment: &crate::view::Environment,
) -> Result<options::Options, UsageError> {
    if !host && options.artefact_dir.is_some() {
        return Err(UsageError::ArtefactsNeedMarkdown);
    }
    if host {
        if options.output.is_empty() && options.artefact_dir.is_none() {
            return Err(UsageError::MarkdownNeedsOutput);
        }
        if crate::check::markdown_host(std::path::Path::new(&options.output)) {
            if options.format.is_empty() {
                options.format = "svg".into();
            }
            options::choice(&options.format, "-e", &["svg", "png"])?;
        }
    }
    options::resolve(&mut options, environment)?;
    Ok(options)
}

fn encoded_output(
    scene: &scene::Scene,
    options: &options::Options,
    document: &elegant_mermaid::Document<'_>,
    config: &elegant_mermaid::config::EffectiveConfig,
    environment: &crate::view::Environment,
) -> Result<Vec<u8>, CliError> {
    match options.format.as_str() {
        "svg" => svg_output(scene, options, document, config).map(String::into_bytes),
        "png" => png_output(scene, options).map_err(CliError::from),
        _ => text_output(scene, options, environment).map(String::into_bytes),
    }
}
fn svg_output(
    scene: &scene::Scene,
    o: &options::Options,
    document: &elegant_mermaid::Document<'_>,
    config: &elegant_mermaid::config::EffectiveConfig,
) -> Result<String, CliError> {
    let model = document.resolved().ok_or(CliError::UnsupportedKind)?;
    let (title, description, kind) = model.accessibility();
    let links = model.links();
    let paths = o.svg_text == "paths";
    let outlines = paths.then(raster::inter_outlines);
    let mut output = String::new();
    svg::write(
        &mut output,
        scene,
        &svg::Options {
            theme: &o.theme,
            background: &o.background,
            kind,
            text: if paths {
                svg::TextMode::Paths
            } else {
                svg::TextMode::Font
            },
            outlines: outlines.as_ref(),
            title,
            description,
            links: &links,
            look: config.look(),
            font_family: config.font_family(),
            ..svg::Options::default()
        },
    )?;
    Ok(output)
}
fn png_output(scene: &scene::Scene, o: &options::Options) -> Result<Vec<u8>, RasterError> {
    let options = raster::PngOptions {
        scale: u32::try_from(o.scale).map_err(|_| RasterError::InvalidConfig { errors: 1 })?,
        background: o.background.clone(),
    };
    let image = raster::rgba(scene, &options, &o.theme)?;
    raster::encode_rgba(image.width, image.height, image.pixels)
}
fn text_output(
    scene: &scene::Scene,
    o: &options::Options,
    environment: &crate::view::Environment,
) -> Result<String, CliError> {
    let charset = if o.charset == "ascii" {
        cells::Charset::Ascii
    } else {
        cells::Charset::Unicode
    };
    cells::render(
        scene,
        &cells::render::Options {
            charset,
            color: options::depth(&o.color, environment),
            theme: o.theme.clone(),
        },
    )
    .map(|r| r.text)
    .map_err(CliError::from)
}
