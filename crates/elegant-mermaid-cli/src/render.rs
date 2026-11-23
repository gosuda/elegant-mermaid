use crate::error::{CliError, UsageError};
use crate::{diagnostics, input, options};
use elegant_mermaid::syntax::config_value::{ConfigValue, parse_config_yaml};
use elegant_mermaid::{
    IconPack, IconPackError, LayoutOptions, Profile, RasterError, RenderError, cells,
    parse_icon_pack, raster, scene, svg,
};
use std::io::IsTerminal;

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
    let o = resolve_options(o, environment)?;
    if o.format == "png" && o.output.is_empty() && std::io::stdout().is_terminal() {
        return Err(UsageError::PngToTerminal.into());
    }
    let path = paths
        .first()
        .map(String::as_str)
        .unwrap_or(if o.input.is_empty() { "-" } else { &o.input });
    let config = read_config(&o.config)?;
    let icon_packs = read_icon_packs(&o.icon_packs)?;
    let bytes = input::read(path)?;
    let document = elegant_mermaid::parse_bytes(&bytes);
    let effective = document.effective_config(config.as_deref())?;
    let source_diagnostics = document.diagnostics_for(&effective);
    let path = input::label(path);
    let mut stderr = diagnostics::text(
        path,
        document.source(),
        &source_diagnostics,
        options::colour(&o.color, environment),
    );
    if diagnostics::has_errors(&source_diagnostics) {
        return Ok((Vec::new(), stderr, 1));
    }
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
    if document.resolved().is_none() {
        return Err(CliError::UnsupportedKind);
    }
    let (scene, ds) = match elegant_mermaid::layout_with_diagnostics(&document, &layout_options) {
        Ok(value) => value,
        Err(error @ RenderError::InvalidConfig { .. }) => return Err(error.into()),
        Err(error) => {
            stderr.push_str(&format!("{error}\n"));
            return Ok((Vec::new(), stderr, 1));
        }
    };
    stderr.push_str(&diagnostics::text(path, document.source(), &ds, false));
    let rendered = match o.format.as_str() {
        "svg" => svg_output(&scene, &o, &document, &effective).map(String::into_bytes),
        "png" => match png_output(&scene, &o) {
            Err(error @ RasterError::InvalidConfig { .. }) => return Err(error.into()),
            other => other.map_err(CliError::from),
        },
        _ => text_output(&scene, &o, environment).map(String::into_bytes),
    };
    let output = match rendered {
        Ok(value) => value,
        Err(error) => {
            stderr.push_str(&format!("{error}\n"));
            return Ok((Vec::new(), stderr, 1));
        }
    };
    if o.output.is_empty() {
        return Ok((output, stderr, 0));
    }
    crate::output::write_file(std::path::Path::new(&o.output), &output, None).map_err(
        |source| CliError::Write {
            path: o.output.clone(),
            source,
        },
    )?;
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
    environment: &crate::view::Environment,
) -> Result<options::Options, UsageError> {
    options::resolve(&mut options, environment)?;
    Ok(options)
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
