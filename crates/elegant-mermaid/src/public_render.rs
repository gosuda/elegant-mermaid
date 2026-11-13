use crate::{
    Document, LayoutOptions, Profile, RenderError, Scene, Severity, SvgOptions, TextOptions,
};

/// Lay out a parsed flowchart with deterministic integer geometry.
pub fn layout(document: &Document<'_>, options: &LayoutOptions) -> Result<Scene, RenderError> {
    if options.cancel.is_cancelled() {
        return Err(RenderError::Cancelled);
    }
    let errors = document
        .diagnostics()
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .count();
    if errors != 0 {
        return Err(RenderError::InvalidDocument { errors });
    }
    if !(1..=5).contains(&options.thoroughness)
        || options.limits.max_nodes == 0
        || options.limits.max_edges == 0
        || options.limits.max_text_bytes == 0
    {
        return Err(RenderError::InvalidConfig { errors: 1 });
    }
    crate::theme::resolve(&options.theme).map_err(|_| RenderError::InvalidConfig { errors: 1 })?;
    if let Some(config) = &options.config {
        let parsed = crate::syntax::config_value::parse_yaml_doc(config, 0, config.len());
        if parsed.stop {
            return Err(RenderError::InvalidConfig { errors: 1 });
        }
        if !parsed.diagnostics.is_empty() {
            return Err(RenderError::InvalidConfig {
                errors: parsed.diagnostics.len(),
            });
        }
        if !matches!(
            parsed.value,
            crate::syntax::config_value::ConfigValue::Mapping(_)
        ) {
            return Err(RenderError::InvalidConfig { errors: 1 });
        }
    }
    let profile = match options.profile {
        Profile::Vector => crate::scene::Profile::Vector,
        Profile::Cell => crate::scene::Profile::Cell,
    };
    let dump = crate::scene::DumpOptions {
        profile,
        thoroughness: options.thoroughness,
        max_width: if profile == crate::scene::Profile::Cell {
            options.max_width
        } else {
            0
        },
        limits: crate::scene::Limits {
            max_nodes: options.limits.max_nodes,
            max_edges: options.limits.max_edges,
            max_text_bytes: options.limits.max_text_bytes,
        },
        ..crate::scene::DumpOptions::default()
    };
    let model = document
        .model
        .as_ref()
        .ok_or(RenderError::InvalidConfig { errors: 1 })?;
    let input = model
        .input(profile, dump)
        .map_err(|_| RenderError::Overflow)?;
    let (scene, _) = crate::layout::families::layout(&input)?;
    if options.cancel.is_cancelled() {
        return Err(RenderError::Cancelled);
    }
    Ok(scene)
}

pub fn render_svg(document: &Document<'_>, options: &SvgOptions) -> Result<String, RenderError> {
    let mut layout_options = options.layout.clone();
    layout_options.profile = Profile::Vector;
    let scene = layout(document, &layout_options)?;
    let model = document
        .model
        .as_ref()
        .ok_or(RenderError::InvalidConfig { errors: 1 })?;
    let (title, description, kind) = model.accessibility();
    let text = match options.text {
        crate::TextMode::Font => crate::svg::TextMode::Font,
        crate::TextMode::Paths => crate::svg::TextMode::Paths,
    };
    let mut output = String::new();
    crate::svg::write(
        &mut output,
        &scene,
        &crate::svg::Options {
            theme: &options.layout.theme,
            background: &options.background,
            text,
            id_prefix: &options.id_prefix,
            title,
            description,
            kind,
            font_family: "",
            links: &[],
        },
    )
    .map_err(|error| match error {
        crate::svg::ConfigError::Overflow => RenderError::Overflow,
        _ => RenderError::InvalidConfig { errors: 1 },
    })?;
    if options.layout.cancel.is_cancelled() {
        return Err(RenderError::Cancelled);
    }
    Ok(output)
}

pub fn render_svg_str(source: &str, options: &SvgOptions) -> Result<String, RenderError> {
    if options.layout.cancel.is_cancelled() {
        return Err(RenderError::Cancelled);
    }
    render_svg(&crate::parse(source), options)
}

pub fn render_text(document: &Document<'_>, options: &TextOptions) -> Result<String, RenderError> {
    let mut layout_options = options.layout.clone();
    layout_options.profile = Profile::Cell;
    let scene = layout(document, &layout_options)?;
    let output = crate::cells::render::render(
        &scene,
        &crate::cells::render::Options {
            charset: match options.charset {
                crate::Charset::Unicode => crate::cells::Charset::Unicode,
                crate::Charset::Ascii => crate::cells::Charset::Ascii,
            },
            color: match options.color {
                crate::ColorMode::None => crate::cells::ColorMode::None,
                crate::ColorMode::Ansi16 => crate::cells::ColorMode::Ansi16,
                crate::ColorMode::Ansi256 => crate::cells::ColorMode::Ansi256,
                crate::ColorMode::Truecolor => crate::cells::ColorMode::Truecolor,
            },
            theme: options.layout.theme.clone(),
        },
    )
    .map_err(|error| match error {
        crate::cells::render::RenderError::Geometry(crate::geom::GeomError::Overflow) => {
            RenderError::Overflow
        }
        _ => RenderError::InvalidConfig { errors: 1 },
    })?;
    if options.layout.cancel.is_cancelled() {
        return Err(RenderError::Cancelled);
    }
    Ok(output.text)
}

pub fn render_text_str(source: &str, options: &TextOptions) -> Result<String, RenderError> {
    if options.layout.cancel.is_cancelled() {
        return Err(RenderError::Cancelled);
    }
    render_text(&crate::parse(source), options)
}
