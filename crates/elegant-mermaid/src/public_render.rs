use crate::{
    Diagnostic, Document, LayoutOptions, Profile, RenderError, Scene, Severity, SvgOptions,
    TextOptions,
};

/// Lay out a parsed diagram with deterministic integer geometry.
pub fn layout(document: &Document<'_>, options: &LayoutOptions) -> Result<Scene, RenderError> {
    layout_with_diagnostics(document, options).map(|(scene, _)| scene)
}

/// Lay out a parsed diagram and return the layout-stage diagnostics with the scene.
pub fn layout_with_diagnostics(
    document: &Document<'_>,
    options: &LayoutOptions,
) -> Result<(Scene, Vec<Diagnostic>), RenderError> {
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
    let max = i32::MAX.unsigned_abs();
    if !(1..=5).contains(&options.thoroughness)
        || options.max_width > max
        || [
            options.limits.max_nodes,
            options.limits.max_edges,
            options.limits.max_text_bytes,
        ]
        .into_iter()
        .any(|limit| !(1..=max).contains(&limit))
    {
        return Err(RenderError::InvalidConfig { errors: 1 });
    }
    crate::theme::resolve(&options.theme).map_err(|_| RenderError::InvalidConfig { errors: 1 })?;
    crate::config::look_with(document.look(), options.config.as_deref())?;
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
    let (mut scene, mut diagnostics) = crate::layout::families::layout(&input)?;
    if input.kind == "treeview" {
        diagnostics.extend(
            crate::layout::treeview::place_icons(&input, &mut scene, &options.icon_packs).map_err(
                |error| match error {
                    crate::geom::GeomError::Overflow => RenderError::Overflow,
                    crate::geom::GeomError::Domain => RenderError::InvalidConfig { errors: 1 },
                },
            )?,
        );
    } else {
        diagnostics.extend(crate::icons::place(
            &mut scene,
            &model.icon_refs(),
            &options.icon_packs,
        ));
    }
    if options.cancel.is_cancelled() {
        return Err(RenderError::Cancelled);
    }
    Ok((scene, diagnostics))
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
    let links = model.links();
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
            outlines: options.outlines.as_ref(),
            id_prefix: &options.id_prefix,
            title,
            description,
            kind,
            font_family: "",
            links: &links,
            look: crate::config::look_with(document.look(), options.layout.config.as_deref())?,
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
