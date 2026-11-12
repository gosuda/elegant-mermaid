use elegant_mermaid::{cells, diag, layout, scene};
use std::ffi::OsString;

struct Arguments {
    path: String,
    profile: scene::Profile,
    stage: scene::Stage,
    metrics: bool,
    dump: Option<String>,
}

pub fn run(args: &[OsString]) -> (String, String, i32) {
    match arguments(args) {
        Ok(options) => execute(options),
        Err(error) => (String::new(), format!("{error}\n"), 2),
    }
}

fn execute(options: Arguments) -> (String, String, i32) {
    if let Some(path) = &options.dump {
        return dump_metrics(path);
    }
    match crate::input::read(&options.path) {
        Ok(bytes) => render(&options, &bytes),
        Err(error) => (String::new(), format!("{error}\n"), 2),
    }
}

fn dump_metrics(path: &str) -> (String, String, i32) {
    let source = match std::fs::read_to_string(path) {
        Ok(source) => source,
        Err(error) => return (String::new(), format!("cannot read {path}: {error}\n"), 2),
    };
    let scene = match scene::metrics::read_dump(&source) {
        Ok(scene) => scene,
        Err(error) => return (String::new(), format!("{error}\n"), 2),
    };
    match scene::metrics::measure(&scene, 0) {
        Ok(metrics) => (metrics.json(), String::new(), 0),
        Err(error) => (String::new(), format!("{error}\n"), 1),
    }
}

fn arguments(args: &[OsString]) -> Result<Arguments, String> {
    let mut path = None;
    let mut options = Arguments {
        path: String::new(),
        profile: scene::Profile::Vector,
        stage: scene::Stage::Layout,
        metrics: false,
        dump: None,
    };
    let mut flags = true;
    let mut iter = args.iter();
    while let Some(argument) = iter.next() {
        let argument = argument.to_string_lossy();
        if flags && argument == "--" {
            flags = false;
            continue;
        }
        if flags && argument == "--metrics" {
            options.metrics = true;
            continue;
        }
        if flags && matches!(argument.as_ref(), "--stage" | "--profile" | "--dump") {
            let value = iter
                .next()
                .ok_or_else(|| format!("missing value for {argument}"))?;
            set_option(&argument, &value.to_string_lossy(), &mut options)?;
        } else {
            set_path(&argument, flags, &mut path)?;
        }
    }
    validate_metrics_options(&options)?;
    options.path = path.unwrap_or_else(|| "-".into());
    Ok(options)
}

fn validate_metrics_options(options: &Arguments) -> Result<(), String> {
    if options.metrics && options.profile == scene::Profile::Cell {
        return Err("--metrics needs --profile vector".into());
    }
    if options.dump.is_some() && !options.metrics {
        return Err("--dump requires --metrics".into());
    }
    Ok(())
}

fn set_path(argument: &str, flags: bool, path: &mut Option<String>) -> Result<(), String> {
    if flags && argument.len() > 1 && argument.starts_with('-') {
        return Err(format!("unknown flag {argument}; run emd layout --help"));
    }
    if path.is_some() {
        return Err("layout accepts one INPUT".into());
    }
    *path = Some(argument.into());
    Ok(())
}

fn set_option(flag: &str, value: &str, options: &mut Arguments) -> Result<(), String> {
    match (flag, value) {
        ("--dump", value) => options.dump = Some(value.into()),
        ("--profile", "vector") => options.profile = scene::Profile::Vector,
        ("--profile", "cell") => options.profile = scene::Profile::Cell,
        ("--stage", "model") => options.stage = scene::Stage::Model,
        ("--stage", "layout") => options.stage = scene::Stage::Layout,
        _ => {
            let values = if flag == "--profile" {
                "vector, cell"
            } else {
                "model, layout"
            };
            return Err(format!(
                "invalid value {value} for {flag}; expected one of: {values}"
            ));
        }
    }
    Ok(())
}

fn render(options: &Arguments, bytes: &[u8]) -> (String, String, i32) {
    let parsed = match crate::diagnostics::parse(bytes) {
        Ok(parsed) => parsed,
        Err(error) => return (String::new(), format!("{error}\n"), 2),
    };
    let path = crate::input::label(&options.path);
    if crate::diagnostics::has_errors(&parsed.diagnostics) {
        return (
            String::new(),
            crate::diagnostics::text(path, &parsed.source, &parsed.diagnostics, false),
            1,
        );
    }
    let Some(model) = parsed.model.as_ref() else {
        return (String::new(), "unsupported diagram kind\n".into(), 2);
    };
    let input = match model.input(options.profile, scene::DumpOptions::default()) {
        Ok(input) => input,
        Err(error) => return (String::new(), format!("{error}\n"), 1),
    };
    if options.stage == scene::Stage::Model && !options.metrics {
        return (layout::modeldump::model_dump(&input), String::new(), 0);
    }
    let (scene, diagnostics) = match layout::families::layout(&input) {
        Ok(result) => result,
        Err(error) => return (String::new(), format!("{error}\n"), 1),
    };
    let output = if options.metrics {
        model_metrics(model, &scene)
    } else {
        Ok(scene.dump())
    };
    match output {
        Ok(output) => {
            let mut stderr = String::new();
            diag::text::render_text(
                &mut stderr,
                path,
                &parsed.source,
                &diagnostics,
                &diag::text::TextFrameOptions {
                    colour: false,
                    width: |_| 1,
                },
            );
            (output, stderr, 0)
        }
        Err(error) => (String::new(), format!("{error}\n"), 1),
    }
}

fn model_metrics(
    model: &elegant_mermaid::model::Resolved,
    vector: &scene::Scene,
) -> Result<String, String> {
    let input = model
        .input(scene::Profile::Cell, scene::DumpOptions::default())
        .map_err(|error| error.to_string())?;
    let (cell, _) = layout::families::layout(&input).map_err(|e| e.to_string())?;
    let rendered = cells::render(&cell, &cells::Options::default()).map_err(|e| e.to_string())?;
    let mut metrics =
        scene::metrics::measure(vector, rendered.refused_clusters).map_err(|e| e.to_string())?;
    metrics.hard_ok &= rendered.route_conflicts == 0;
    Ok(metrics.json())
}
