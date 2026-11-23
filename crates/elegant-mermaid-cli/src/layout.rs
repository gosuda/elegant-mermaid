use crate::error::{CliError, UsageError};
use elegant_mermaid::scene::metrics::DumpError;
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
    let scene = match read_dump(path) {
        Ok(scene) => scene,
        Err(error) => return (String::new(), format!("{error}\n"), 2),
    };
    match scene::metrics::measure(&scene, 0) {
        Ok(metrics) => (metrics.json(), String::new(), 0),
        Err(error) => (String::new(), format!("{error}\n"), 1),
    }
}

fn read_dump(path: &str) -> Result<scene::Scene, CliError> {
    let bytes = std::fs::read(path).map_err(|source| crate::input::read_error(path, source))?;
    let malformed = |source: DumpError| CliError::MalformedDump {
        path: path.to_owned(),
        source,
    };
    let text = String::from_utf8(bytes).map_err(|_| malformed(DumpError::from("invalid UTF-8")))?;
    scene::metrics::read_dump(&text).map_err(malformed)
}

fn arguments(args: &[OsString]) -> Result<Arguments, UsageError> {
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
        } else if flags && crate::options::is_flag(&argument) {
            set_flag(&argument, &mut iter, &mut options)?;
        } else {
            set_path(&argument, &mut path)?;
        }
    }
    validate_metrics_options(&options)?;
    options.path = path.unwrap_or_else(|| "-".into());
    Ok(options)
}

fn validate_metrics_options(options: &Arguments) -> Result<(), UsageError> {
    if options.metrics && options.profile == scene::Profile::Cell {
        return Err(UsageError::MetricsNeedVector);
    }
    if options.dump.is_some() && !options.metrics {
        return Err(UsageError::DumpNeedsMetrics);
    }
    Ok(())
}

fn set_path(argument: &str, path: &mut Option<String>) -> Result<(), UsageError> {
    if path.is_some() {
        return Err(UsageError::ExtraInput { command: "layout" });
    }
    *path = Some(argument.into());
    Ok(())
}

fn set_flag<'a>(
    argument: &str,
    rest: &mut impl Iterator<Item = &'a OsString>,
    options: &mut Arguments,
) -> Result<(), UsageError> {
    let unknown = || UsageError::UnknownFlag {
        flag: argument.to_owned(),
        command: "layout",
    };
    let flag = crate::options::split_flag(argument).ok_or_else(unknown)?;
    match flag.name {
        "metrics" => options.metrics = flag.switch()?,
        "stage" | "profile" | "dump" => {
            let value = flag.value(argument, || {
                rest.next().map(|text| text.to_string_lossy().into_owned())
            })?;
            set_option(flag.name, &value, options)?;
        }
        _ => return Err(unknown()),
    }
    Ok(())
}

fn set_option(name: &str, value: &str, options: &mut Arguments) -> Result<(), UsageError> {
    match (name, value) {
        ("dump", value) => options.dump = Some(value.into()),
        ("profile", "vector") => options.profile = scene::Profile::Vector,
        ("profile", "cell") => options.profile = scene::Profile::Cell,
        ("stage", "model") => options.stage = scene::Stage::Model,
        ("stage", "layout") => options.stage = scene::Stage::Layout,
        _ => {
            let values = if name == "profile" {
                "vector, cell"
            } else {
                "model, layout"
            };
            return Err(crate::options::invalid(value, &format!("--{name}"), values));
        }
    }
    Ok(())
}

fn render(options: &Arguments, bytes: &[u8]) -> (String, String, i32) {
    let parsed = crate::diagnostics::parse(bytes);
    let path = crate::input::label(&options.path);
    if crate::diagnostics::has_errors(&parsed.diagnostics) {
        return (
            String::new(),
            crate::diagnostics::text(path, &parsed.source, &parsed.diagnostics, false),
            1,
        );
    }
    let Some(model) = parsed.model.as_ref() else {
        return (String::new(), format!("{}\n", CliError::UnsupportedKind), 2);
    };
    let mut dump_options = scene::DumpOptions::default();
    parsed.config.apply_to(&mut dump_options);
    let input = match model.input(options.profile, dump_options) {
        Ok(input) => input,
        Err(error) => return (String::new(), format!("{error}\n"), 1),
    };
    if options.stage == scene::Stage::Model && !options.metrics {
        return (
            layout::modeldump::model_dump(&input),
            crate::diagnostics::text(path, &parsed.source, &parsed.diagnostics, false),
            0,
        );
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
            let mut stderr =
                crate::diagnostics::text(path, &parsed.source, &parsed.diagnostics, false);
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
) -> Result<String, CliError> {
    let input = model.input(scene::Profile::Cell, scene::DumpOptions::default())?;
    let (cell, _) = layout::families::layout(&input)?;
    let rendered = cells::render(&cell, &cells::Options::default())?;
    let mut metrics = scene::metrics::measure(vector, rendered.refused_clusters)?;
    metrics.hard_ok &= rendered.route_conflicts == 0;
    Ok(metrics.json())
}
