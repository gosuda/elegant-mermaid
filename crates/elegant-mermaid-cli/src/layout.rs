use elegant_mermaid::{diag, layout, scene, syntax};
use std::ffi::OsString;
use std::io::Read;

pub fn run(args: &[OsString]) -> (String, String, i32) {
    match arguments(args).and_then(|(path, profile)| read_source(&path).map(|s| (path, profile, s)))
    {
        Ok((path, profile, bytes)) => render(&path, profile, &bytes),
        Err(error) => (String::new(), format!("{error}\n"), 2),
    }
}

fn read_source(path: &str) -> Result<Vec<u8>, String> {
    if path != "-" {
        return std::fs::read(path).map_err(|e| e.to_string());
    }
    let mut bytes = Vec::new();
    std::io::stdin()
        .read_to_end(&mut bytes)
        .map_err(|e| e.to_string())?;
    Ok(bytes)
}

fn arguments(args: &[OsString]) -> Result<(String, scene::Profile), String> {
    let mut path = None;
    let mut profile = scene::Profile::Vector;
    let mut flags = true;
    let mut iter = args.iter();
    while let Some(argument) = iter.next() {
        let argument = argument.to_string_lossy();
        if flags && argument == "--" {
            flags = false;
            continue;
        }
        if flags && matches!(argument.as_ref(), "--stage" | "--profile") {
            let value = iter
                .next()
                .ok_or_else(|| format!("missing value for {argument}"))?;
            set_option(&argument, &value.to_string_lossy(), &mut profile)?;
        } else {
            set_path(&argument, flags, &mut path)?;
        }
    }
    Ok((path.unwrap_or_else(|| "-".into()), profile))
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

fn set_option(flag: &str, value: &str, profile: &mut scene::Profile) -> Result<(), String> {
    let expected = if flag == "--stage" {
        "model"
    } else {
        "vector, cell"
    };
    match (flag, value) {
        ("--stage", "model") => {}
        ("--profile", "vector") => *profile = scene::Profile::Vector,
        ("--profile", "cell") => *profile = scene::Profile::Cell,
        _ => {
            return Err(format!(
                "invalid value {value} for {flag}; expected one of: {expected}"
            ));
        }
    }
    Ok(())
}

fn render(path: &str, profile: scene::Profile, bytes: &[u8]) -> (String, String, i32) {
    let (source, _) = elegant_mermaid::source::repair_utf8(bytes);
    let prep = syntax::preprocess::preprocess(&source);
    let detection = syntax::detect::detect(&source, &prep.removed);
    if detection
        .kind
        .is_some_and(|k| k != elegant_mermaid::DiagramKind::Flowchart)
    {
        return (
            String::new(),
            format!(
                "unsupported diagram kind: {}\n",
                detection.kind.map_or("", |k| k.id())
            ),
            2,
        );
    }
    let parsed = syntax::flowchart::parse(&source, &prep.removed);
    let (model, resolved) = elegant_mermaid::model::flowchart::resolve(&source, &parsed.document);
    let mut diagnostics = prep.diagnostics;
    diagnostics.extend(detection.diagnostics);
    diagnostics.extend(parsed.diagnostics);
    diagnostics.extend(resolved);
    diag::sort(&mut diagnostics);
    if diagnostics
        .iter()
        .any(|d| d.severity == diag::Severity::Error)
    {
        let mut stderr = String::new();
        diag::text::render_text(
            &mut stderr,
            path,
            &source,
            &diagnostics,
            &diag::text::TextFrameOptions {
                colour: false,
                width: |_| 1,
            },
        );
        return (String::new(), stderr, 1);
    }
    let input = layout::flowchart::from_flowchart(
        &parsed.document,
        &model,
        profile,
        scene::DumpOptions::default(),
    );
    (layout::modeldump::model_dump(&input), String::new(), 0)
}
