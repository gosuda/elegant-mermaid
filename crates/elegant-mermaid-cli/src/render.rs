use crate::{diagnostics, input, options};
use elegant_mermaid::{cells, layout, scene, svg};

pub fn run(args: &[String]) -> (String, String, i32) {
    match prepare(args) {
        Ok(result) => result,
        Err(error) => (String::new(), format!("{error}\n"), 2),
    }
}
fn prepare(args: &[String]) -> Result<(String, String, i32), String> {
    let (mut o, paths) = options::parse("render", args)?;
    if paths.len() > 1 {
        return Err("render accepts one INPUT".into());
    }
    if !paths.is_empty() && !o.input.is_empty() {
        return Err("pass input either as INPUT or with -i, not both".into());
    }
    options::resolve(&mut o)?;
    let path = paths
        .first()
        .map(String::as_str)
        .unwrap_or(if o.input.is_empty() { "-" } else { &o.input });
    let bytes = input::read(path)?;
    let parsed = diagnostics::parse(&bytes)?;
    let path = input::label(path);
    let mut stderr = diagnostics::text(
        path,
        &parsed.source,
        &parsed.diagnostics,
        options::colour(&o.color),
    );
    if diagnostics::has_errors(&parsed.diagnostics) {
        return Ok((String::new(), stderr, 1));
    }
    let profile = if o.format == "text" {
        scene::Profile::Cell
    } else {
        scene::Profile::Vector
    };
    let opts = scene::DumpOptions {
        max_width: o.width.unsigned_abs(),
        ..scene::DumpOptions::default()
    };
    let in_model = layout::flowchart::from_flowchart(&parsed.model, profile, opts);
    let (scene, ds) = match layout::families::layout(&in_model) {
        Ok(value) => value,
        Err(error) => {
            stderr.push_str(&format!("{error}\n"));
            return Ok((String::new(), stderr, 1));
        }
    };
    stderr.push_str(&diagnostics::text(path, &parsed.source, &ds, false));
    let output = match serialize(&scene, &o) {
        Ok(value) => value,
        Err(error) => {
            stderr.push_str(&format!("{error}\n"));
            return Ok((String::new(), stderr, 1));
        }
    };
    if o.output.is_empty() {
        return Ok((output, stderr, 0));
    }
    atomic_output(&o.output, output.as_bytes()).map_err(|e| e.to_string())?;
    Ok((String::new(), stderr, 0))
}
fn serialize(scene: &scene::Scene, o: &options::Options) -> Result<String, String> {
    if o.format == "svg" {
        let mut output = String::new();
        svg::write(
            &mut output,
            scene,
            &svg::Options {
                theme: &o.theme,
                background: &o.background,
                kind: "flowchart",
                ..svg::Options::default()
            },
        )
        .map_err(|e| e.to_string())?;
        return Ok(output);
    }
    let charset = if o.charset == "ascii" {
        cells::Charset::Ascii
    } else {
        cells::Charset::Unicode
    };
    cells::render(
        scene,
        &cells::render::Options {
            charset,
            color: options::depth(&o.color),
            theme: o.theme.clone(),
        },
    )
    .map(|r| r.text)
    .map_err(|e| e.to_string())
}
fn atomic_output(path: &str, data: &[u8]) -> std::io::Result<()> {
    use std::io::Write;
    let parent = std::path::Path::new(path)
        .parent()
        .unwrap_or_else(|| std::path::Path::new("."));
    let temp = parent.join(format!(".emd-{}", std::process::id()));
    let result = (|| {
        let mut file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&temp)?;
        file.write_all(data)?;
        drop(file);
        std::fs::rename(&temp, path)
    })();
    let cleanup = std::fs::remove_file(&temp);
    if let Err(error) = cleanup
        && error.kind() != std::io::ErrorKind::NotFound
    {
        return Err(error);
    }
    result
}
