use std::io::IsTerminal;

#[derive(Default)]
pub struct Options {
    pub input: String,
    pub output: String,
    pub format: String,
    pub theme: String,
    pub background: String,
    pub charset: String,
    pub color: String,
    pub svg_text: String,
    pub width: i32,
}

pub fn invalid(value: &str, flag: &str, choices: &str) -> String {
    format!("invalid value {value} for {flag}; expected one of: {choices}")
}
pub fn choice(value: &str, flag: &str, choices: &[&str]) -> Result<(), String> {
    if choices.contains(&value) {
        Ok(())
    } else {
        Err(invalid(value, flag, &choices.join(", ")))
    }
}
pub fn parse(command: &str, args: &[String]) -> Result<(Options, Vec<String>), String> {
    let mut options = Options {
        charset: "unicode".into(),
        color: "auto".into(),
        svg_text: "font".into(),
        ..Options::default()
    };
    if command == "check" {
        options.format = "text".into();
    }
    let mut paths = Vec::new();
    let mut iter = args.iter();
    while let Some(arg) = iter.next() {
        if arg == "--" {
            paths.extend(iter.cloned());
            break;
        }
        if arg == "-" || !arg.starts_with('-') {
            paths.push(arg.clone());
            continue;
        }
        let (flag, inline) = arg
            .split_once('=')
            .map_or((arg.as_str(), None), |(a, b)| (a, Some(b)));
        let name = flag.trim_start_matches('-');
        if !known(command, name) {
            return Err(format!("unknown flag {arg}; run emd {command} --help"));
        }
        let value = inline
            .or_else(|| iter.next().map(String::as_str))
            .ok_or_else(|| format!("missing value for {arg}"))?;
        set(&mut options, name, value)?;
    }
    Ok((options, paths))
}
fn known(command: &str, name: &str) -> bool {
    name == "color"
        || if command == "check" {
            name == "output-format"
        } else {
            ["i", "o", "e", "t", "b", "charset", "svg-text", "width"].contains(&name)
        }
}
fn set(o: &mut Options, name: &str, value: &str) -> Result<(), String> {
    let target = match name {
        "i" => &mut o.input,
        "o" => &mut o.output,
        "e" | "output-format" => &mut o.format,
        "t" => &mut o.theme,
        "b" => &mut o.background,
        "charset" => &mut o.charset,
        "color" => &mut o.color,
        "svg-text" => &mut o.svg_text,
        _ => {
            o.width = value
                .parse::<i32>()
                .ok()
                .filter(|v| *v >= 0)
                .ok_or_else(|| invalid(value, "--width", "non-negative integers"))?;
            return Ok(());
        }
    };
    value.clone_into(target);
    Ok(())
}
pub fn resolve(o: &mut Options, environment: &crate::view::Environment) -> Result<(), String> {
    if o.format.is_empty() {
        o.format = infer(&o.output)?;
    }
    let b = o.background.strip_prefix('#').unwrap_or("");
    if !o.background.is_empty()
        && (!matches!(b.len(), 3 | 6) || !b.bytes().all(|v| v.is_ascii_hexdigit()))
    {
        return Err(invalid(&o.background, "-b", "#rgb, #rrggbb"));
    }
    choice(&o.format, "-e", &["svg", "text"])?;
    choice(&o.charset, "--charset", &["unicode", "ascii"])?;
    choice(&o.color, "--color", &["auto", "always", "never"])?;
    choice(&o.svg_text, "--svg-text", &["font"])?;
    if o.theme.is_empty() {
        o.theme = if o.format == "text" && dark_background(&environment.colorfgbg) {
            "elegant-dark"
        } else {
            "elegant-light"
        }
        .into();
    }
    choice(&o.theme, "-t", &["elegant-light", "elegant-dark"])
}
fn infer(output: &str) -> Result<String, String> {
    if output.is_empty() {
        return Ok(if std::io::stdout().is_terminal() {
            "text"
        } else {
            "svg"
        }
        .into());
    }
    match std::path::Path::new(output)
        .extension()
        .and_then(|s| s.to_str())
    {
        Some("svg") => Ok("svg".into()),
        Some("txt") => Ok("text".into()),
        Some("png") => Ok("png".into()),
        _ => Err(format!(
            "cannot infer the output format from {output}; pass -e"
        )),
    }
}
fn dark_background(value: &str) -> bool {
    let parts: Vec<_> = value.split(';').collect();
    parts.len() >= 2
        && parts.iter().all(|p| p.parse::<u8>().is_ok())
        && parts
            .last()
            .and_then(|p| p.parse::<u8>().ok())
            .is_some_and(|n| n <= 6 || n == 8)
}
pub fn colour_enabled(mode: &str, terminal: bool, getenv: impl Fn(&str) -> String) -> bool {
    if mode != "auto" {
        return mode == "always";
    }
    if !getenv("NO_COLOR").is_empty() {
        return false;
    }
    let force = getenv("FORCE_COLOR");
    if getenv("CLICOLOR_FORCE") == "1" || (!force.is_empty() && force != "0") {
        return true;
    }
    if getenv("CLICOLOR") == "0" || getenv("TERM") == "dumb" {
        return false;
    }
    terminal
}
pub fn colour(mode: &str, environment: &crate::view::Environment) -> bool {
    if mode == "auto" {
        environment.auto_colour
    } else {
        mode == "always"
    }
}
pub fn depth(
    mode: &str,
    environment: &crate::view::Environment,
) -> elegant_mermaid::cells::ColorMode {
    if colour(mode, environment) {
        environment.depth
    } else {
        elegant_mermaid::cells::ColorMode::None
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn colour_precedence() {
        let cases = [
            ("always", false, vec![("NO_COLOR", "1")], true),
            ("never", true, vec![], false),
            (
                "auto",
                true,
                vec![("NO_COLOR", "1"), ("CLICOLOR_FORCE", "1")],
                false,
            ),
            (
                "auto",
                false,
                vec![("CLICOLOR_FORCE", "1"), ("TERM", "dumb")],
                true,
            ),
            ("auto", true, vec![("TERM", "dumb")], false),
            ("auto", true, vec![], true),
        ];
        for (mode, terminal, env, expected) in cases {
            assert_eq!(
                super::colour_enabled(mode, terminal, |key| env
                    .iter()
                    .find(|(name, _)| *name == key)
                    .map_or(String::new(), |(_, value)| (*value).into())),
                expected
            );
        }
    }
}
