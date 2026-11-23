use crate::error::UsageError;
use std::io::IsTerminal;

#[derive(Default)]
pub struct Options {
    pub input: String,
    pub output: String,
    pub artefact_dir: Option<String>,
    pub format: String,
    pub theme: String,
    pub background: String,
    pub charset: String,
    pub color: String,
    pub svg_text: String,
    pub width: i32,
    pub scale: i32,
    pub config: String,
    pub icon_packs: Vec<String>,
}

pub fn invalid(value: &str, flag: &str, choices: &str) -> UsageError {
    UsageError::InvalidValue {
        value: value.to_owned(),
        flag: flag.to_owned(),
        choices: choices.to_owned(),
    }
}
pub fn choice(value: &str, flag: &str, choices: &[&str]) -> Result<(), UsageError> {
    if choices.contains(&value) {
        Ok(())
    } else {
        Err(invalid(value, flag, &choices.join(", ")))
    }
}
/// Whether an argument is a flag: it starts with `-` and is not a lone `-`.
pub fn is_flag(arg: &str) -> bool {
    arg.len() > 1 && arg.starts_with('-')
}

/// A flag argument split into its name and the text after its first `=`.
pub struct FlagArg<'a> {
    pub name: &'a str,
    pub inline: Option<&'a str>,
}

/// Splits a flag argument. One or two leading dashes name the same flag; an
/// argument with three or more leading dashes names no flag.
pub fn split_flag(arg: &str) -> Option<FlagArg<'_>> {
    let body = arg.strip_prefix("--").or_else(|| arg.strip_prefix('-'))?;
    if body.starts_with('-') {
        return None;
    }
    let (name, inline) = body
        .split_once('=')
        .map_or((body, None), |(name, value)| (name, Some(value)));
    Some(FlagArg { name, inline })
}

impl FlagArg<'_> {
    /// The value of the flag: the text after `=`, else the next argument.
    pub fn value(
        &self,
        arg: &str,
        next: impl FnOnce() -> Option<String>,
    ) -> Result<String, UsageError> {
        self.inline
            .map(str::to_owned)
            .or_else(next)
            .ok_or_else(|| UsageError::MissingValue {
                flag: arg.to_owned(),
            })
    }

    /// The value of a switch: `true` without `=`, else the boolean after it.
    pub fn switch(&self) -> Result<bool, UsageError> {
        let value = self.inline.unwrap_or("true");
        match value {
            "1" | "t" | "T" | "true" | "TRUE" | "True" => Ok(true),
            "0" | "f" | "F" | "false" | "FALSE" | "False" => Ok(false),
            _ => Err(invalid(value, &format!("--{}", self.name), "true, false")),
        }
    }
}
pub fn parse(command: &'static str, args: &[String]) -> Result<(Options, Vec<String>), UsageError> {
    let mut options = Options {
        charset: "unicode".into(),
        color: "auto".into(),
        scale: 2,
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
        if !is_flag(arg) {
            paths.push(arg.clone());
            continue;
        }
        let flag = split_flag(arg).filter(|flag| known(command, flag.name));
        let Some(flag) = flag else {
            return Err(UsageError::UnknownFlag {
                flag: arg.clone(),
                command,
            });
        };
        let value = flag.value(arg, || iter.next().cloned())?;
        set(&mut options, flag.name, &value)?;
    }
    Ok((options, paths))
}
fn known(command: &str, name: &str) -> bool {
    name == "color"
        || if command == "check" {
            name == "output-format"
        } else {
            [
                "i",
                "o",
                "a",
                "s",
                "e",
                "t",
                "b",
                "c",
                "charset",
                "svg-text",
                "width",
                "icon-pack",
            ]
            .contains(&name)
        }
}
fn set(o: &mut Options, name: &str, value: &str) -> Result<(), UsageError> {
    let target = match name {
        "i" => &mut o.input,
        "o" => &mut o.output,
        "a" => {
            o.artefact_dir = Some(value.to_owned());
            return Ok(());
        }
        "e" | "output-format" => &mut o.format,
        "t" => &mut o.theme,
        "b" => &mut o.background,
        "c" => &mut o.config,
        "charset" => &mut o.charset,
        "color" => &mut o.color,
        "svg-text" => &mut o.svg_text,
        "icon-pack" => {
            o.icon_packs.push(value.to_owned());
            return Ok(());
        }
        "s" => {
            o.scale = value
                .parse::<i32>()
                .ok()
                .filter(|v| (1..=8).contains(v))
                .ok_or_else(|| invalid(value, "-s", "1..8"))?;
            return Ok(());
        }
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
pub fn resolve(o: &mut Options, environment: &crate::view::Environment) -> Result<(), UsageError> {
    if o.format.is_empty() {
        o.format = infer(&o.output)?;
    }
    let b = o.background.strip_prefix('#').unwrap_or("");
    if !o.background.is_empty()
        && (!matches!(b.len(), 3 | 6) || !b.bytes().all(|v| v.is_ascii_hexdigit()))
    {
        return Err(invalid(&o.background, "-b", "#rgb, #rrggbb"));
    }
    choice(&o.format, "-e", &["svg", "png", "text"])?;
    choice(&o.charset, "--charset", &["unicode", "ascii"])?;
    choice(&o.color, "--color", &["auto", "always", "never"])?;
    choice(&o.svg_text, "--svg-text", &["font", "paths"])?;
    if o.theme.is_empty() {
        o.theme = if o.format == "text" && dark_background(&environment.colorfgbg) {
            "elegant-dark"
        } else {
            "elegant-light"
        }
        .into();
    }
    choice(&o.theme, "-t", &elegant_mermaid::theme::names())
}
fn infer(output: &str) -> Result<String, UsageError> {
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
        _ => Err(UsageError::UnknownFormat {
            output: output.to_owned(),
        }),
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

    fn args(values: &[&str]) -> Vec<String> {
        values.iter().map(|v| (*v).to_owned()).collect()
    }

    #[test]
    fn scale_flag_takes_one_to_eight() -> Result<(), crate::error::UsageError> {
        assert_eq!(super::parse("render", &args(&[]))?.0.scale, 2);
        for scale in 1..=8 {
            let text = scale.to_string();
            let (options, _) = super::parse("render", &args(&["-s", &text]))?;
            assert_eq!(options.scale, scale);
        }
        assert_eq!(super::parse("render", &args(&["-s=3"]))?.0.scale, 3);
        for bad in ["0", "9", "-1", "x", "", "2.5"] {
            let error = super::parse("render", &args(&["-s", bad]))
                .err()
                .map(|error| error.to_string());
            assert_eq!(
                error,
                Some(format!("invalid value {bad} for -s; expected one of: 1..8"))
            );
        }
        Ok(())
    }

    #[test]
    fn scale_is_a_render_flag_only() {
        let error = super::parse("check", &args(&["-s", "2"]))
            .err()
            .map(|error| error.to_string());
        assert_eq!(
            error.as_deref(),
            Some("unknown flag -s; run emd check --help")
        );
    }

    #[test]
    fn format_and_svg_text_values() {
        for (flag, value, accepted) in [
            ("-e", "png", true),
            ("-e", "svg", true),
            ("-e", "text", true),
            ("-e", "gif", false),
            ("--svg-text", "paths", true),
            ("--svg-text", "font", true),
            ("--svg-text", "glyphs", false),
        ] {
            let environment = crate::view::Environment {
                colorfgbg: String::new(),
                kitty_window_id: String::new(),
                term: String::new(),
                term_program: String::new(),
                auto_colour: false,
                depth: elegant_mermaid::cells::ColorMode::None,
            };
            let parsed = super::parse("render", &args(&[flag, value]));
            let resolved = parsed.and_then(|(mut options, _)| {
                super::resolve(&mut options, &environment).map(|()| options)
            });
            assert_eq!(resolved.is_ok(), accepted, "{flag} {value}");
        }
    }
}
