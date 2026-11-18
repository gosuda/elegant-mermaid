use crate::json::{self, Scanner};
use elegant_mermaid::LintConfig;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Op {
    Check,
    Lint,
    Fix,
    RenderSvg,
    RenderText,
    Layout,
    Version,
}

impl Op {
    pub fn parse(name: &str) -> Option<Op> {
        match name {
            "check" => Some(Op::Check),
            "lint" => Some(Op::Lint),
            "fix" => Some(Op::Fix),
            "render_svg" => Some(Op::RenderSvg),
            "render_text" => Some(Op::RenderText),
            "layout" => Some(Op::Layout),
            "version" => Some(Op::Version),
            _ => None,
        }
    }
}

#[derive(Clone, Copy)]
enum Key {
    Theme,
    Background,
    Charset,
    Profile,
    Stage,
    MaxWidth,
    Lint,
    Max,
}

impl Key {
    fn parse(name: &str) -> Option<Key> {
        match name {
            "theme" => Some(Key::Theme),
            "background" => Some(Key::Background),
            "charset" => Some(Key::Charset),
            "profile" => Some(Key::Profile),
            "stage" => Some(Key::Stage),
            "max_width" => Some(Key::MaxWidth),
            "lint" => Some(Key::Lint),
            "max" => Some(Key::Max),
            _ => None,
        }
    }

    fn read_by(self, op: Op) -> bool {
        let ops: &[Op] = match self {
            Key::Theme | Key::MaxWidth => &[Op::RenderSvg, Op::RenderText],
            Key::Background => &[Op::RenderSvg],
            Key::Charset => &[Op::RenderText],
            Key::Profile | Key::Stage => &[Op::Layout],
            Key::Lint => &[Op::Lint, Op::Fix],
            Key::Max => &[Op::Fix],
        };
        ops.contains(&op)
    }
}

pub struct Options {
    pub theme: String,
    pub background: String,
    pub ascii: bool,
    pub cell: bool,
    pub model: bool,
    pub unsafe_fixes: bool,
    pub width: u32,
    pub lint: LintConfig,
}

impl Default for Options {
    fn default() -> Options {
        Options {
            theme: "elegant-light".to_owned(),
            background: String::new(),
            ascii: false,
            cell: false,
            model: false,
            unsafe_fixes: false,
            width: 0,
            lint: LintConfig::default(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, thiserror::Error)]
pub enum OptionError {
    #[error("invalid option: options")]
    Malformed,
    #[error("invalid option: {0}")]
    Rejected(String),
}

pub fn parse(op: Op, text: &str) -> Result<Options, OptionError> {
    let mut options = Options::default();
    if text.trim().is_empty() {
        return Ok(options);
    }
    let mut scanner = Scanner::new(text);
    if !scanner.eat(b'{') {
        return Err(OptionError::Malformed);
    }
    if !scanner.eat(b'}') {
        loop {
            member(&mut scanner, op, &mut options)?;
            if !scanner.eat(b',') {
                break;
            }
        }
        if !scanner.eat(b'}') {
            return Err(OptionError::Malformed);
        }
    }
    if scanner.at_end() {
        Ok(options)
    } else {
        Err(OptionError::Malformed)
    }
}

fn member(scanner: &mut Scanner<'_>, op: Op, options: &mut Options) -> Result<(), OptionError> {
    let name = scanner.key().ok_or(OptionError::Malformed)?;
    let raw = scanner.value().ok_or(OptionError::Malformed)?;
    let Some(key) = Key::parse(&name) else {
        return Err(OptionError::Rejected(name));
    };
    if !key.read_by(op) || apply(key, raw, options) {
        Ok(())
    } else {
        Err(OptionError::Rejected(name))
    }
}

fn apply(key: Key, raw: &str, options: &mut Options) -> bool {
    match key {
        Key::Theme => store(&mut options.theme, json::string(raw)),
        Key::Background => store(&mut options.background, nullable(raw)),
        Key::Charset => store(&mut options.ascii, either(raw, "unicode", "ascii")),
        Key::Profile => store(&mut options.cell, either(raw, "vector", "cell")),
        Key::Stage => store(&mut options.model, either(raw, "layout", "model")),
        Key::MaxWidth => store(&mut options.width, width(raw)),
        Key::Lint => store(&mut options.lint, lint_config(raw)),
        Key::Max => store(&mut options.unsafe_fixes, either(raw, "safe", "unsafe")),
    }
}

fn store<T>(slot: &mut T, value: Option<T>) -> bool {
    value.map(|value| *slot = value).is_some()
}

fn nullable(raw: &str) -> Option<String> {
    (raw == "null")
        .then(String::new)
        .or_else(|| json::string(raw))
}

fn either(raw: &str, first: &str, second: &str) -> Option<bool> {
    let word = json::string(raw)?;
    [first, second]
        .iter()
        .position(|choice| *choice == word)
        .map(|position| position == 1)
}

fn width(raw: &str) -> Option<u32> {
    if raw == "null" {
        return Some(0);
    }
    raw.parse::<i32>().ok().and_then(|n| u32::try_from(n).ok())
}

/// Reads the `lint` option as the `lint` object of an `emd.json`, so unknown
/// keys and unknown rule codes are rejected as the CLI rejects them.
fn lint_config(raw: &str) -> Option<LintConfig> {
    let document = format!("{{\"lint\":{raw}}}");
    elegant_mermaid::lint::parse_config("emd.json", &document).ok()
}
