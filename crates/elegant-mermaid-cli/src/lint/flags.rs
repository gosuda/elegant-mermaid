use crate::error::{CliError, UsageError};
use crate::options;
use elegant_mermaid::lint;

const FORMATS: [&str; 4] = ["text", "json", "sarif", "github"];

#[derive(Default)]
pub struct Flags {
    pub fix: bool,
    pub unsafe_fixes: bool,
    pub deny_warnings: bool,
    pub no_config: bool,
    pub select: Vec<String>,
    pub ignore: Vec<String>,
    pub format: String,
    pub color: String,
    pub config_file: String,
}

enum Spec {
    Switch(fn(&mut Flags, bool)),
    Value(fn(&mut Flags, String)),
}

fn spec(name: &str) -> Option<Spec> {
    Some(match name {
        "fix" => Spec::Switch(|f, v| f.fix = v),
        "unsafe-fixes" => Spec::Switch(|f, v| f.unsafe_fixes = v),
        "deny-warnings" => Spec::Switch(|f, v| f.deny_warnings = v),
        "no-config" => Spec::Switch(|f, v| f.no_config = v),
        "output-format" => Spec::Value(|f, v| f.format = v),
        "lint-config" => Spec::Value(|f, v| f.config_file = v),
        "color" => Spec::Value(|f, v| f.color = v),
        "select" => Spec::Value(|f, v| f.select.push(v)),
        "ignore" => Spec::Value(|f, v| f.ignore.push(v)),
        _ => return None,
    })
}

/// Flags may come before or after positionals, `--` ends flags, and a lone `-`
/// is a positional (stdin).
pub fn parse(args: &[String]) -> Result<(Flags, Vec<String>), UsageError> {
    let mut flags = Flags {
        format: "text".into(),
        color: "auto".into(),
        ..Flags::default()
    };
    let mut paths = Vec::new();
    let mut rest = args.iter();
    while let Some(arg) = rest.next() {
        if arg == "--" {
            paths.extend(rest.cloned());
            break;
        }
        if options::is_flag(arg) {
            apply(&mut flags, arg, &mut rest)?;
        } else {
            paths.push(arg.clone());
        }
    }
    Ok((flags, paths))
}

fn apply<'a>(
    flags: &mut Flags,
    arg: &str,
    rest: &mut impl Iterator<Item = &'a String>,
) -> Result<(), UsageError> {
    let unknown = || UsageError::UnknownFlag {
        flag: arg.to_owned(),
        command: "lint",
    };
    let flag = options::split_flag(arg).ok_or_else(unknown)?;
    let spec = spec(flag.name).ok_or_else(unknown)?;
    match spec {
        Spec::Switch(set) => set(flags, flag.switch()?),
        Spec::Value(set) => set(flags, flag.value(arg, || rest.next().cloned())?),
    }
    Ok(())
}

/// Splits comma-separated code lists, trimming blanks and dropping empties.
pub fn code_list(values: &[String]) -> Vec<String> {
    values
        .iter()
        .flat_map(|value| value.split(','))
        .map(str::trim)
        .filter(|code| !code.is_empty())
        .map(str::to_owned)
        .collect()
}

pub fn validate(flags: &Flags, paths: &[String]) -> Result<(), CliError> {
    options::choice(&flags.format, "--output-format", &FORMATS)?;
    options::choice(&flags.color, "--color", &["auto", "always", "never"])?;
    if flags.unsafe_fixes && !flags.fix {
        return Err(UsageError::UnsafeFixesNeedFix.into());
    }
    if flags.fix && flags.format != "text" && paths.iter().any(|path| path == "-") {
        return Err(UsageError::FixStdinFormat.into());
    }
    lint::validate_codes(&code_list(&flags.select))?;
    lint::validate_codes(&code_list(&flags.ignore))?;
    Ok(())
}
