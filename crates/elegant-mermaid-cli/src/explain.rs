use crate::error::{CliError, UsageError};
use crate::options;
use elegant_mermaid::{
    DiagramKind, diag::json::push_json_string, lint, lint::ConfigError, lint::Described,
};

const SUPPRESSION: &str = "%% emd-disable-next-line CODE: reason";

pub fn run(args: &[String]) -> (String, String, i32) {
    match explain(args) {
        Ok(stdout) => (stdout, String::new(), 0),
        Err(error) => (String::new(), format!("{error}\n"), 2),
    }
}

fn explain(args: &[String]) -> Result<String, CliError> {
    let (format, operands) = parse(args)?;
    options::choice(&format, "--output-format", &["text", "json"])?;
    let code = match operands.as_slice() {
        [] => return Err(UsageError::MissingCode.into()),
        [code] => code,
        [_, extra, ..] => {
            return Err(UsageError::ExtraCode {
                extra: extra.clone(),
            }
            .into());
        }
    };
    let row =
        lint::describe(code).ok_or_else(|| ConfigError::UnknownCode { code: code.clone() })?;
    let fields = fields(&row);
    Ok(if format == "json" {
        json(&fields)
    } else {
        text(&fields)
    })
}

fn parse(args: &[String]) -> Result<(String, Vec<String>), UsageError> {
    let mut format = String::from("text");
    let mut operands = Vec::new();
    let mut rest = args.iter();
    while let Some(arg) = rest.next() {
        if arg == "--" {
            operands.extend(rest.cloned());
            break;
        }
        if !options::is_flag(arg) {
            operands.push(arg.clone());
            continue;
        }
        let flag = options::split_flag(arg).filter(|flag| flag.name == "output-format");
        let Some(flag) = flag else {
            return Err(UsageError::UnknownFlag {
                flag: arg.clone(),
                command: "explain",
            });
        };
        format = flag.value(arg, || rest.next().cloned())?;
    }
    Ok((format, operands))
}

fn fields(row: &Described) -> Vec<(&'static str, String)> {
    vec![
        ("code", row.code.to_owned()),
        ("kind", kind(row.code).to_owned()),
        ("severity", row.severity.to_owned()),
        ("fix_safety", row.fix_safety.to_owned()),
        ("summary", row.summary.to_owned()),
        ("help", row.help.to_owned()),
        ("rationale", row.rationale.to_owned()),
        ("suppression", SUPPRESSION.replacen("CODE", row.code, 1)),
    ]
}

/// The kind id of a code's prefix, or `common` when the prefix is not a kind.
fn kind(code: &str) -> &str {
    let prefix = code.split_once('/').map_or(code, |(prefix, _)| prefix);
    DiagramKind::from_id(prefix).map_or("common", |kind| kind.id())
}

fn text(fields: &[(&str, String)]) -> String {
    let mut out = String::new();
    for (key, value) in fields {
        out.push_str(key);
        out.push_str(": ");
        out.push_str(value);
        out.push('\n');
    }
    out
}

fn json(fields: &[(&str, String)]) -> String {
    let mut out = String::from("{");
    for (at, (key, value)) in fields.iter().enumerate() {
        if at > 0 {
            out.push(',');
        }
        push_json_string(&mut out, key);
        out.push(':');
        push_json_string(&mut out, value);
    }
    out.push_str("}\n");
    out
}
