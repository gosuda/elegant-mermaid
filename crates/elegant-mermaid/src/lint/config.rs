use crate::diag::Severity;
use crate::options::LintConfig;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

const MAX_DEPTH: usize = 1_000;

#[derive(Debug, thiserror::Error)]
pub enum ConfigError {
    #[error("invalid emd.json {path}: {message}")]
    Invalid { path: String, message: String },
    #[error("unknown diagnostic code: {code}; use a code printed by emd check or emd lint")]
    UnknownCode { code: String },
}

/// Walks up from `start` to the first `emd.json`, or past the root.
pub fn find_config(start: &Path) -> Option<PathBuf> {
    let mut dir = Some(start);
    while let Some(step) = dir {
        let candidate = step.join("emd.json");
        if candidate.is_file() {
            return Some(candidate);
        }
        dir = step.parent();
    }
    None
}

pub fn load_config(path: &Path) -> Result<LintConfig, ConfigError> {
    let shown = path.display().to_string();
    let text = std::fs::read_to_string(path).map_err(|error| ConfigError::Invalid {
        path: shown.clone(),
        message: error.to_string(),
    })?;
    parse_config(&shown, &text)
}

pub fn parse_config(path: &str, text: &str) -> Result<LintConfig, ConfigError> {
    let json = parse_json(text).map_err(|()| invalid(path, "not valid JSON"))?;
    let Json::Object(entries) = json else {
        return Err(invalid(path, "top level must be a JSON object"));
    };
    let root = fields(&entries);
    check_keys(&root, "", &["lint", "mermaid"], path)?;
    if root
        .get("mermaid")
        .is_some_and(|value| !matches!(value, Json::Object(_)))
    {
        return Err(invalid(path, "mermaid must be a JSON object"));
    }
    let config = match root.get("lint") {
        Some(value) => read_lint(value, path)?,
        None => LintConfig::default(),
    };
    validate_codes(&config)?;
    Ok(config)
}

fn invalid(path: &str, message: &str) -> ConfigError {
    ConfigError::Invalid {
        path: path.to_owned(),
        message: message.to_owned(),
    }
}

/// An object's members by name, in byte order, a later duplicate replacing an
/// earlier one.
fn fields(entries: &[(String, Json)]) -> BTreeMap<&str, &Json> {
    entries
        .iter()
        .map(|(key, value)| (key.as_str(), value))
        .collect()
}

fn check_keys(
    fields: &BTreeMap<&str, &Json>,
    prefix: &str,
    allowed: &[&str],
    path: &str,
) -> Result<(), ConfigError> {
    match fields.keys().find(|key| !allowed.contains(key)) {
        Some(key) => Err(invalid(path, &format!("unknown key \"{prefix}{key}\""))),
        None => Ok(()),
    }
}

fn read_lint(value: &Json, path: &str) -> Result<LintConfig, ConfigError> {
    let Json::Object(entries) = value else {
        return Err(invalid(path, "lint must be a JSON object"));
    };
    let members = fields(entries);
    check_keys(&members, "lint.", &["select", "ignore", "severity"], path)?;
    let mut config = LintConfig {
        select: code_list(members.get("select").copied(), path, "lint.select")?,
        ignore: code_list(members.get("ignore").copied(), path, "lint.ignore")?,
        ..LintConfig::default()
    };
    if let Some(severity) = members.get("severity") {
        read_severities(severity, &mut config, path)?;
    }
    Ok(config)
}

/// An absent or `null` list is empty and a `null` element is the empty code.
fn code_list(value: Option<&Json>, path: &str, key: &str) -> Result<Vec<String>, ConfigError> {
    let items = match value {
        None | Some(Json::Null) => return Ok(Vec::new()),
        Some(Json::Array(items)) => items,
        Some(_) => return Err(invalid(path, &format!("{key} must be an array of strings"))),
    };
    items
        .iter()
        .map(|item| match item {
            Json::String(code) => Ok(code.clone()),
            Json::Null => Ok(String::new()),
            _ => Err(invalid(path, &format!("{key} must be an array of strings"))),
        })
        .collect()
}

fn read_severities(value: &Json, config: &mut LintConfig, path: &str) -> Result<(), ConfigError> {
    let not_an_object = || invalid(path, "lint.severity must be a JSON object");
    let Json::Object(entries) = value else {
        return Err(not_an_object());
    };
    let mut words: BTreeMap<&str, &str> = BTreeMap::new();
    for (code, word) in fields(entries) {
        match word {
            Json::String(word) => words.insert(code, word),
            Json::Null => words.insert(code, ""),
            _ => return Err(not_an_object()),
        };
    }
    for (code, word) in words {
        let severity = match word {
            "error" => Severity::Error,
            "warning" => Severity::Warning,
            "info" => Severity::Info,
            "off" => {
                config.off.push(code.to_owned());
                continue;
            }
            _ => {
                return Err(invalid(
                    path,
                    &format!("lint.severity \"{code}\" must be error, warning, info, or off"),
                ));
            }
        };
        config.severity.insert(code.to_owned(), severity);
    }
    Ok(())
}

fn validate_codes(config: &LintConfig) -> Result<(), ConfigError> {
    for code in config
        .select
        .iter()
        .chain(config.ignore.iter())
        .chain(config.off.iter())
        .chain(config.severity.keys())
    {
        if super::describe::canonical_code(code).is_none() {
            return Err(ConfigError::UnknownCode { code: code.clone() });
        }
    }
    Ok(())
}

enum Json {
    Object(Vec<(String, Json)>),
    Array(Vec<Json>),
    String(String),
    Null,
    Other,
}

fn parse_json(text: &str) -> Result<Json, ()> {
    let bytes = text.as_bytes();
    let mut at = skip_ws(bytes, 0);
    let value = parse_value(bytes, &mut at, 1)?;
    at = skip_ws(bytes, at);
    if at != bytes.len() {
        return Err(());
    }
    Ok(value)
}

fn parse_value(bytes: &[u8], at: &mut usize, depth: usize) -> Result<Json, ()> {
    if depth > MAX_DEPTH {
        return Err(());
    }
    *at = skip_ws(bytes, *at);
    match bytes.get(*at) {
        Some(b'{') => parse_object(bytes, at, depth),
        Some(b'[') => parse_array(bytes, at, depth),
        Some(b'"') => Ok(Json::String(parse_string(bytes, at)?)),
        Some(_) => parse_scalar(bytes, at),
        None => Err(()),
    }
}

fn parse_object(bytes: &[u8], at: &mut usize, depth: usize) -> Result<Json, ()> {
    *at += 1;
    let mut entries = Vec::new();
    *at = skip_ws(bytes, *at);
    if bytes.get(*at) == Some(&b'}') {
        *at += 1;
        return Ok(Json::Object(entries));
    }
    loop {
        *at = skip_ws(bytes, *at);
        if bytes.get(*at) != Some(&b'"') {
            return Err(());
        }
        let key = parse_string(bytes, at)?;
        *at = skip_ws(bytes, *at);
        if bytes.get(*at) != Some(&b':') {
            return Err(());
        }
        *at += 1;
        let value = parse_value(bytes, at, depth + 1)?;
        entries.push((key, value));
        *at = skip_ws(bytes, *at);
        match bytes.get(*at) {
            Some(b',') => {
                *at += 1;
                Ok(())
            }
            Some(b'}') => {
                *at += 1;
                return Ok(Json::Object(entries));
            }
            _ => Err(()),
        }?;
    }
}

fn parse_array(bytes: &[u8], at: &mut usize, depth: usize) -> Result<Json, ()> {
    *at += 1;
    let mut items = Vec::new();
    *at = skip_ws(bytes, *at);
    if bytes.get(*at) == Some(&b']') {
        *at += 1;
        return Ok(Json::Array(items));
    }
    loop {
        let value = parse_value(bytes, at, depth + 1)?;
        items.push(value);
        *at = skip_ws(bytes, *at);
        match bytes.get(*at) {
            Some(b',') => {
                *at += 1;
                Ok(())
            }
            Some(b']') => {
                *at += 1;
                return Ok(Json::Array(items));
            }
            _ => Err(()),
        }?;
    }
}

fn parse_string(bytes: &[u8], at: &mut usize) -> Result<String, ()> {
    *at += 1;
    let mut out = String::new();
    while let Some(&byte) = bytes.get(*at) {
        match byte {
            b'"' => {
                *at += 1;
                return Ok(out);
            }
            b'\\' => push_escape(bytes, at, &mut out)?,
            0..=0x1f => return Err(()),
            _ => {
                let mut end = *at + 1;
                while matches!(bytes.get(end), Some(&b) if b & 0xc0 == 0x80) {
                    end += 1;
                }
                let chunk = std::str::from_utf8(&bytes[*at..end]).map_err(|_| ())?;
                out.push_str(chunk);
                *at = end;
            }
        }
    }
    Err(())
}

fn push_escape(bytes: &[u8], at: &mut usize, out: &mut String) -> Result<(), ()> {
    let escape = *bytes.get(*at + 1).ok_or(())?;
    *at += 2;
    match escape {
        b'"' => out.push('"'),
        b'\\' => out.push('\\'),
        b'/' => out.push('/'),
        b'b' => out.push('\u{8}'),
        b'f' => out.push('\u{c}'),
        b'n' => out.push('\n'),
        b'r' => out.push('\r'),
        b't' => out.push('\t'),
        b'u' => push_unicode(bytes, at, out)?,
        _ => return Err(()),
    }
    Ok(())
}

fn hex4(bytes: &[u8], at: usize) -> Result<u32, ()> {
    let digits = bytes.get(at..at + 4).ok_or(())?;
    digits.iter().try_fold(0, |code, &digit| {
        Ok(code * 16 + (digit as char).to_digit(16).ok_or(())?)
    })
}

/// A `\uXXXX` escape, joined with a directly following low surrogate escape
/// into one scalar. A lone surrogate becomes U+FFFD.
fn push_unicode(bytes: &[u8], at: &mut usize, out: &mut String) -> Result<(), ()> {
    let first = hex4(bytes, *at)?;
    *at += 4;
    if (0xD800..0xDC00).contains(&first)
        && bytes.get(*at..*at + 2) == Some(b"\\u")
        && let Ok(second) = hex4(bytes, *at + 2)
        && (0xDC00..0xE000).contains(&second)
    {
        *at += 6;
        let code = 0x1_0000 + ((first - 0xD800) << 10) + (second - 0xDC00);
        out.push(char::from_u32(code).unwrap_or('\u{fffd}'));
        return Ok(());
    }
    out.push(char::from_u32(first).unwrap_or('\u{fffd}'));
    Ok(())
}

fn parse_scalar(bytes: &[u8], at: &mut usize) -> Result<Json, ()> {
    match bytes.get(*at) {
        Some(b't') => literal(bytes, at, b"true").map(|()| Json::Other),
        Some(b'f') => literal(bytes, at, b"false").map(|()| Json::Other),
        Some(b'n') => literal(bytes, at, b"null").map(|()| Json::Null),
        Some(b'-' | b'0'..=b'9') => number(bytes, at).map(|()| Json::Other),
        _ => Err(()),
    }
}

fn literal(bytes: &[u8], at: &mut usize, word: &[u8]) -> Result<(), ()> {
    if bytes.get(*at..).is_some_and(|rest| rest.starts_with(word)) {
        *at += word.len();
        Ok(())
    } else {
        Err(())
    }
}

/// RFC 8259: `-? (0 | [1-9][0-9]*) (. [0-9]+)? ([eE] [+-]? [0-9]+)?`.
fn number(bytes: &[u8], at: &mut usize) -> Result<(), ()> {
    if bytes.get(*at) == Some(&b'-') {
        *at += 1;
    }
    match bytes.get(*at) {
        Some(b'0') => *at += 1,
        Some(b'1'..=b'9') => digits(bytes, at)?,
        _ => return Err(()),
    }
    if bytes.get(*at) == Some(&b'.') {
        *at += 1;
        digits(bytes, at)?;
    }
    if matches!(bytes.get(*at), Some(b'e' | b'E')) {
        *at += 1;
        if matches!(bytes.get(*at), Some(b'+' | b'-')) {
            *at += 1;
        }
        digits(bytes, at)?;
    }
    Ok(())
}

fn digits(bytes: &[u8], at: &mut usize) -> Result<(), ()> {
    if !bytes.get(*at).is_some_and(u8::is_ascii_digit) {
        return Err(());
    }
    while bytes.get(*at).is_some_and(u8::is_ascii_digit) {
        *at += 1;
    }
    Ok(())
}

fn skip_ws(bytes: &[u8], mut at: usize) -> usize {
    while matches!(bytes.get(at), Some(&b' ' | &b'\t' | &b'\n' | &b'\r')) {
        at += 1;
    }
    at
}
