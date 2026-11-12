use std::io::{IsTerminal, Read};

pub fn read(path: &str) -> Result<Vec<u8>, String> {
    if path != "-" {
        return std::fs::read(path).map_err(|error| read_error(path, &error, "open"));
    }
    if std::io::stdin().is_terminal() {
        return Err("missing INPUT; pass a path or pipe Mermaid source".into());
    }
    let mut bytes = Vec::new();
    std::io::stdin()
        .read_to_end(&mut bytes)
        .map_err(|error| read_error(path, &error, "read"))?;
    Ok(bytes)
}

pub fn read_error(path: &str, error: &std::io::Error, operation: &str) -> String {
    let text = match error.raw_os_error() {
        Some(2) => "no such file or directory".into(),
        Some(13) => "permission denied".into(),
        Some(21) => "is a directory".into(),
        _ => error.to_string(),
    };
    let operation = if error.raw_os_error() == Some(21) {
        "read"
    } else {
        operation
    };
    format!("cannot read {path}: {operation} {path}: {text}")
}

pub fn label(path: &str) -> &str {
    if path == "-" { "<stdin>" } else { path }
}
