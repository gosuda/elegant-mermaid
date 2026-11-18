use crate::error::InputError;
use std::io::{IsTerminal, Read};

pub const STDIN_LABEL: &str = "<stdin>";

pub fn read(path: &str) -> Result<Vec<u8>, InputError> {
    if path != "-" {
        return std::fs::read(path).map_err(|error| read_error(path, error));
    }
    if std::io::stdin().is_terminal() {
        return Err(InputError::Missing);
    }
    let mut bytes = Vec::new();
    std::io::stdin()
        .read_to_end(&mut bytes)
        .map_err(|error| read_error(STDIN_LABEL, error))?;
    Ok(bytes)
}

pub fn read_error(path: &str, source: std::io::Error) -> InputError {
    InputError::Read {
        path: path.to_owned(),
        source,
    }
}

pub fn label(path: &str) -> &str {
    if path == "-" { STDIN_LABEL } else { path }
}
