//! Replaces a file in place: write a sibling temporary file with the original
//! permissions, then rename it over the target.

use crate::error::CliError;
use crate::input;
use std::path::Path;

pub fn rewrite_file(path: &str, data: &[u8]) -> Result<(), CliError> {
    let metadata = std::fs::metadata(path).map_err(|e| input::read_error(path, e))?;
    crate::output::write_file(Path::new(path), data, Some(permissions(&metadata))).map_err(
        |source| CliError::Write {
            path: path.to_owned(),
            source,
        },
    )
}

#[cfg(unix)]
fn permissions(metadata: &std::fs::Metadata) -> std::fs::Permissions {
    use std::os::unix::fs::PermissionsExt;
    std::fs::Permissions::from_mode(metadata.permissions().mode() & 0o777)
}

#[cfg(not(unix))]
fn permissions(metadata: &std::fs::Metadata) -> std::fs::Permissions {
    metadata.permissions()
}
