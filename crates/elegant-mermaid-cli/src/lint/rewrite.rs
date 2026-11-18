//! Replaces a file in place: write a sibling temporary file with the original
//! permissions, then rename it over the target.

use crate::error::CliError;
use crate::input;
use std::io::Write;
use std::path::{Path, PathBuf};

pub fn rewrite_file(path: &str, data: &[u8]) -> Result<(), CliError> {
    let metadata = std::fs::metadata(path).map_err(|e| input::read_error(path, e))?;
    replace(path, data, &metadata).map_err(|source| CliError::Write {
        path: path.to_owned(),
        source,
    })
}

fn replace(path: &str, data: &[u8], metadata: &std::fs::Metadata) -> std::io::Result<()> {
    let target = Path::new(path);
    let dir = target
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let (temp, mut file) = create_temp(dir)?;
    let written = file
        .write_all(data)
        .and_then(|()| file.set_permissions(permissions(metadata)))
        .and_then(|()| file.sync_all())
        .and_then(|()| {
            drop(file);
            std::fs::rename(&temp, target)
        });
    written.inspect_err(|_| {
        let _ = std::fs::remove_file(&temp);
    })
}

fn create_temp(dir: &Path) -> std::io::Result<(PathBuf, std::fs::File)> {
    for attempt in 0..64u32 {
        let temp = dir.join(format!(".emd-{}-{attempt}", std::process::id()));
        let opened = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&temp);
        match opened {
            Ok(file) => return Ok((temp, file)),
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {}
            Err(e) => return Err(e),
        }
    }
    Err(std::io::Error::from(std::io::ErrorKind::AlreadyExists))
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
