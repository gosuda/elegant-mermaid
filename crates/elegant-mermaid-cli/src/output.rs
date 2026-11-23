//! Atomically replace a destination through an exclusively owned sibling file.

use std::fs::{File, Permissions};
use std::io::{self, Write};
use std::path::{Path, PathBuf};

pub fn write_file(path: &Path, data: &[u8], permissions: Option<Permissions>) -> io::Result<()> {
    let (temp, mut file) = create_temp(path)?;
    let result = (|| {
        file.write_all(data)?;
        if let Some(permissions) = permissions {
            file.set_permissions(permissions)?;
        }
        file.sync_all()?;
        drop(file);
        std::fs::rename(&temp, path)
    })();
    if result.is_err() {
        let _ = std::fs::remove_file(&temp);
    }
    result
}

fn create_temp(target: &Path) -> io::Result<(PathBuf, File)> {
    let dir = target
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let target_name = target.file_name().and_then(|name| name.to_str());
    for attempt in 0..64u32 {
        let name = format!(".emd-{}-{attempt}", std::process::id());
        if target_name.is_some_and(|target| target.eq_ignore_ascii_case(&name)) {
            continue;
        }
        let path = dir.join(name);
        match File::options().write(true).create_new(true).open(&path) {
            Ok(file) => return Ok((path, file)),
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {}
            Err(error) => return Err(error),
        }
    }
    Err(io::Error::from(io::ErrorKind::AlreadyExists))
}

#[cfg(test)]
mod tests {
    use super::{create_temp, write_file};
    use std::io;
    use std::path::PathBuf;

    struct TestDir(PathBuf);

    impl TestDir {
        fn new(name: &str) -> io::Result<Self> {
            let path = std::env::temp_dir().join(format!("emd-{name}-{}", std::process::id()));
            std::fs::create_dir(&path)?;
            Ok(Self(path))
        }
    }

    impl Drop for TestDir {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn temporary_file_is_distinct_from_destination() -> io::Result<()> {
        let dir = TestDir::new("output-destination")?;
        for name in [
            format!(".emd-{}-0", std::process::id()),
            format!(".EMD-{}-0", std::process::id()),
        ] {
            let target = dir.0.join(&name);
            let (temp, file) = create_temp(&target)?;
            drop(file);
            let temp_name = temp
                .file_name()
                .and_then(|name| name.to_str())
                .ok_or_else(|| io::Error::other("temporary filename must be ASCII"))?;
            assert!(
                !temp_name.eq_ignore_ascii_case(&name),
                "the temporary file must differ on case-insensitive filesystems"
            );
            assert!(
                !target.exists(),
                "the destination must stay absent until rename"
            );
        }
        Ok(())
    }

    #[test]
    fn existing_temporary_files_are_preserved() -> io::Result<()> {
        let dir = TestDir::new("output-collision")?;
        let occupied = [
            dir.0.join(format!(".emd-{}", std::process::id())),
            dir.0.join(format!(".emd-{}-0", std::process::id())),
        ];
        for path in &occupied {
            std::fs::write(path, b"unrelated content")?;
        }
        let target = dir.0.join("diagram.svg");
        write_file(&target, b"rendered diagram", None)?;
        for path in &occupied {
            assert_eq!(std::fs::read(path)?, b"unrelated content");
        }
        assert_eq!(std::fs::read(target)?, b"rendered diagram");
        assert_eq!(std::fs::read_dir(&dir.0)?.count(), 3);
        Ok(())
    }

    #[test]
    fn creation_failure_preserves_every_existing_file() -> io::Result<()> {
        let dir = TestDir::new("output-occupied")?;
        for attempt in 0..64u32 {
            let path = dir.0.join(format!(".emd-{}-{attempt}", std::process::id()));
            std::fs::write(path, b"unrelated content")?;
        }
        let target = dir.0.join("diagram.svg");
        std::fs::write(&target, b"original diagram")?;
        let result = write_file(&target, b"rendered diagram", None);
        assert!(matches!(result, Err(error) if error.kind() == io::ErrorKind::AlreadyExists));
        for attempt in 0..64u32 {
            let path = dir.0.join(format!(".emd-{}-{attempt}", std::process::id()));
            assert_eq!(std::fs::read(path)?, b"unrelated content");
        }
        assert_eq!(std::fs::read(target)?, b"original diagram");
        assert_eq!(std::fs::read_dir(&dir.0)?.count(), 65);
        Ok(())
    }

    #[test]
    fn rename_failure_removes_only_the_owned_temporary_file() -> io::Result<()> {
        let dir = TestDir::new("output-rename")?;
        let occupied = dir.0.join(format!(".emd-{}-0", std::process::id()));
        std::fs::write(&occupied, b"unrelated content")?;
        let target = dir.0.join("diagram.svg");
        std::fs::create_dir(&target)?;
        assert!(write_file(&target, b"rendered diagram", None).is_err());
        assert_eq!(std::fs::read(occupied)?, b"unrelated content");
        assert!(target.is_dir());
        assert_eq!(std::fs::read_dir(&dir.0)?.count(), 2);
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn rewriting_preserves_requested_permissions() -> io::Result<()> {
        use std::os::unix::fs::PermissionsExt;

        let dir = TestDir::new("output-permissions")?;
        let target = dir.0.join("diagram.mmd");
        std::fs::write(&target, b"original diagram")?;
        let permissions = std::fs::Permissions::from_mode(0o640);
        write_file(&target, b"fixed diagram", Some(permissions))?;
        assert_eq!(std::fs::read(&target)?, b"fixed diagram");
        assert_eq!(
            std::fs::metadata(target)?.permissions().mode() & 0o777,
            0o640
        );
        Ok(())
    }
}
