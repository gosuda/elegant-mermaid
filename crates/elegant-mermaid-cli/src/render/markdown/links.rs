//! Markdown text escaping and relative image URLs.

use std::borrow::Cow;
use std::ffi::OsStr;
use std::io;
use std::path::{Component, Path, PathBuf};

pub(crate) fn alt_text(title: &str) -> String {
    if title.is_empty() {
        return "diagram".into();
    }
    let mut escaped = String::with_capacity(title.len());
    for character in title.chars() {
        match character {
            '\n' => escaped.push_str("&#10;"),
            '\r' => escaped.push_str("&#13;"),
            character if character.is_ascii_punctuation() => {
                escaped.push('\\');
                escaped.push(character);
            }
            character => escaped.push(character),
        }
    }
    escaped
}

/// Resolve ancestor directories in filesystem order. Normalize the final output
/// name without following it, because the atomic writer replaces that entry.
pub(crate) fn relative_url(target: &Path, host: &Path) -> io::Result<String> {
    let parent = host
        .parent()
        .filter(|path| !path.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let parent = resolved_directory(parent)?;
    let target = resolved_target(target)?;
    let target: Vec<_> = target.components().collect();
    let parent: Vec<_> = parent.components().collect();
    let common = target
        .iter()
        .zip(&parent)
        .take_while(|(left, right)| same_volume(left, right))
        .count();
    if common == 0 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "cannot make asset path relative to host",
        ));
    }
    let mut url = String::new();
    for _ in common..parent.len() {
        push_component(&mut url, b"..");
    }
    for component in &target[common..] {
        push_component(&mut url, component.as_os_str().as_encoded_bytes());
    }
    if url.is_empty() {
        url.push('.');
    }
    Ok(url)
}

/// Whether two leading components name the same volume. Comparison only:
/// resolved paths keep their spelling for filesystem operations. An
/// ordinary drive prefix matches its verbatim form by drive letter;
/// anything else must already be identical.
fn same_volume(left: &Component, right: &Component) -> bool {
    if left == right {
        return true;
    }
    match (left, right) {
        (Component::Prefix(left), Component::Prefix(right)) => {
            same_drive(left.kind(), right.kind())
        }
        _ => false,
    }
}

/// Whether two Windows prefixes name the same drive by letter.
fn same_drive(left: std::path::Prefix<'_>, right: std::path::Prefix<'_>) -> bool {
    match (left, right) {
        (std::path::Prefix::Disk(left), std::path::Prefix::VerbatimDisk(right))
        | (std::path::Prefix::VerbatimDisk(left), std::path::Prefix::Disk(right)) => {
            left.eq_ignore_ascii_case(&right)
        }
        _ => false,
    }
}

/// Existing components must be directories. Missing components are prospective
/// directories, so their suffix can be resolved before any output is created.
pub(crate) fn resolved_directory(path: &Path) -> io::Result<PathBuf> {
    resolved_from(path, &std::env::current_dir()?.canonicalize()?)
}

/// Resolve the parent directory and the final operand name without following
/// the final entry. Link planning and the atomic writer must use this same path.
pub(crate) fn resolved_target(path: &Path) -> io::Result<PathBuf> {
    let parent = path
        .parent()
        .filter(|path| !path.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let directory = resolved_directory(parent)?;
    let name = path
        .file_name()
        .ok_or_else(|| io::Error::from(io::ErrorKind::IsADirectory))?;
    let name = input_name(name, is_verbatim(path), true)?;
    if name.is_empty() {
        return Err(io::ErrorKind::IsADirectory.into());
    }
    Ok(directory.join(name.as_ref()))
}

fn resolved_from(path: &Path, base: &Path) -> io::Result<PathBuf> {
    let literal = is_verbatim(path);
    let mut directory = base.to_path_buf();
    let mut components = path.components().peekable();
    let trailing_marker = path
        .as_os_str()
        .as_encoded_bytes()
        .rsplit(|byte| std::path::is_separator(char::from(*byte)))
        .next()
        .is_some_and(|name| name.is_empty() || name == b".");
    while let Some(component) = components.next() {
        match component {
            Component::Prefix(prefix) => {
                directory = PathBuf::from(prefix.as_os_str());
                if !path.has_root() {
                    directory = std::path::absolute(directory)?.canonicalize()?;
                }
            }
            Component::RootDir => {
                directory.push(component.as_os_str());
                directory = directory.canonicalize()?;
            }
            Component::CurDir => {}
            Component::ParentDir => {
                directory.pop();
            }
            Component::Normal(name) => {
                let last = components.peek().is_none() && !trailing_marker;
                let name = input_name(name, literal, last)?;
                if !name.is_empty() {
                    directory.push(name.as_ref());
                }
                resolve_existing_directory(&mut directory)?;
            }
        }
    }
    Ok(directory)
}

/// Whether the input names a verbatim Windows path, which keeps every
/// component literal. Anything else resolves with ordinary normalization.
fn is_verbatim(path: &Path) -> bool {
    matches!(
        path.components().next(),
        Some(Component::Prefix(prefix))
            if matches!(
                prefix.kind(),
                std::path::Prefix::VerbatimDisk(_)
                    | std::path::Prefix::VerbatimUNC(..)
                    | std::path::Prefix::Verbatim(_)
                    | std::path::Prefix::DeviceNS(_)
            )
    )
}

/// Normalize only an operand component. The synthetic root cannot reinterpret
/// a resolved ancestor with a literal trailing dot or space. The sentinel child
/// supplies native intermediate-component context without a filesystem lookup.
#[cfg(windows)]
fn input_name(name: &OsStr, literal: bool, last: bool) -> io::Result<Cow<'_, OsStr>> {
    if literal {
        return Ok(Cow::Borrowed(name));
    }
    let mut probe = PathBuf::from(r"C:\");
    probe.push(name);
    if !last {
        probe.push("__emd_next_component__");
    }
    let mut normalized = std::path::absolute(probe)?;
    if !last && !normalized.pop() {
        return Err(io::ErrorKind::InvalidInput.into());
    }
    let suffix = normalized
        .strip_prefix(r"C:\")
        .map_err(|_| io::Error::from(io::ErrorKind::InvalidInput))?;
    let mut components = suffix.components();
    let name = match (components.next(), components.next()) {
        (None, None) => OsStr::new("").to_os_string(),
        (Some(Component::Normal(name)), None) => name.to_os_string(),
        _ => return Err(io::ErrorKind::InvalidInput.into()),
    };
    Ok(Cow::Owned(name))
}

#[cfg(not(windows))]
fn input_name(name: &OsStr, _literal: bool, _last: bool) -> io::Result<Cow<'_, OsStr>> {
    Ok(Cow::Borrowed(name))
}

fn resolve_existing_directory(path: &mut PathBuf) -> io::Result<()> {
    let metadata = match std::fs::symlink_metadata(path.as_path()) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(()),
        Err(error) => return Err(error),
    };
    if !metadata.is_dir() && !metadata.file_type().is_symlink() {
        return Err(io::ErrorKind::NotADirectory.into());
    }
    if metadata.file_type().is_symlink() || cfg!(windows) {
        *path = path.canonicalize()?;
        if !path.metadata()?.is_dir() {
            return Err(io::ErrorKind::NotADirectory.into());
        }
    }
    Ok(())
}

fn push_component(url: &mut String, bytes: &[u8]) {
    const HEX: &[u8; 16] = b"0123456789ABCDEF";
    if !url.is_empty() {
        url.push('/');
    }
    for &byte in bytes {
        if byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'.' | b'_' | b'~') {
            url.push(char::from(byte));
        } else {
            url.push('%');
            url.push(char::from(HEX[usize::from(byte >> 4)]));
            url.push(char::from(HEX[usize::from(byte & 15)]));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{alt_text, relative_url, resolved_directory};
    use std::path::{Path, PathBuf};
    use std::sync::atomic::{AtomicUsize, Ordering};

    static NEXT: AtomicUsize = AtomicUsize::new(0);

    struct TestDir(PathBuf);

    impl TestDir {
        fn new() -> std::io::Result<Self> {
            let path = std::env::temp_dir().join(format!(
                "emd-markdown-links-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            std::fs::create_dir(&path)?;
            Ok(Self(path.canonicalize()?))
        }
    }

    impl Drop for TestDir {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    /// Build a probe path that keeps `.` and `..` lexically intact, so the
    /// resolver under test actually sees them. `Path::join` on a verbatim
    /// Windows base collapses `..` lexically (see `PathBuf::push`), which
    /// would make these probes vacuous on Windows.
    fn probe_path(base: &Path, parts: &[&str]) -> PathBuf {
        let separator = std::path::MAIN_SEPARATOR.to_string();
        let mut buf = base.as_os_str().to_owned();
        for part in parts {
            buf.push(&separator);
            buf.push(part);
        }
        PathBuf::from(buf)
    }

    #[test]
    fn title_cannot_change_the_image_syntax() {
        assert_eq!(alt_text(""), "diagram");
        assert_eq!(
            alt_text("A [x](y) & <z> \\\n\r"),
            "A \\[x\\]\\(y\\) \\& \\<z\\> \\\\&#10;&#13;"
        );
        assert_eq!(alt_text("hé😀"), "hé😀");
    }

    #[test]
    fn relative_urls_resolve_directory_components_and_encode_bytes() -> std::io::Result<()> {
        assert_eq!(
            relative_url(
                Path::new("assets/a b#%()é/image.svg"),
                Path::new("docs/output.md")
            )?,
            "../assets/a%20b%23%25%28%29%C3%A9/image.svg"
        );
        assert_eq!(
            relative_url(
                Path::new("docs/../assets/./image.svg"),
                Path::new("docs/./nested/../output.md")
            )?,
            "../assets/image.svg"
        );
        assert_eq!(
            relative_url(Path::new("image.svg"), Path::new("out.md"))?,
            "image.svg"
        );
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn literal_backslash_in_a_unix_filename_is_encoded() -> std::io::Result<()> {
        assert_eq!(
            relative_url(Path::new("a\\b.svg"), Path::new("out.md"))?,
            "a%5Cb.svg"
        );
        Ok(())
    }

    #[test]
    fn directory_resolution_allows_missing_directories_but_rejects_files() -> std::io::Result<()> {
        let directory = TestDir::new()?;
        assert_eq!(
            resolved_directory(&probe_path(&directory.0, &["missing", "..", "images"]))?,
            directory.0.join("images")
        );
        assert!(!directory.0.join("missing").exists());
        std::fs::write(directory.0.join("file"), b"sentinel")?;
        assert_eq!(
            resolved_directory(&probe_path(&directory.0, &["file", "..", "images"]))
                .map_err(|error| error.kind()),
            Err(std::io::ErrorKind::NotADirectory)
        );
        Ok(())
    }

    #[test]
    fn verbatim_and_ordinary_drive_prefixes_share_a_volume() {
        use std::path::Prefix::{Disk, VerbatimDisk};
        assert!(super::same_drive(Disk(b'C'), VerbatimDisk(b'C')));
        assert!(super::same_drive(VerbatimDisk(b'c'), Disk(b'C')));
        assert!(!super::same_drive(Disk(b'C'), VerbatimDisk(b'D')));
        assert!(!super::same_drive(Disk(b'C'), Disk(b'D')));
        assert!(!super::same_drive(VerbatimDisk(b'C'), VerbatimDisk(b'D')));
    }

    #[cfg(unix)]
    #[test]
    fn directory_links_resolve_before_parents_and_final_links_stay_literal() -> std::io::Result<()>
    {
        let directory = TestDir::new()?;
        std::fs::create_dir_all(directory.0.join("physical/nested"))?;
        std::os::unix::fs::symlink("physical/nested", directory.0.join("alias"))?;
        assert_eq!(
            resolved_directory(&directory.0.join("alias/../images"))?,
            directory.0.join("physical/images")
        );
        std::os::unix::fs::symlink("missing", directory.0.join("dangling"))?;
        assert_eq!(
            resolved_directory(&directory.0.join("dangling/../images"))
                .map_err(|error| error.kind()),
            Err(std::io::ErrorKind::NotFound)
        );
        std::os::unix::fs::symlink("physical/nested", directory.0.join("image.svg"))?;
        std::os::unix::fs::symlink("missing", directory.0.join("host.md"))?;
        assert_eq!(
            relative_url(&directory.0.join("image.svg"), &directory.0.join("host.md"))?,
            "image.svg"
        );
        Ok(())
    }

    #[cfg(windows)]
    #[test]
    fn relative_and_absolute_urls_share_the_same_windows_volume() -> std::io::Result<()> {
        let canonical = std::env::current_dir()?.canonicalize()?;
        let mut components = canonical.components();
        let Some(std::path::Component::Prefix(prefix)) = components.next() else {
            return Err(std::io::ErrorKind::InvalidInput.into());
        };
        let mut ordinary = match prefix.kind() {
            std::path::Prefix::VerbatimDisk(drive) => {
                PathBuf::from(format!("{}:", char::from(drive)))
            }
            std::path::Prefix::VerbatimUNC(server, share) => {
                let mut prefix = std::ffi::OsString::from(r"\\");
                prefix.push(server);
                prefix.push("\\");
                prefix.push(share);
                PathBuf::from(prefix)
            }
            _ => PathBuf::from(prefix.as_os_str()),
        };
        for component in components {
            ordinary.push(component.as_os_str());
        }
        let missing = PathBuf::from(format!(
            "emd-markdown-volume-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        for parent in [PathBuf::new(), missing] {
            let host = parent.join("out.md");
            let image = parent.join("image.svg");
            assert_eq!(relative_url(&ordinary.join(&image), &host)?, "image.svg");
            assert_eq!(relative_url(&image, &ordinary.join(&host))?, "image.svg");
        }
        Ok(())
    }
    /// The same directory in ordinary spelling, so a probe exercises the
    /// Win32-normalized form instead of the canonical verbatim one.
    #[cfg(windows)]
    fn ordinary_spelling(canonical: &Path) -> std::io::Result<PathBuf> {
        let mut components = canonical.components();
        let mut ordinary = match components.next() {
            Some(std::path::Component::Prefix(prefix)) => match prefix.kind() {
                std::path::Prefix::VerbatimDisk(drive) => {
                    PathBuf::from(format!("{}:", char::from(drive)))
                }
                _ => return Err(std::io::ErrorKind::InvalidInput.into()),
            },
            _ => return Err(std::io::ErrorKind::InvalidInput.into()),
        };
        for component in components {
            ordinary.push(component.as_os_str());
        }
        Ok(ordinary)
    }

    #[cfg(windows)]
    #[test]
    fn mixed_ordinary_and_verbatim_paths_share_the_same_drive() -> std::io::Result<()> {
        let directory = TestDir::new()?;
        std::fs::create_dir_all(directory.0.join("assets"))?;
        let ordinary = ordinary_spelling(&directory.0)?;
        assert_eq!(
            relative_url(
                &directory.0.join("assets").join("image.svg"),
                &ordinary.join("out.md")
            )?,
            "assets/image.svg"
        );
        assert_eq!(
            relative_url(
                &ordinary.join("assets").join("image.svg"),
                &directory.0.join("out.md")
            )?,
            "assets/image.svg"
        );
        Ok(())
    }

    #[cfg(windows)]
    #[test]
    fn ordinary_symlinks_keep_verbatim_only_targets() -> std::io::Result<()> {
        let directory = TestDir::new()?;
        let literal = directory.0.join("assets ");
        std::fs::create_dir_all(&literal)?;
        let link = directory.0.join("linked");
        match std::os::windows::fs::symlink_dir(&literal, &link) {
            Err(error) if error.kind() == std::io::ErrorKind::PermissionDenied => return Ok(()),
            Err(error) => return Err(error),
            Ok(()) => {}
        }
        let ordinary = ordinary_spelling(&directory.0)?;
        let resolved = super::resolved_from(Path::new("linked"), &ordinary)?;
        assert_eq!(resolved, literal);
        std::fs::write(resolved.join("probe.svg"), b"<svg")?;
        assert!(literal.join("probe.svg").exists());
        assert!(!ordinary.join("assets").join("probe.svg").exists());
        Ok(())
    }

    #[cfg(windows)]
    #[test]
    fn ordinary_trailing_dots_keep_win32_normalization() -> std::io::Result<()> {
        let directory = TestDir::new()?;
        let mut components = directory.0.components();
        let Some(std::path::Component::Prefix(prefix)) = components.next() else {
            return Err(std::io::ErrorKind::InvalidInput.into());
        };
        let mut base = match prefix.kind() {
            std::path::Prefix::VerbatimDisk(drive) => {
                PathBuf::from(format!("{}:", char::from(drive)))
            }
            _ => PathBuf::from(prefix.as_os_str()),
        };
        for component in components {
            base.push(component.as_os_str());
        }
        std::fs::create_dir_all(base.join("assets"))?;
        let resolved = super::resolved_from(Path::new("assets."), &base)?;
        assert_eq!(
            resolved.canonicalize()?,
            base.join("assets").canonicalize()?
        );
        std::fs::write(resolved.join("probe.svg"), b"<svg")?;
        assert!(base.join("assets/probe.svg").exists());
        // The ordinary link names the native directory where the file landed.
        assert_eq!(
            super::relative_url(&resolved.join("probe.svg"), &base.join("out.md"))?,
            "assets/probe.svg"
        );
        let verbatim = base.canonicalize()?;
        assert_eq!(
            super::resolved_from(&verbatim.join("assets."), &base)?,
            verbatim.join("assets.")
        );
        assert_eq!(
            super::relative_url(
                &verbatim.join("assets.").join("probe.svg"),
                &verbatim.join("out.md")
            )?,
            "assets./probe.svg"
        );
        Ok(())
    }

    #[cfg(windows)]
    #[test]
    fn ordinary_directory_names_use_native_locations_and_urls() -> std::io::Result<()> {
        for (name, encoded) in [("assets.", "assets."), ("assets ", "assets%20")] {
            let directory = TestDir::new()?;
            let ordinary = ordinary_spelling(&directory.0)?;
            std::fs::create_dir(directory.0.join("assets"))?;
            let native = ordinary.join(name).canonicalize()?;
            assert_eq!(native, directory.0.join("assets").canonicalize()?);
            std::fs::write(native.join("native.svg"), b"native")?;
            assert_eq!(std::fs::read(directory.0.join("assets/native.svg"))?, b"native");
            assert_eq!(resolved_directory(&ordinary.join(name))?, native);
            assert_eq!(
                relative_url(
                    &ordinary.join(name).join("image.svg"),
                    &ordinary.join("out.md")
                )?,
                "assets/image.svg"
            );
            assert_eq!(
                relative_url(&ordinary.join("future./image.svg"), &ordinary.join("out.md"))?,
                "future/image.svg"
            );
            let literal = directory.0.join(name);
            std::fs::create_dir(&literal)?;
            assert_eq!(
                relative_url(&literal.join("image.svg"), &directory.0.join("out.md"))?,
                format!("{encoded}/image.svg")
            );
        }
        Ok(())
    }

    #[cfg(windows)]
    #[test]
    fn directory_links_keep_literal_ancestors_before_normalized_children() -> std::io::Result<()> {
        for (suffix, encoded) in [(" ", "%20"), (".", ".")] {
            let directory = TestDir::new()?;
            let ordinary = ordinary_spelling(&directory.0)?;
            let target = directory.0.join(format!("assets{suffix}"));
            std::fs::create_dir(&target)?;
            std::fs::create_dir(target.join("child"))?;
            std::fs::create_dir(directory.0.join("assets"))?;
            let link = ordinary.join("linked");
            std::os::windows::fs::symlink_dir(&target, &link)?;
            std::fs::write(link.join("native.svg"), b"literal")?;
            assert_eq!(std::fs::read(target.join("native.svg"))?, b"literal");
            assert!(!directory.0.join("assets/native.svg").exists());
            let native_child = link.join("child.").canonicalize()?;
            assert_eq!(native_child, target.join("child").canonicalize()?);
            let resolved = resolved_directory(&link)?;
            assert_eq!(resolved, target.canonicalize()?);
            std::fs::write(resolved.join("written.svg"), b"literal")?;
            assert_eq!(std::fs::read(target.join("written.svg"))?, b"literal");
            assert!(!directory.0.join("assets/written.svg").exists());
            assert_eq!(resolved_directory(&link.join("child."))?, native_child);
            assert_eq!(
                relative_url(&link.join("child./image.svg"), &ordinary.join("out.md"))?,
                format!("assets{encoded}/child/image.svg")
            );
        }
        Ok(())
    }

    #[cfg(windows)]
    #[test]
    fn windows_normalization_retains_intermediate_component_spelling() -> std::io::Result<()> {
        use std::ffi::OsStr;

        for (name, last, expected) in [
            ("assets.", true, "assets"),
            ("assets ", true, "assets"),
            ("assets..", true, "assets"),
            ("...", true, ""),
            ("assets.", false, "assets"),
            ("assets ", false, "assets "),
            ("assets..", false, "assets.."),
        ] {
            assert_eq!(
                super::input_name(OsStr::new(name), false, last)?.as_ref(),
                OsStr::new(expected)
            );
            assert_eq!(
                super::input_name(OsStr::new(name), true, last)?.as_ref(),
                OsStr::new(name)
            );
        }
        let directory = TestDir::new()?;
        let literal = directory.0.join("literal ");
        std::fs::create_dir(&literal)?;
        std::fs::create_dir(literal.join("child"))?;
        let ordinary = ordinary_spelling(&directory.0)?.join(r"literal \child");
        let native = ordinary.canonicalize()?;
        assert_eq!(native, literal.join("child").canonicalize()?);
        assert_eq!(resolved_directory(&ordinary)?, native);
        Ok(())
    }

    #[cfg(windows)]
    #[test]
    fn final_windows_names_are_normalized_without_following_links() -> std::io::Result<()> {
        for (name, encoded) in [("image.svg.", "image.svg."), ("image.svg ", "image.svg%20")] {
            let directory = TestDir::new()?;
            let ordinary = ordinary_spelling(&directory.0)?;
            std::fs::write(ordinary.join(name), b"ordinary")?;
            assert_eq!(std::fs::read(directory.0.join("image.svg"))?, b"ordinary");
            assert_eq!(
                super::resolved_target(&ordinary.join(name))?,
                directory.0.join("image.svg")
            );
            assert_eq!(
                relative_url(&ordinary.join(name), &ordinary.join("out.md"))?,
                "image.svg"
            );
            std::fs::write(directory.0.join(name), b"literal")?;
            assert_eq!(
                super::resolved_target(&directory.0.join(name))?,
                directory.0.join(name)
            );
            assert_eq!(
                relative_url(&directory.0.join(name), &directory.0.join("out.md"))?,
                encoded
            );
            let link = ordinary.join("linked.svg");
            std::os::windows::fs::symlink_file("image.svg", &link)?;
            let resolved = super::resolved_target(&link)?;
            assert_eq!(resolved, directory.0.join("linked.svg"));
            assert!(std::fs::symlink_metadata(resolved)?.file_type().is_symlink());
        }
        Ok(())
    }
}
