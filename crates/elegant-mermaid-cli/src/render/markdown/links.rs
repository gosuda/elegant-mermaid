//! Markdown text escaping and relative image URLs.

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

/// Resolve ancestor directories in filesystem order. The final output filename
/// stays literal because the atomic writer replaces that entry, including links.
pub(crate) fn relative_url(target: &Path, host: &Path) -> io::Result<String> {
    let parent = host
        .parent()
        .filter(|path| !path.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let parent = resolved_directory(parent)?;
    let name = target.file_name().ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "cannot make asset path relative to host",
        )
    })?;
    let target = resolved_directory(target.parent().unwrap_or(Path::new(".")))?.join(name);
    let target: Vec<_> = target.components().collect();
    let parent: Vec<_> = parent.components().collect();
    let common = target
        .iter()
        .zip(&parent)
        .take_while(|(left, right)| left == right)
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

/// Existing components must be directories. Missing components are prospective
/// directories, so their suffix can be resolved before any output is created.
fn resolved_directory(path: &Path) -> io::Result<PathBuf> {
    let mut directory = std::env::current_dir()?.canonicalize()?;
    for component in path.components() {
        match component {
            Component::Prefix(prefix) => {
                directory = PathBuf::from(prefix.as_os_str());
                if !path.has_root() {
                    directory = std::path::absolute(directory)?.canonicalize()?;
                }
            }
            Component::RootDir => directory.push(component.as_os_str()),
            Component::CurDir => {}
            Component::ParentDir => {
                directory.pop();
            }
            Component::Normal(name) => {
                directory.push(name);
                resolve_existing_directory(&mut directory)?;
            }
        }
    }
    Ok(directory)
}

fn resolve_existing_directory(path: &mut PathBuf) -> io::Result<()> {
    let metadata = match std::fs::symlink_metadata(path.as_path()) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(()),
        Err(error) => return Err(error),
    };
    if metadata.file_type().is_symlink() {
        *path = path.canonicalize()?;
        if !path.metadata()?.is_dir() {
            return Err(io::ErrorKind::NotADirectory.into());
        }
    } else if !metadata.is_dir() {
        return Err(io::ErrorKind::NotADirectory.into());
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
    fn directory_resolution_allows_missing_directories_but_rejects_files()
    -> std::io::Result<()> {
        let directory = TestDir::new()?;
        assert_eq!(
            resolved_directory(&directory.0.join("missing/../images"))?,
            directory.0.join("images")
        );
        assert!(!directory.0.join("missing").exists());
        std::fs::write(directory.0.join("file"), b"sentinel")?;
        assert_eq!(
            resolved_directory(&directory.0.join("file/../images"))
                .map_err(|error| error.kind()),
            Err(std::io::ErrorKind::NotADirectory)
        );
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn directory_links_resolve_before_parents_and_final_links_stay_literal()
    -> std::io::Result<()> {
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
}
