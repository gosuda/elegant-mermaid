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

/// Resolve both paths lexically. Targets need not exist before encoding.
pub(crate) fn relative_url(target: &Path, host: &Path) -> io::Result<String> {
    let target = normalized_absolute(target)?;
    let parent = host
        .parent()
        .filter(|path| !path.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let parent = normalized_absolute(parent)?;
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

fn normalized_absolute(path: &Path) -> io::Result<PathBuf> {
    Ok(clean_path(&std::path::absolute(path)?))
}

/// Clean generated paths without resolving links or requiring existing files.
pub(crate) fn clean_path(path: &Path) -> PathBuf {
    let mut normalized = PathBuf::new();
    for component in path.components() {
        match component {
            Component::CurDir => {}
            Component::ParentDir => {
                if matches!(
                    normalized.components().next_back(),
                    Some(Component::Normal(_))
                ) {
                    normalized.pop();
                } else if !normalized.has_root() {
                    normalized.push(component.as_os_str());
                }
            }
            component => normalized.push(component.as_os_str()),
        }
    }
    if normalized.as_os_str().is_empty() {
        normalized.push(".");
    }
    normalized
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
    use super::{alt_text, clean_path, relative_url};
    use std::path::Path;

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
    fn generated_paths_clean_dot_segments_without_losing_leading_parents() {
        for (source, expected) in [
            ("./assets/../images/out.svg", "images/out.svg"),
            ("../../images/./out.svg", "../../images/out.svg"),
            ("images/../..", ".."),
            ("assets/..", "."),
        ] {
            assert_eq!(clean_path(Path::new(source)), Path::new(expected));
        }
    }

    #[test]
    fn relative_urls_use_normalized_components_and_encoded_bytes() -> std::io::Result<()> {
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
}
