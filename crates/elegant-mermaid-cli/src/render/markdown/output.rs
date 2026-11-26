use super::Encoded;
use super::links::{alt_text, relative_url, resolved_directory};
use crate::error::CliError;
use crate::options::Options;
use elegant_mermaid::markdown::Block;
use std::ffi::{OsStr, OsString};
use std::io;
use std::path::{Path, PathBuf};

struct Plan {
    images: Vec<PathBuf>,
    host: Option<PathBuf>,
}

pub(super) fn write(
    input: &str,
    bytes: &[u8],
    blocks: &[Block<'_>],
    options: &Options,
    encoded: &[Encoded],
) -> Result<(), CliError> {
    let plan = Plan::new(input, options, blocks.len())?;
    let host = plan
        .host
        .as_ref()
        .map(|path| rewrite(bytes, blocks, encoded, &plan.images, path))
        .transpose()?;
    // Complete every transformation before directory creation or file writes.
    // Resolve each output directory first, mirroring the Go engine: a missing
    // prefix cancelled by `..` must not be created, and a later symlink keeps
    // its meaning. Errors name the path the user supplied.
    let resolve_target = |path: &Path| -> Result<PathBuf, CliError> {
        let parent = path
            .parent()
            .filter(|path| !path.as_os_str().is_empty())
            .unwrap_or(Path::new("."));
        let directory = resolved_directory(parent).map_err(|source| write_error(path, source))?;
        std::fs::create_dir_all(&directory).map_err(|source| write_error(path, source))?;
        let name = path
            .file_name()
            .ok_or_else(|| write_error(path, io::Error::from(io::ErrorKind::IsADirectory)))?;
        Ok(directory.join(name))
    };
    let mut image_targets = Vec::with_capacity(plan.images.len());
    for path in &plan.images {
        image_targets.push(resolve_target(path)?);
    }
    let host_target = match &plan.host {
        Some(path) => Some(resolve_target(path)?),
        None => None,
    };
    for (target, image) in image_targets.iter().zip(encoded) {
        atomic_write(target, &image.bytes)?;
    }
    if let (Some(target), Some(bytes)) = (host_target, host) {
        atomic_write(&target, &bytes)?;
    }
    Ok(())
}

impl Plan {
    fn new(input: &str, options: &Options, count: usize) -> Result<Self, CliError> {
        let output = Path::new(&options.output);
        let host = crate::check::markdown_host(output).then(|| output.to_path_buf());
        validate_output_name(output)?;
        if host.is_some() || options.artefact_dir.is_none() {
            validate_output_target(output)?;
        }
        let (stem, extension, default_dir) = if host.is_some() {
            let stem = file_stem(output)?;
            let mut assets = stem.to_os_string();
            assets.push(".assets");
            (
                stem,
                format_extension(options),
                output.with_file_name(assets),
            )
        } else if options.output.is_empty() {
            (
                file_stem(Path::new(input))?,
                format_extension(options),
                PathBuf::from("."),
            )
        } else {
            let mut extension = OsString::new();
            if let Some(suffix) = output.extension() {
                extension.push(".");
                extension.push(suffix);
            }
            (
                file_stem(output)?,
                extension,
                output.parent().unwrap_or(Path::new(".")).to_path_buf(),
            )
        };
        let directory = options
            .artefact_dir
            .as_ref()
            .map_or(default_dir, PathBuf::from);
        let images = (1..=count)
            .map(|index| {
                let mut name = stem.to_os_string();
                name.push(format!("-{index}"));
                name.push(&extension);
                directory.join(name)
            })
            .collect();
        Ok(Self { images, host })
    }
}

fn format_extension(options: &Options) -> OsString {
    if options.format == "text" {
        ".txt".into()
    } else {
        format!(".{}", options.format).into()
    }
}

fn validate_output_name(path: &Path) -> Result<(), CliError> {
    if path.as_os_str().is_empty() {
        return Ok(());
    }
    let last = path
        .as_os_str()
        .as_encoded_bytes()
        .rsplit(|byte| std::path::is_separator(char::from(*byte)))
        .next();
    if matches!(last, Some(b"" | b"." | b"..")) || path.file_name().is_none() {
        return Err(write_error(
            path,
            io::Error::from(io::ErrorKind::IsADirectory),
        ));
    }
    Ok(())
}

fn validate_output_target(path: &Path) -> Result<(), CliError> {
    if path.as_os_str().is_empty() {
        return Ok(());
    }
    match std::fs::symlink_metadata(path) {
        Ok(metadata) if metadata.is_dir() => Err(write_error(
            path,
            io::Error::from(io::ErrorKind::IsADirectory),
        )),
        Ok(_) => Ok(()),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(write_error(path, error)),
    }
}

fn file_stem(path: &Path) -> Result<&OsStr, CliError> {
    path.file_stem()
        .ok_or_else(|| write_error(path, io::Error::from(io::ErrorKind::IsADirectory)))
}

fn rewrite(
    source: &[u8],
    blocks: &[Block<'_>],
    encoded: &[Encoded],
    images: &[PathBuf],
    path: &Path,
) -> Result<Vec<u8>, CliError> {
    let mut out = Vec::with_capacity(source.len());
    let mut at = 0;
    for ((block, image), target) in blocks.iter().zip(encoded).zip(images) {
        out.extend_from_slice(&source[at..block.span.start]);
        let span = &source[block.span.start..block.span.end];
        out.extend_from_slice(opener_prefix(span).map_err(|source| write_error(path, source))?);
        let url = relative_url(target, path).map_err(|source| write_error(path, source))?;
        out.extend_from_slice(format!("![{}]({url})", alt_text(&image.title)).as_bytes());
        out.extend_from_slice(consumed_ending(span));
        at = block.span.end;
    }
    out.extend_from_slice(&source[at..]);
    Ok(out)
}

fn opener_prefix(span: &[u8]) -> io::Result<&[u8]> {
    let end = span
        .iter()
        .position(|byte| matches!(byte, b'\r' | b'\n'))
        .unwrap_or(span.len());
    let marker = span[..end]
        .windows(3)
        .position(|bytes| matches!(bytes, b"```" | b"~~~" | b":::"));
    marker
        .map(|marker| &span[..marker])
        .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "invalid Markdown block opener"))
}

// A closed block excludes its closing line ending, which the raw suffix keeps.
// An unclosed block includes its last line ending, so replace that ending here.
fn consumed_ending(span: &[u8]) -> &[u8] {
    if span.ends_with(b"\r\n") {
        b"\r\n"
    } else if span.ends_with(b"\n") {
        b"\n"
    } else if span.ends_with(b"\r") {
        b"\r"
    } else {
        b""
    }
}

fn atomic_write(path: &Path, bytes: &[u8]) -> Result<(), CliError> {
    crate::output::write_file(path, bytes, None).map_err(|source| write_error(path, source))
}

fn write_error(path: &Path, source: io::Error) -> CliError {
    CliError::Write {
        path: path.to_string_lossy().into_owned(),
        source,
    }
}

#[cfg(test)]
mod tests {
    use super::{Encoded, Plan, rewrite};
    use crate::options::Options;
    use elegant_mermaid::markdown;
    use std::path::{Path, PathBuf};

    #[test]
    fn raw_host_splice_preserves_prefixes_and_consumed_endings()
    -> Result<(), Box<dyn std::error::Error>> {
        for (source, expected) in [
            (
                &b"Before\xff\r\n> - ```mermaid\r\n>   flowchart LR\r\n>   A --> B\r\n>   ```\r\nAfter\xfe\r\n"[..],
                &b"Before\xff\r\n> - ![diagram](assets/out-1.svg)\r\nAfter\xfe\r\n"[..],
            ),
            (
                b"Before\n> :::mermaid\n> flowchart LR\r> A --> B\rAfter\n",
                b"Before\n> ![diagram](assets/out-1.svg)\rAfter\n",
            ),
            (
                b"Before\n```mermaid\nflowchart LR\nA --> B",
                b"Before\n![diagram](assets/out-1.svg)",
            ),
        ] {
            let blocks = markdown::blocks(source);
            assert_eq!(blocks.len(), 1);
            let encoded = [Encoded { bytes: Vec::new(), title: String::new() }];
            let images = [PathBuf::from("assets/out-1.svg")];
            assert_eq!(rewrite(source, &blocks, &encoded, &images, Path::new("out.md"))?, expected);
        }
        Ok(())
    }

    #[test]
    fn image_names_keep_explicit_extensions_and_dotfile_stems()
    -> Result<(), Box<dyn std::error::Error>> {
        let options = Options {
            output: "unused/name.dat".into(),
            artefact_dir: Some("assets".into()),
            format: "svg".into(),
            ..Options::default()
        };
        let plan = Plan::new("input.md", &options, 2)?;
        assert_eq!(
            plan.images,
            [
                PathBuf::from("assets/name-1.dat"),
                PathBuf::from("assets/name-2.dat")
            ]
        );
        assert!(plan.host.is_none());

        let options = Options {
            output: String::new(),
            format: "text".into(),
            ..options
        };
        let plan = Plan::new(".md", &options, 1)?;
        assert_eq!(plan.images, [PathBuf::from("assets/.md-1.txt")]);
        Ok(())
    }
}
