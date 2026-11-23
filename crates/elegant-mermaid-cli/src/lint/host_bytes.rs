//! Transplant fixed Mermaid bodies while preserving every other host byte.

use elegant_mermaid::Span;
use elegant_mermaid::markdown::{self, Block};
use std::io;

pub(super) fn preserve(path: &str, original: &[u8], fixed: String) -> io::Result<Vec<u8>> {
    if std::str::from_utf8(original).is_ok() {
        return Ok(fixed.into_bytes());
    }
    let fixed = fixed.as_bytes();
    let before = markdown::blocks(original);
    let after = markdown::blocks(fixed);
    if before.len() != after.len() {
        return Err(changed_boundaries(path));
    }
    let mut output = Vec::with_capacity(fixed.len());
    let mut original_end = 0;
    let mut fixed_end = 0;
    for (before, after) in before.iter().zip(&after) {
        let before = body_span(original, before);
        let after = body_span(fixed, after);
        let protected = &original[original_end..before.start];
        if String::from_utf8_lossy(protected).as_bytes() != &fixed[fixed_end..after.start] {
            return Err(changed_boundaries(path));
        }
        output.extend_from_slice(protected);
        output.extend_from_slice(&fixed[after.start..after.end]);
        original_end = before.end;
        fixed_end = after.end;
    }
    let protected = &original[original_end..];
    if String::from_utf8_lossy(protected).as_bytes() != &fixed[fixed_end..] {
        return Err(changed_boundaries(path));
    }
    output.extend_from_slice(protected);
    Ok(output)
}

fn body_span(host: &[u8], block: &Block<'_>) -> Span {
    let (Some(first), Some(last)) = (block.lines.first(), block.lines.last()) else {
        let at = after_line(host, block.span.start);
        return Span { start: at, end: at };
    };
    let mut start = first.host_offset;
    while start > 0 && !matches!(host[start - 1], b'\r' | b'\n') {
        start -= 1;
    }
    Span {
        start,
        end: after_line(host, last.host_offset + last.len),
    }
}

fn after_line(host: &[u8], mut at: usize) -> usize {
    while at < host.len() && !matches!(host[at], b'\r' | b'\n') {
        at += 1;
    }
    if host.get(at) == Some(&b'\r') {
        at += 1;
    }
    if host.get(at) == Some(&b'\n') {
        at += 1;
    }
    at
}

fn changed_boundaries(path: &str) -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidData,
        format!("cannot fix {path}: lint fix changed Markdown block boundaries"),
    )
}

#[cfg(test)]
mod tests {
    use super::preserve;
    use std::io;

    #[test]
    fn rejects_protected_changes() {
        let original = b"Before\xff\n```mermaid\nflowchart LR\nA --> B\n```\n";
        for fixed in [
            "Different\u{fffd}\n```mermaid\nflowchart LR\nA --> B\n```\n",
            "Before\u{fffd}\n```mmd\nflowchart LR\nA --> B\n```\n",
            "Before\u{fffd}\n",
            "Before\u{fffd}\n```mermaid\nflowchart LR\nA --> B\n```\n```mermaid\nflowchart LR\n```\n",
        ] {
            let result = preserve("document.md", original, fixed.to_owned());
            assert!(
                matches!(
                    &result,
                    Err(error) if error.kind() == io::ErrorKind::InvalidData
                        && error.to_string()
                            == "cannot fix document.md: lint fix changed Markdown block boundaries"
                ),
                "protected changes must fail without output: {result:?}"
            );
        }
    }

    #[test]
    fn allows_empty_body() -> io::Result<()> {
        let original = b"Before\xff\n```mermaid\nend\n```\nAfter\xfe\n";
        let fixed = "Before\u{fffd}\n```mermaid\n```\nAfter\u{fffd}\n";
        let expected = b"Before\xff\n```mermaid\n```\nAfter\xfe\n";
        assert_eq!(
            preserve("document.md", original, fixed.to_owned())?,
            expected
        );
        Ok(())
    }
}
