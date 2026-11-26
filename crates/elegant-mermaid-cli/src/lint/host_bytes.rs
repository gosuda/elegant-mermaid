//! Transplant fixed Mermaid bodies while preserving every other host byte.

use elegant_mermaid::Span;
use elegant_mermaid::markdown::{self, Block};
use std::io;

pub(super) fn preserve(path: &str, original: &[u8], fixed: String) -> io::Result<Vec<u8>> {
    if std::str::from_utf8(original).is_ok() {
        return Ok(fixed.into_bytes());
    }
    let fixed = fixed.as_bytes();
    let before = body_spans(original);
    let mut after = body_spans(fixed);
    if before.len() != after.len() {
        return Err(changed_boundaries(path));
    }
    align_bodies(path, original, fixed, &before, &mut after)?;
    let mut output = Vec::with_capacity(fixed.len());
    let mut original_end = 0;
    for (before, after) in before.iter().zip(&after) {
        output.extend_from_slice(&original[original_end..before.start]);
        output.extend_from_slice(&fixed[after.start..after.end]);
        original_end = before.end;
    }
    output.extend_from_slice(&original[original_end..]);
    Ok(output)
}

fn body_spans(host: &[u8]) -> Vec<Span> {
    markdown::blocks(host)
        .iter()
        .map(|block| body_span(host, block))
        .collect()
}

fn align_bodies(
    path: &str,
    original: &[u8],
    fixed: &[u8],
    before: &[Span],
    after: &mut [Span],
) -> io::Result<()> {
    let mut original_end = 0;
    let mut fixed_end = 0;
    for index in 0..=before.len() {
        let original_stop = before.get(index).map_or(original.len(), |body| body.start);
        let fixed_stop = after.get(index).map_or(fixed.len(), |body| body.start);
        let gap = match_gap(
            &original[original_end..original_stop],
            fixed,
            Span {
                start: fixed_end,
                end: fixed_stop,
            },
            index > 0,
            index < before.len(),
        )
        .ok_or_else(|| changed_boundaries(path))?;
        if index > 0 {
            after[index - 1].end = gap.start;
        }
        if index < before.len() {
            after[index].start = gap.end;
            original_end = before[index].end;
            fixed_end = after[index].end;
        }
    }
    let mut end = 0;
    for body in after {
        if body.start < end || body.end < body.start || body.end > fixed.len() {
            return Err(changed_boundaries(path));
        }
        end = body.end;
    }
    Ok(())
}

fn match_gap(
    original: &[u8],
    fixed: &[u8],
    bounds: Span,
    has_before: bool,
    has_after: bool,
) -> Option<Span> {
    let start = if has_before && original.first() == Some(&b'\n') && after_crlf(fixed, bounds.start)
    {
        bounds.start - 1
    } else {
        bounds.start
    };
    let end = if has_after && original.last() == Some(&b'\r') && after_crlf(fixed, bounds.end) {
        bounds.end - 1
    } else {
        bounds.end
    };
    let repaired = String::from_utf8_lossy(original);
    for start in [bounds.start, start] {
        for end in [bounds.end, end] {
            if start <= end && fixed.get(start..end) == Some(repaired.as_bytes()) {
                return Some(Span { start, end });
            }
        }
    }
    None
}

fn after_crlf(host: &[u8], at: usize) -> bool {
    host.get(..at).is_some_and(|head| head.ends_with(b"\r\n"))
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

    #[test]
    fn preserves_host_newlines_after_body_deletion() -> io::Result<()> {
        let cases: [(&str, &[u8], &[u8]); 3] = [
            (
                "trailing protected LF",
                b"Before\xff\n> ```mermaid\n> flowchart LR\r> end\n\nAfter\xfe\n",
                b"Before\xff\n> ```mermaid\n> flowchart LR\r\nAfter\xfe\n",
            ),
            (
                "leading body LF",
                b"Before\xff\n- ```mermaid\r  end\n\n  flowchart LR\n  ```\nAfter\xfe\n",
                b"Before\xff\n- ```mermaid\r\n  flowchart LR\n  ```\nAfter\xfe\n",
            ),
            (
                "empty body",
                b"Before\xff\n> ```mermaid\r> end\n\nAfter\xfe\n",
                b"Before\xff\n> ```mermaid\r\nAfter\xfe\n",
            ),
        ];
        for (name, before, after) in cases {
            let fixed = String::from_utf8_lossy(after).into_owned();
            let output = preserve("document.md", before, fixed.clone())?;
            assert_eq!(output, after, "{name}");
            assert_eq!(
                String::from_utf8_lossy(&output).as_ref(),
                fixed.as_str(),
                "{name}: restoring raw gaps must preserve the normalized fixed output"
            );
        }
        Ok(())
    }

    #[test]
    fn rejects_protected_newline_changes() {
        let cases: [(&str, &[u8], &[u8]); 4] = [
            (
                "missing outside LF",
                b"Before\xff\n> ```mermaid\n> flowchart LR\r> end\n\nAfter\xfe\n",
                b"Before\xff\n> ```mermaid\n> flowchart LR\rAfter\xfe\n",
            ),
            (
                "changed prose after coalescence",
                b"Before\xff\n> ```mermaid\n> flowchart LR\r> end\n\nAfter\xfe\n",
                b"Before\xff\n> ```mermaid\n> flowchart LR\r\nDifferent\xfe\n",
            ),
            (
                "added LF at EOF",
                b"Before\xff\n```mermaid\nflowchart LR\n```\r",
                b"Before\xff\n```mermaid\nflowchart LR\n```\r\n",
            ),
            (
                "overlapping empty body",
                b"Before\xff\n> ```mermaid\r\n\nAfter\xfe\n",
                b"Before\xff\n> ```mermaid\r\nAfter\xfe\n",
            ),
        ];
        for (name, before, fixed) in cases {
            let fixed = String::from_utf8_lossy(fixed).into_owned();
            let result = preserve("document.md", before, fixed);
            assert!(
                matches!(&result, Err(error) if error.kind() == io::ErrorKind::InvalidData),
                "{name}: protected changes must fail without output: {result:?}"
            );
        }
    }
}
