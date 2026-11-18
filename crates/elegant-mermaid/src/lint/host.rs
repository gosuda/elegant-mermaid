//! Linting and fixing a Markdown host: every Mermaid block is linted on its
//! own, diagnostics map to host offsets, and `<!-- emd-disable-file -->`
//! directives apply across blocks and are reported once.

use super::engine::{configured_meta, fix_passes, host_pass};
use super::suppression::{Line, file_suppressions, line_at, skip_blanks};
use crate::diag::{self, Diagnostic, Edit, FixSafety, Related, Severity};
use crate::markdown::{self, Block};
use crate::options::{FixOutcome, LintConfig};
use crate::source::Span;

/// The text a host report indexes, and its diagnostics in output order.
#[derive(Debug, Clone, PartialEq)]
pub struct HostReport {
    pub source: String,
    pub diagnostics: Vec<Diagnostic>,
}

/// Lints every Mermaid block of a Markdown host. Input that is not valid
/// UTF-8 is repaired first, with `source/invalid-utf8` at the first bad byte.
pub fn lint_host(host: &[u8], config: &LintConfig) -> HostReport {
    let (text, bad) = crate::source::repair_utf8(host);
    let text = text.into_owned();
    let diagnostics = host_diagnostics(&text, bad, config);
    HostReport {
        source: text,
        diagnostics,
    }
}

/// Applies fixes of safety at most `max` to a Markdown host, as
/// [`crate::apply_fixes`] does to one source.
pub fn apply_host_fixes(host: &[u8], config: &LintConfig, max: FixSafety) -> FixOutcome {
    fix_passes(host, max, |text| host_diagnostics(text, None, config))
}

fn host_diagnostics(text: &str, bad: Option<usize>, config: &LintConfig) -> Vec<Diagnostic> {
    let blocks = markdown::blocks(text.as_bytes());
    let mut skip = fenced_spans(text.as_bytes());
    skip.extend(blocks.iter().map(|block| block.span));
    let mut file = file_suppressions(text, &skip);
    let mut out = Vec::new();
    if let Some(at) = bad {
        out.push(invalid_utf8(at));
    }
    for block in &blocks {
        let document = crate::document::parse_bytes(&block.source);
        let pass = host_pass(&document, config, &mut file);
        out.extend(
            pass.syntax
                .into_iter()
                .chain(pass.lint)
                .map(|diagnostic| host_diagnostic(text.as_bytes(), block, diagnostic)),
        );
    }
    out.extend(configured_meta(file.meta(), config));
    diag::sort(&mut out);
    out
}

fn invalid_utf8(at: usize) -> Diagnostic {
    Diagnostic {
        code: "source/invalid-utf8",
        severity: Severity::Error,
        message: format!("invalid UTF-8 at byte {at}"),
        span: Span {
            start: at,
            end: at + '\u{fffd}'.len_utf8(),
        },
        related: Vec::new(),
        help: "Save the source as UTF-8.".to_owned(),
        fixes: Vec::new(),
    }
}

fn host_span(block: &Block<'_>, span: Span) -> Span {
    let start = block.host_offset(span.start);
    Span {
        start,
        end: start.max(block.host_offset(span.end)),
    }
}

fn host_diagnostic(host: &[u8], block: &Block<'_>, mut diagnostic: Diagnostic) -> Diagnostic {
    diagnostic.span = host_span(block, diagnostic.span);
    diagnostic.related = diagnostic
        .related
        .into_iter()
        .map(|related| Related {
            span: host_span(block, related.span),
            message: related.message,
        })
        .collect();
    for fix in &mut diagnostic.fixes {
        for edit in &mut fix.edits {
            edit.span =
                host_lines(host, block, edit).unwrap_or_else(|| host_span(block, edit.span));
        }
    }
    diagnostic
}

/// A deletion of whole block lines maps to the whole host lines, container
/// prefixes and line endings included, so removing the last line of a block
/// neither leaves a prefix-only line behind nor swallows the next line.
fn host_lines(host: &[u8], block: &Block<'_>, edit: &Edit) -> Option<Span> {
    let source: &[u8] = &block.source;
    let Span { start, end } = edit.span;
    if !edit.new_text.is_empty()
        || start >= end
        || end > source.len()
        || !starts_line(source, start)
    {
        return None;
    }
    let width = terminator_before(source, end);
    if width == 0 && end != source.len() {
        return None;
    }
    let content_end = block.host_offset(end - width);
    Some(Span {
        start: line_start_of(host, block.host_offset(start)),
        end: content_end + terminator_at(host, content_end),
    })
}

fn starts_line(source: &[u8], at: usize) -> bool {
    at == 0 || terminator_before(source, at) > 0
}

fn terminator_before(source: &[u8], at: usize) -> usize {
    if at == 0 || at > source.len() {
        return 0;
    }
    match source[at - 1] {
        b'\n' if at >= 2 && source[at - 2] == b'\r' => 2,
        b'\n' => 1,
        b'\r' if source.get(at) != Some(&b'\n') => 1,
        _ => 0,
    }
}

fn terminator_at(source: &[u8], at: usize) -> usize {
    match (source.get(at), source.get(at + 1)) {
        (Some(b'\r'), Some(b'\n')) => 2,
        (Some(b'\n' | b'\r'), _) => 1,
        _ => 0,
    }
}

fn line_start_of(host: &[u8], mut at: usize) -> usize {
    while at > 0
        && host
            .get(at - 1)
            .is_some_and(|byte| !matches!(byte, b'\n' | b'\r'))
    {
        at -= 1;
    }
    at
}

/// Returns the fence character, the run length, and the offset after the run.
fn fence_run(host: &[u8], line: &Line) -> (u8, usize, usize) {
    let mut at = line.start;
    while at < line.end && at - line.start < 3 && host[at] == b' ' {
        at += 1;
    }
    if at >= line.end || (host[at] != b'`' && host[at] != b'~') {
        return (0, 0, at);
    }
    let fence = host[at];
    let mut run = 0;
    while at + run < line.end && host[at + run] == fence {
        run += 1;
    }
    (fence, run, at + run)
}

fn opening_fence(host: &[u8], line: &Line) -> Option<(u8, usize)> {
    let (fence, run, after) = fence_run(host, line);
    if run < 3 || (fence == b'`' && host[after..line.end].contains(&b'`')) {
        return None;
    }
    Some((fence, run))
}

fn closing_fence(host: &[u8], line: &Line, fence: u8, count: usize) -> bool {
    let (got, run, after) = fence_run(host, line);
    got == fence && run >= count && skip_blanks(host, after, line.end) == line.end
}

/// Every fenced code block of the host, whatever its info string: a closed
/// fence runs through its closing line, an unclosed one to the end.
fn fenced_spans(host: &[u8]) -> Vec<Span> {
    let mut spans = Vec::new();
    let mut pos = 0;
    while pos < host.len() {
        let line = line_at(host, pos);
        pos = line.next;
        let Some((fence, count)) = opening_fence(host, &line) else {
            continue;
        };
        let mut end = host.len();
        while pos < host.len() {
            let inner = line_at(host, pos);
            pos = inner.next;
            if closing_fence(host, &inner, fence, count) {
                end = inner.next;
                break;
            }
        }
        spans.push(Span {
            start: line.start,
            end,
        });
    }
    spans
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fenced_spans_cover_every_info_string_and_unclosed_fences() {
        let host = b"a\n```rust\nx\n```\nb\n~~~~\ny\n~~~\nz\n```mermaid\nflowchart LR\n";
        let spans = fenced_spans(host);
        assert_eq!(spans.len(), 2);
        assert_eq!(&host[spans[0].start..spans[0].end], b"```rust\nx\n```\n");
        assert_eq!(
            &host[spans[1].start..spans[1].end],
            b"~~~~\ny\n~~~\nz\n```mermaid\nflowchart LR\n"
        );
    }

    #[test]
    fn a_backtick_in_a_backtick_info_string_is_not_an_opening_fence() {
        let host = b"```a`b\nx\n```\n";
        let spans = fenced_spans(host);
        assert_eq!(spans.len(), 1);
        assert_eq!(&host[spans[0].start..spans[0].end], b"```\n");
        assert_eq!(fenced_spans(b"~~~a`b\nx\n~~~\n").len(), 1);
    }

    #[test]
    fn host_lint_maps_block_diagnostics_to_host_offsets() {
        let host = "# T\n\n```mermaid\nflowchart LR\n  A -> B\n```\n";
        let report = lint_host(host.as_bytes(), &LintConfig::default());
        assert_eq!(report.source, host);
        assert_eq!(report.diagnostics.len(), 1);
        let diagnostic = &report.diagnostics[0];
        assert_eq!(diagnostic.code, "flowchart/arrow-invalid");
        assert_eq!(&host[diagnostic.span.start..diagnostic.span.end], "->");
    }

    #[test]
    fn host_fix_edits_the_block_in_the_host() {
        let host = "# T\n\n```mermaid\nflowchart LR\n  A -> B\n```\n";
        let fixed = apply_host_fixes(host.as_bytes(), &LintConfig::default(), FixSafety::Safe);
        assert_eq!(fixed.text, host.replace("A -> B", "A --> B"));
        assert_eq!(fixed.applied, 1);
    }

    #[test]
    fn invalid_utf8_is_repaired_and_reported_at_the_first_bad_byte() {
        let host = b"ok\n\xff\n";
        let report = lint_host(host, &LintConfig::default());
        assert_eq!(report.source, "ok\n\u{fffd}\n");
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, "source/invalid-utf8");
        assert_eq!(report.diagnostics[0].span, Span { start: 3, end: 6 });
    }

    #[test]
    fn a_file_directive_is_used_across_blocks_and_reported_once() {
        let dup = "```mermaid\nflowchart LR\n  A[S] --> B[E]\n  A[T] --> C[E]\n```\n";
        let host = format!("<!-- emd-disable-file flowchart/duplicate-ids: ids -->\n{dup}\n{dup}");
        let report = lint_host(host.as_bytes(), &LintConfig::default());
        assert!(report.diagnostics.is_empty(), "{:?}", report.diagnostics);
        let unused = "<!-- emd-disable-file flowchart/duplicate-ids: ids -->\n```mermaid\nflowchart LR\n  A --> B\n```\n```mermaid\nflowchart LR\n  C --> D\n```\n";
        let report = lint_host(unused.as_bytes(), &LintConfig::default());
        let codes: Vec<&str> = report.diagnostics.iter().map(|d| d.code).collect();
        assert_eq!(codes, ["meta/unused-suppression"]);
    }

    #[test]
    fn a_file_directive_inside_a_foreign_fence_is_text() {
        let host = "```rust\n<!-- emd-disable-file -->\n```\n";
        assert!(
            lint_host(host.as_bytes(), &LintConfig::default())
                .diagnostics
                .is_empty()
        );
    }

    #[test]
    fn host_fix_removes_whole_lines() {
        let cases = [
            (
                "last line of a top-level fence",
                "# T\n\n```mermaid\nflowchart TD\n  A --> B\n  end\n```\n\nafter\n",
                "# T\n\n```mermaid\nflowchart TD\n  A --> B\n```\n\nafter\n",
            ),
            (
                "last line inside a block quote",
                "> ```mermaid\n> flowchart TD\n>   A --> B\n>   end\n> ```\n",
                "> ```mermaid\n> flowchart TD\n>   A --> B\n> ```\n",
            ),
            (
                "last line inside a list item",
                "- item\n\n  ```mermaid\n  flowchart TD\n    A --> B\n    end\n  ```\n",
                "- item\n\n  ```mermaid\n  flowchart TD\n    A --> B\n  ```\n",
            ),
            (
                "last line with CRLF endings",
                "```mermaid\r\nflowchart TD\r\n  A --> B\r\n  end\r\n```\r\n",
                "```mermaid\r\nflowchart TD\r\n  A --> B\r\n```\r\n",
            ),
            (
                "last line of an unclosed fence",
                "```mermaid\nflowchart TD\n  A --> B\n  end\n",
                "```mermaid\nflowchart TD\n  A --> B\n",
            ),
            (
                "middle line of a top-level fence",
                "```mermaid\nflowchart TD\n  end\n  A --> B\n```\n",
                "```mermaid\nflowchart TD\n  A --> B\n```\n",
            ),
            (
                "middle line inside a block quote",
                "> ```mermaid\n> flowchart TD\n>   end\n>   A --> B\n> ```\n",
                "> ```mermaid\n> flowchart TD\n>   A --> B\n> ```\n",
            ),
            (
                "first and last lines in one pass",
                "```mermaid\nflowchart TD\n  end\n  A --> B\n  end\n```\n",
                "```mermaid\nflowchart TD\n  A --> B\n```\n",
            ),
            (
                "a blank line before the closing fence stays",
                "```mermaid\nflowchart TD\n  A --> B\n  end\n\n```\n",
                "```mermaid\nflowchart TD\n  A --> B\n\n```\n",
            ),
        ];
        for (name, host, want) in cases {
            let config = LintConfig::default();
            let fixed = apply_host_fixes(host.as_bytes(), &config, FixSafety::Unsafe);
            assert_eq!(fixed.text, want, "{name}");
            assert!(fixed.applied > 0, "{name}");
            let again = apply_host_fixes(fixed.text.as_bytes(), &config, FixSafety::Unsafe);
            assert_eq!(again.text, want, "{name}");
            assert_eq!(again.applied, 0, "{name}");
        }
    }

    #[test]
    fn host_fix_edits_stay_on_host_lines() {
        let host = "> ```mermaid\n> flowchart TD\n>   A --> B\n>   end\n> ```\n";
        let report = lint_host(host.as_bytes(), &LintConfig::default());
        let edits: Vec<&diag::Edit> = report
            .diagnostics
            .iter()
            .flat_map(|diagnostic| &diagnostic.fixes)
            .flat_map(|fix| &fix.edits)
            .collect();
        assert_eq!(edits.len(), 1);
        assert_eq!(&host[edits[0].span.start..edits[0].span.end], ">   end\n");
        assert!(edits[0].new_text.is_empty());
    }

    #[test]
    fn host_fix_keeps_in_line_edits_in_their_block() {
        let host = "> ```mermaid\n> flowchart LR\n>   A -> B\n> ```\n";
        let fixed = apply_host_fixes(host.as_bytes(), &LintConfig::default(), FixSafety::Safe);
        assert_eq!(
            fixed.text,
            "> ```mermaid\n> flowchart LR\n>   A --> B\n> ```\n"
        );
        assert_eq!(fixed.applied, 1);
    }
}
