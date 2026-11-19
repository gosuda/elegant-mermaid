//! Suppression comments (`spec/lint.md`): the directive grammar, scopes, the
//! `meta/*` findings, and the host-wide `<!-- emd-disable-file -->` form.

use super::describe::{canonical_code, suppressible};
use crate::diag::{Diagnostic, Severity};
use crate::r#gen::lintrules::LINT_RULES;
use crate::source::Span;
use std::collections::BTreeMap;

const UNKNOWN: &str = "meta/unknown-rule";
const UNUSED: &str = "meta/unused-suppression";
const MALFORMED: &str = "meta/malformed-suppression";
const COMMENT_OPEN: &str = "<!--";
const COMMENT_CLOSE: &str = "-->";
const FILE_KEYWORD: &str = "emd-disable-file";

/// Splits a source into line content ranges; LF, CRLF, and a lone CR each end
/// a line, and the ending is never part of the range.
pub(crate) fn lines(src: &str) -> Vec<(usize, usize)> {
    let bytes = src.as_bytes();
    let mut out = Vec::new();
    let mut at = 0;
    while at < bytes.len() {
        let line = line_at(bytes, at);
        out.push((line.start, line.end));
        at = line.next;
    }
    out
}

#[derive(Clone, Copy)]
pub(crate) struct Line {
    pub start: usize,
    pub end: usize,
    pub next: usize,
}

impl Line {
    /// The offset just past the line and its ending, so a diagnostic that
    /// starts on the line ending still belongs to the line.
    fn exclusive_end(self) -> usize {
        if self.next > self.end {
            self.next
        } else {
            self.end + 1
        }
    }
}

pub(crate) fn line_at(src: &[u8], pos: usize) -> Line {
    let mut end = pos;
    while end < src.len() && src[end] != b'\n' && src[end] != b'\r' {
        end += 1;
    }
    if end == src.len() {
        return Line {
            start: pos,
            end,
            next: end,
        };
    }
    let mut next = end + 1;
    if src[end] == b'\r' && next < src.len() && src[next] == b'\n' {
        next += 1;
    }
    Line {
        start: pos,
        end,
        next,
    }
}

fn is_blank(byte: u8) -> bool {
    byte == b' ' || byte == b'\t'
}

pub(crate) fn skip_blanks(src: &[u8], mut from: usize, limit: usize) -> usize {
    while from < limit && is_blank(src[from]) {
        from += 1;
    }
    from
}

fn trim_end(src: &[u8], from: usize, mut end: usize) -> usize {
    while end > from && is_blank(src[end - 1]) {
        end -= 1;
    }
    end
}

fn has_prefix_at(src: &[u8], at: usize, limit: usize, want: &str) -> bool {
    limit >= at + want.len() && &src[at..at + want.len()] == want.as_bytes()
}

fn is_code_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || matches!(byte, b'/' | b'_' | b'-')
}

fn is_keyword_byte(byte: u8) -> bool {
    byte.is_ascii_alphabetic() || byte == b'-'
}

fn keyword_end(src: &[u8], mut pos: usize, limit: usize) -> usize {
    while pos < limit && is_keyword_byte(src[pos]) {
        pos += 1;
    }
    pos
}

fn keyword_terminated(src: &[u8], end: usize, limit: usize) -> bool {
    end == limit || is_blank(src[end]) || src[end] == b':'
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    NextLine,
    Disable,
    Enable,
    DisableDiagram,
}

fn verb(keyword: &[u8]) -> Option<Kind> {
    match keyword {
        b"emd-disable-next-line" => Some(Kind::NextLine),
        b"emd-disable" => Some(Kind::Disable),
        b"emd-disable-diagram" => Some(Kind::DisableDiagram),
        b"emd-enable" => Some(Kind::Enable),
        _ => None,
    }
}

struct Token {
    text: String,
    span: Span,
}

fn scan_token(src: &[u8], pos: usize, limit: usize) -> Option<Token> {
    let mut end = pos;
    while end < limit && is_code_byte(src[end]) {
        end += 1;
    }
    if end == pos {
        return None;
    }
    Some(Token {
        text: String::from_utf8_lossy(&src[pos..end]).into_owned(),
        span: Span { start: pos, end },
    })
}

/// Codes separated by a comma and at most one space. Returns the tokens and
/// the offset where the list stopped.
fn scan_token_list(src: &[u8], pos: usize, limit: usize) -> Option<(Vec<Token>, usize)> {
    let mut pos = skip_blanks(src, pos, limit);
    let mut tokens = Vec::new();
    loop {
        let token = scan_token(src, pos, limit)?;
        pos = token.span.end;
        tokens.push(token);
        if pos == limit || src[pos] != b',' {
            return Some((tokens, pos));
        }
        pos += 1;
        if pos < limit && src[pos] == b' ' {
            pos += 1;
        }
    }
}

fn parse_reason_list(src: &[u8], pos: usize, limit: usize) -> Option<Vec<Token>> {
    let (tokens, stop) = scan_token_list(src, pos, limit)?;
    if stop == limit || src[stop] != b':' {
        return None;
    }
    let reason_start = skip_blanks(src, stop + 1, limit);
    (reason_start < trim_end(src, stop + 1, limit)).then_some(tokens)
}

fn parse_bare_list(src: &[u8], pos: usize, limit: usize) -> Option<Vec<Token>> {
    let (tokens, stop) = scan_token_list(src, pos, limit)?;
    (stop == limit).then_some(tokens)
}

enum LineResult {
    Ordinary,
    Malformed,
    Directive(Kind, Vec<Token>),
}

fn parse_mermaid_line(src: &[u8], line: Line) -> LineResult {
    let start = skip_blanks(src, line.start, line.end);
    if !has_prefix_at(src, start, line.end, "%%")
        || start + 2 >= line.end
        || !is_blank(src[start + 2])
    {
        return LineResult::Ordinary;
    }
    let keyword = skip_blanks(src, start + 2, line.end);
    let end = keyword_end(src, keyword, line.end);
    let Some(kind) = verb(&src[keyword..end]) else {
        return LineResult::Ordinary;
    };
    if !keyword_terminated(src, end, line.end) {
        return LineResult::Ordinary;
    }
    let limit = trim_end(src, end, line.end);
    let tokens = if kind == Kind::Enable {
        parse_bare_list(src, end, limit)
    } else {
        parse_reason_list(src, end, limit)
    };
    match tokens {
        Some(tokens) => LineResult::Directive(kind, tokens),
        None => LineResult::Malformed,
    }
}

fn parse_file_line(host: &[u8], line: Line) -> LineResult {
    let start = skip_blanks(host, line.start, line.end);
    if !has_prefix_at(host, start, line.end, COMMENT_OPEN) {
        return LineResult::Ordinary;
    }
    let keyword = skip_blanks(host, start + COMMENT_OPEN.len(), line.end);
    let end = keyword_end(host, keyword, line.end);
    if &host[keyword..end] != FILE_KEYWORD.as_bytes() || !keyword_terminated(host, end, line.end) {
        return LineResult::Ordinary;
    }
    let Some(limit) = trim_end(host, end, line.end).checked_sub(COMMENT_CLOSE.len()) else {
        return LineResult::Malformed;
    };
    if limit < end || !has_prefix_at(host, limit, limit + COMMENT_CLOSE.len(), COMMENT_CLOSE) {
        return LineResult::Malformed;
    }
    match parse_reason_list(host, end, limit) {
        Some(tokens) => LineResult::Directive(Kind::Disable, tokens),
        None => LineResult::Malformed,
    }
}

fn directive_span(src: &[u8], line: Line) -> Span {
    let start = skip_blanks(src, line.start, line.end);
    Span {
        start,
        end: trim_end(src, start, line.end),
    }
}

struct Finding {
    code: &'static str,
    value: String,
    span: Span,
}

struct CodeRef {
    code: &'static str,
    name: String,
}

/// Resolves each token to its current code. Unknown tokens become findings,
/// and a code that cannot be suppressed blocks the whole directive.
fn classify(tokens: &[Token]) -> (Vec<CodeRef>, Vec<Finding>, bool) {
    let mut refs: Vec<CodeRef> = Vec::new();
    let mut finds = Vec::new();
    let mut blocked = false;
    for token in tokens {
        let Some(code) = canonical_code(&token.text) else {
            finds.push(Finding {
                code: UNKNOWN,
                value: token.text.clone(),
                span: token.span,
            });
            continue;
        };
        blocked = blocked || !suppressible(code);
        if !refs.iter().any(|known| known.code == code) {
            refs.push(CodeRef {
                code,
                name: token.text.clone(),
            });
        }
    }
    (refs, finds, blocked)
}

fn admit(span: Span, tokens: &[Token]) -> (Vec<CodeRef>, Vec<Finding>, bool) {
    let (refs, mut finds, blocked) = classify(tokens);
    if blocked {
        finds.push(Finding {
            code: MALFORMED,
            value: String::new(),
            span,
        });
        return (Vec::new(), finds, false);
    }
    (refs, finds, true)
}

struct Scope {
    code: &'static str,
    start: usize,
    end: usize,
}

struct Directive {
    span: Span,
    names: Vec<String>,
    scopes: Vec<Scope>,
}

impl Directive {
    fn covers(&self, code: &str, at: usize) -> bool {
        self.scopes
            .iter()
            .any(|scope| scope.code == code && at >= scope.start && at < scope.end)
    }
}

struct Raw {
    kind: Kind,
    span: Span,
    line: Line,
    refs: Vec<CodeRef>,
}

fn scan_mermaid(src: &[u8], body_start: usize) -> (Vec<Raw>, Vec<Finding>) {
    let mut raws = Vec::new();
    let mut finds = Vec::new();
    let mut pos = body_start.min(src.len());
    while pos < src.len() {
        let line = line_at(src, pos);
        pos = line.next;
        let span = directive_span(src, line);
        match parse_mermaid_line(src, line) {
            LineResult::Ordinary => {}
            LineResult::Malformed => finds.push(Finding {
                code: MALFORMED,
                value: String::new(),
                span,
            }),
            LineResult::Directive(kind, tokens) => {
                let (refs, more, ok) = admit(span, &tokens);
                finds.extend(more);
                if ok {
                    raws.push(Raw {
                        kind,
                        span,
                        line,
                        refs,
                    });
                }
            }
        }
    }
    (raws, finds)
}

struct Resolver<'a> {
    src: &'a [u8],
    open: BTreeMap<&'static str, (usize, usize)>,
    dirs: Vec<Directive>,
    findings: Vec<Finding>,
}

fn names(refs: &[CodeRef]) -> Vec<String> {
    refs.iter().map(|code| code.name.clone()).collect()
}

fn whole_scopes(refs: &[CodeRef], end: usize) -> Vec<Scope> {
    refs.iter()
        .map(|code| Scope {
            code: code.code,
            start: 0,
            end,
        })
        .collect()
}

impl Resolver<'_> {
    fn resolve(&mut self, raw: &Raw) {
        match raw.kind {
            Kind::NextLine => {
                let scopes = self.next_line_scopes(raw);
                self.add(raw, scopes);
            }
            Kind::DisableDiagram => {
                let scopes = whole_scopes(&raw.refs, self.src.len() + 1);
                self.add(raw, scopes);
            }
            Kind::Disable => self.disable(raw),
            Kind::Enable => self.enable(raw),
        }
    }

    fn add(&mut self, raw: &Raw, scopes: Vec<Scope>) -> usize {
        self.dirs.push(Directive {
            span: raw.span,
            names: names(&raw.refs),
            scopes,
        });
        self.dirs.len() - 1
    }

    fn malformed(&mut self, raw: &Raw) {
        self.findings.push(Finding {
            code: MALFORMED,
            value: String::new(),
            span: raw.span,
        });
    }

    fn next_line_scopes(&self, raw: &Raw) -> Vec<Scope> {
        if raw.line.next >= self.src.len() {
            return Vec::new();
        }
        let next = line_at(self.src, raw.line.next);
        raw.refs
            .iter()
            .map(|code| Scope {
                code: code.code,
                start: next.start,
                end: next.exclusive_end(),
            })
            .collect()
    }

    fn disable(&mut self, raw: &Raw) {
        if raw
            .refs
            .iter()
            .any(|code| self.open.contains_key(code.code))
        {
            self.malformed(raw);
            return;
        }
        let scopes = raw
            .refs
            .iter()
            .map(|code| Scope {
                code: code.code,
                start: raw.line.start,
                end: self.src.len() + 1,
            })
            .collect();
        let index = self.add(raw, scopes);
        for (at, code) in raw.refs.iter().enumerate() {
            self.open.insert(code.code, (index, at));
        }
    }

    fn enable(&mut self, raw: &Raw) {
        if raw
            .refs
            .iter()
            .any(|code| !self.open.contains_key(code.code))
        {
            self.malformed(raw);
            return;
        }
        for code in &raw.refs {
            if let Some((dir, scope)) = self.open.remove(code.code) {
                self.dirs[dir].scopes[scope].end = raw.line.start;
            }
        }
    }
}

fn parse_block_directives(src: &str, body_start: usize) -> (Vec<Directive>, Vec<Finding>) {
    let bytes = src.as_bytes();
    let (raws, mut finds) = scan_mermaid(bytes, body_start);
    let mut resolver = Resolver {
        src: bytes,
        open: BTreeMap::new(),
        dirs: Vec::new(),
        findings: Vec::new(),
    };
    for raw in &raws {
        resolver.resolve(raw);
    }
    finds.extend(resolver.findings);
    (resolver.dirs, finds)
}

/// The `<!-- emd-disable-file CODES: reason -->` directives of a Markdown
/// host. They cover every code they name in every block, and a block that
/// suppresses a diagnostic with one marks it used.
pub struct FileScope {
    dirs: Vec<Directive>,
    used: Vec<bool>,
    findings: Vec<Finding>,
}

/// Parses the host-wide directives of `host`, skipping every line that starts
/// inside one of the `skip` spans (fenced code blocks and Mermaid blocks).
/// Spans are host offsets.
pub fn file_suppressions(host: &str, skip: &[Span]) -> FileScope {
    let bytes = host.as_bytes();
    let mut dirs = Vec::new();
    let mut findings = Vec::new();
    let mut pos = 0;
    while pos < bytes.len() {
        let line = line_at(bytes, pos);
        pos = line.next;
        if skip
            .iter()
            .any(|span| line.start >= span.start && line.start < span.end)
        {
            continue;
        }
        let span = directive_span(bytes, line);
        match parse_file_line(bytes, line) {
            LineResult::Ordinary => {}
            LineResult::Malformed => findings.push(Finding {
                code: MALFORMED,
                value: String::new(),
                span,
            }),
            LineResult::Directive(_, tokens) => {
                let (refs, more, ok) = admit(span, &tokens);
                findings.extend(more);
                if ok {
                    dirs.push(Directive {
                        span,
                        names: names(&refs),
                        scopes: whole_scopes(&refs, usize::MAX),
                    });
                }
            }
        }
    }
    FileScope {
        used: vec![false; dirs.len()],
        dirs,
        findings,
    }
}

impl FileScope {
    /// The metadiagnostics of the host-wide directives: the findings made
    /// while parsing, then one `meta/unused-suppression` for each directive
    /// that no block used.
    pub(crate) fn meta(&self) -> Vec<Diagnostic> {
        let mut out: Vec<Diagnostic> = self.findings.iter().map(finding_diagnostic).collect();
        out.extend(
            unused_findings(&self.dirs, &self.used)
                .iter()
                .map(finding_diagnostic),
        );
        out
    }
}

fn unused_findings(dirs: &[Directive], used: &[bool]) -> Vec<Finding> {
    dirs.iter()
        .zip(used)
        .filter(|(dir, used)| !**used && !dir.names.is_empty())
        .map(|(dir, _)| Finding {
            code: UNUSED,
            value: dir.names.join(", "),
            span: dir.span,
        })
        .collect()
}

fn finding_diagnostic(finding: &Finding) -> Diagnostic {
    let row = LINT_RULES.iter().find(|row| row.code == finding.code);
    Diagnostic {
        code: finding.code,
        severity: Severity::Warning,
        message: row.map_or(String::new(), |row| {
            row.summary.replacen("CODE", &finding.value, 1)
        }),
        span: finding.span,
        related: Vec::new(),
        help: row.map_or(String::new(), |row| row.help.to_owned()),
        fixes: Vec::new(),
    }
}

pub(crate) struct Outcome {
    pub syntax: Vec<Diagnostic>,
    pub lint: Vec<Diagnostic>,
    pub meta: Vec<Diagnostic>,
}

struct Suppressor<'a> {
    block: &'a [Directive],
    used: Vec<bool>,
    file: Option<&'a mut FileScope>,
}

impl Suppressor<'_> {
    fn filter(&mut self, diagnostics: Vec<Diagnostic>) -> Vec<Diagnostic> {
        diagnostics
            .into_iter()
            .filter(|diagnostic| !self.covers(diagnostic))
            .collect()
    }

    /// Every directive that covers the diagnostic is marked used, not only the
    /// first.
    fn covers(&mut self, diagnostic: &Diagnostic) -> bool {
        let Some(code) = canonical_code(diagnostic.code).filter(|code| suppressible(code)) else {
            return false;
        };
        let at = diagnostic.span.start;
        let mut hit = false;
        for (dir, used) in self.block.iter().zip(&mut self.used) {
            if dir.covers(code, at) {
                *used = true;
                hit = true;
            }
        }
        if let Some(file) = self.file.as_deref_mut() {
            for (dir, used) in file.dirs.iter().zip(&mut file.used) {
                if dir.covers(code, at) {
                    *used = true;
                    hit = true;
                }
            }
        }
        hit
    }
}

/// Applies the block's directives to its diagnostics. `body_start` is the
/// offset where directives start to count (after any frontmatter). `file`
/// holds the host-wide directives when the block belongs to a Markdown host.
pub(crate) fn run(
    source: &str,
    body_start: usize,
    syntax: Vec<Diagnostic>,
    lint: Vec<Diagnostic>,
    file: Option<&mut FileScope>,
) -> Outcome {
    let (dirs, finds) = parse_block_directives(source, body_start);
    let mut suppressor = Suppressor {
        block: &dirs,
        used: vec![false; dirs.len()],
        file,
    };
    let syntax = suppressor.filter(syntax);
    let lint = suppressor.filter(lint);
    let mut meta: Vec<Diagnostic> = finds.iter().map(finding_diagnostic).collect();
    meta.extend(
        unused_findings(&dirs, &suppressor.used)
            .iter()
            .map(finding_diagnostic),
    );
    Outcome { syntax, lint, meta }
}

#[cfg(test)]
mod tests {
    use super::*;

    const DUP: &str = "flowchart/duplicate-ids";

    fn body(directive: &str) -> String {
        format!("flowchart LR\n  A[S] --> B[E]\n{directive}\n  A[T] --> C[E]\n")
    }

    fn finding_codes(src: &str) -> Vec<(&'static str, String)> {
        let (_, finds) = parse_block_directives(src, 0);
        finds.into_iter().map(|f| (f.code, f.value)).collect()
    }

    #[test]
    fn split_lines_on_lf_crlf_and_cr() {
        let text = "a\r\nb\nc\rd";
        assert_eq!(lines(text), vec![(0, 1), (3, 4), (5, 6), (7, 8)]);
        assert_eq!(lines(""), Vec::<(usize, usize)>::new());
    }

    #[test]
    fn the_code_list_accepts_one_space_after_a_comma() {
        for good in [
            format!("  %% emd-disable-next-line {DUP}, common/no-experimental: r"),
            format!("  %% emd-disable-next-line {DUP},common/no-experimental: r"),
        ] {
            assert!(finding_codes(&body(&good)).is_empty(), "{good}");
        }
        for bad in [
            format!("  %% emd-disable-next-line {DUP} : r"),
            format!("  %% emd-disable-next-line {DUP},  common/no-experimental: r"),
            format!("  %% emd-disable-next-line {DUP},: r"),
            format!("  %% emd-disable-next-line {DUP}"),
            format!("  %% emd-disable-next-line {DUP}:   "),
            "  %% emd-disable-next-line flowchart/*: r".to_owned(),
            "  %% emd-disable-next-line : r".to_owned(),
            "  %% emd-disable-next-line".to_owned(),
        ] {
            assert_eq!(
                finding_codes(&body(&bad)),
                [(MALFORMED, String::new())],
                "{bad}"
            );
        }
    }

    #[test]
    fn a_directive_that_names_only_unknown_codes_is_not_reported_unused() {
        let src = body("  %% emd-disable-next-line nope/nothing: r");
        let (dirs, finds) = parse_block_directives(&src, 0);
        assert_eq!(finds.len(), 1);
        assert_eq!(finds[0].code, UNKNOWN);
        assert!(unused_findings(&dirs, &[false]).is_empty());
    }

    #[test]
    fn names_keep_the_first_spelling_of_each_current_code() {
        let src = body(&format!("  %% emd-disable-next-line {DUP}, {DUP}: r"));
        let (dirs, _) = parse_block_directives(&src, 0);
        assert_eq!(dirs[0].names, [DUP]);
    }

    #[test]
    fn syntax_error_rows_and_meta_rows_block_a_directive() {
        for code in [
            "flowchart/arrow-invalid",
            "flowchart/node-unclosed-bracket",
            "meta/unused-suppression",
        ] {
            let src = body(&format!("  %% emd-disable-next-line {code}: r"));
            assert_eq!(finding_codes(&src), [(MALFORMED, String::new())], "{code}");
        }
    }

    #[test]
    fn the_span_excludes_trailing_blanks_and_enable_takes_no_reason() {
        let src = body(&format!("  %% emd-disable-next-line {DUP}: r   "));
        let (dirs, _) = parse_block_directives(&src, 0);
        let text = &src[dirs[0].span.start..dirs[0].span.end];
        assert_eq!(text, format!("%% emd-disable-next-line {DUP}: r"));
        let closed =
            format!("flowchart LR\n%% emd-disable {DUP}: r\n%% emd-enable {DUP}: done\nA --> B\n");
        assert_eq!(finding_codes(&closed), [(MALFORMED, String::new())]);
    }

    #[test]
    fn a_range_runs_until_its_enable_and_a_diagram_directive_covers_every_line() {
        let src = format!(
            "flowchart LR\n%% emd-disable {DUP}: r\nA\n%% emd-enable {DUP}\nB\n%% emd-disable-diagram {DUP}: r\n"
        );
        let (dirs, finds) = parse_block_directives(&src, 0);
        assert!(finds.is_empty());
        assert_eq!(dirs.len(), 2);
        let inside = src.find("A\n").unwrap_or(0);
        let outside = src.find("B\n").unwrap_or(0);
        assert!(dirs[0].covers(DUP, inside));
        assert!(!dirs[0].covers(DUP, outside));
        assert!(dirs[1].covers(DUP, 0) && dirs[1].covers(DUP, outside));
    }

    #[test]
    fn two_directives_that_cover_one_diagnostic_are_both_used() {
        let src = body(&format!(
            "  %% emd-disable-diagram {DUP}: b\n  %% emd-disable-next-line {DUP}: a"
        ));
        let line = |text: &str| {
            let at = src.find(text).unwrap_or(0);
            Span {
                start: at,
                end: at + 1,
            }
        };
        let diagnostic = Diagnostic {
            code: "flowchart/duplicate-ids",
            severity: Severity::Error,
            message: String::new(),
            span: line("  A[T]"),
            related: Vec::new(),
            help: String::new(),
            fixes: Vec::new(),
        };
        let outcome = run(&src, 0, Vec::new(), vec![diagnostic], None);
        assert!(outcome.lint.is_empty());
        assert!(outcome.meta.is_empty(), "{:?}", outcome.meta);
    }

    #[test]
    fn file_directives_skip_lines_inside_skip_spans_and_report_findings() {
        let host = "<!-- emd-disable-file flowchart/duplicate-ids: ids -->\n```mermaid\nflowchart LR\n```\n<!-- emd-disable-file -->\n";
        let blocks = [Span { start: 55, end: 81 }];
        let parsed = file_suppressions(host, &blocks);
        assert_eq!(parsed.dirs.len(), 1);
        assert_eq!(parsed.dirs[0].names, ["flowchart/duplicate-ids"]);
        assert_eq!(parsed.findings.len(), 1);
        assert_eq!(parsed.findings[0].code, MALFORMED);
    }

    #[test]
    fn file_directive_grammar_is_the_block_grammar_with_a_comment_close() {
        let cases = [
            ("<!-- emd-disable-file flowchart/duplicate-ids: r -->", true),
            ("<!--emd-disable-file  flowchart/duplicate-ids: r-->", true),
            (
                "  <!-- emd-disable-file flowchart/duplicate-ids: r -->  ",
                true,
            ),
            (
                "<!-- emd-disable-file flowchart/duplicate-ids , common/no-experimental: r -->",
                false,
            ),
            ("<!-- emd-disable-file flowchart/duplicate-ids: r", false),
            ("<!-- emd-disable-file flowchart/duplicate-ids -->", false),
            ("<!-- emd-disable-file : r -->", false),
        ];
        for (line, ok) in cases {
            let parsed = file_suppressions(line, &[]);
            assert_eq!(
                (parsed.dirs.len(), parsed.findings.len()),
                if ok { (1, 0) } else { (0, 1) },
                "{line}"
            );
        }
    }

    #[test]
    fn unknown_file_codes_point_at_the_token() {
        let host = "<!-- emd-disable-file flowchart/duplicate-ids, flowchart/nope: r -->\n";
        let parsed = file_suppressions(host, &[]);
        assert_eq!(parsed.findings.len(), 1);
        let span = parsed.findings[0].span;
        assert_eq!(&host[span.start..span.end], "flowchart/nope");
    }
}
