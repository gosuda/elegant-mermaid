use crate::diag::{Diagnostic, Severity};
use crate::r#gen::diagnostics::DIAGNOSTICS;
use crate::r#gen::kinds::{KINDS, KindHeader};
use crate::kind::DiagramKind;
use crate::source::Span;

pub const C_UNKNOWN_KIND: &str = "common/unknown-diagram-kind";

pub const C_EMPTY_SOURCE: &str = "common/empty-source";

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Detection {
    pub kind: Option<DiagramKind>,
    pub header: Span,
    pub diagnostics: Vec<Diagnostic>,
}

pub fn detect(src: &str, removed: &[Span]) -> Detection {
    let start = header_start(src, removed);
    if start >= src.len() {
        return Detection {
            kind: None,
            header: Span { start: 0, end: 0 },
            diagnostics: vec![empty_source()],
        };
    }
    let end = token_end(src, start);
    let token = src.get(start..end).unwrap_or_default();
    let header = Span { start, end };
    match kind_of(token) {
        Some(id) => Detection {
            kind: Some(id),
            header,
            diagnostics: Vec::new(),
        },
        None => Detection {
            kind: None,
            header,
            diagnostics: vec![unknown_kind(token, header)],
        },
    }
}

fn header_start(src: &str, removed: &[Span]) -> usize {
    let bytes = src.as_bytes();
    let mut p = 0;
    let mut cursor = 0;
    while p < bytes.len() {
        while cursor < removed.len() && removed.get(cursor).is_some_and(|s| s.end <= p) {
            cursor += 1;
        }
        if let Some(span) = removed.get(cursor)
            && span.start <= p
        {
            p = span.end.min(bytes.len());
            continue;
        }
        if is_blank(bytes.get(p).copied()) {
            p += 1;
            continue;
        }
        break;
    }
    p
}

fn is_blank(byte: Option<u8>) -> bool {
    matches!(byte, Some(b' ' | b'\t' | b'\r' | b'\n'))
}

fn token_end(src: &str, start: usize) -> usize {
    let bytes = src.as_bytes();
    let mut p = start;
    while p < bytes.len() && bytes.get(p).copied().is_some_and(is_token_byte) {
        p += 1;
    }
    p
}

fn is_token_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'-' || byte == b'_'
}

fn kind_of(token: &str) -> Option<DiagramKind> {
    KINDS.iter().find_map(|kind| {
        kind.headers
            .iter()
            .any(|h| header_matches(h, token))
            .then(|| kind_enum(kind.id))
            .flatten()
    })
}

fn header_matches(header: &KindHeader, token: &str) -> bool {
    if header.insensitive {
        token.eq_ignore_ascii_case(header.text)
    } else {
        token == header.text
    }
}

fn empty_source() -> Diagnostic {
    let message = summary(C_EMPTY_SOURCE).to_owned();
    registered(C_EMPTY_SOURCE, message, Span { start: 0, end: 0 })
}

fn unknown_kind(token: &str, span: Span) -> Diagnostic {
    let message = summary(C_UNKNOWN_KIND).replace("TOKEN", token);
    registered(C_UNKNOWN_KIND, message, span)
}

fn summary(code: &str) -> &'static str {
    DIAGNOSTICS
        .iter()
        .find(|row| row.code == code)
        .map_or("", |row| row.summary)
}

fn registered(code: &'static str, message: String, span: Span) -> Diagnostic {
    let row = DIAGNOSTICS.iter().find(|row| row.code == code);
    Diagnostic {
        code,
        severity: row.map_or(Severity::Error, |row| severity(row.severity)),
        message,
        span,
        related: Vec::new(),
        help: row.map_or_else(String::new, |row| row.help.to_owned()),
        fixes: Vec::new(),
    }
}

fn severity(word: &str) -> Severity {
    match word {
        "warning" => Severity::Warning,
        "info" => Severity::Info,
        _ => Severity::Error,
    }
}

fn kind_enum(id: &str) -> Option<DiagramKind> {
    [
        DiagramKind::Flowchart,
        DiagramKind::Swimlane,
        DiagramKind::Agentflow,
        DiagramKind::Class,
        DiagramKind::State,
        DiagramKind::Er,
        DiagramKind::Requirement,
        DiagramKind::Usecase,
        DiagramKind::C4,
        DiagramKind::Sequence,
        DiagramKind::Block,
        DiagramKind::Architecture,
        DiagramKind::Kanban,
        DiagramKind::Packet,
        DiagramKind::Mindmap,
        DiagramKind::Treeview,
        DiagramKind::Ishikawa,
        DiagramKind::Gitgraph,
        DiagramKind::Eventmodeling,
        DiagramKind::Timeline,
        DiagramKind::Journey,
        DiagramKind::Gantt,
        DiagramKind::Xychart,
        DiagramKind::Quadrant,
        DiagramKind::Treemap,
        DiagramKind::Wardley,
        DiagramKind::Pie,
        DiagramKind::Radar,
        DiagramKind::Sankey,
        DiagramKind::Venn,
        DiagramKind::Cynefin,
        DiagramKind::Railroad,
        DiagramKind::Info,
    ]
    .into_iter()
    .find(|kind| kind.id() == id)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::preprocess::preprocess;

    const HEADERS: [(&str, &str, bool); 52] = [
        ("graph", "flowchart", false),
        ("flowchart", "flowchart", false),
        ("flowchart-elk", "flowchart", false),
        ("swimlane-beta", "swimlane", false),
        ("agentflow-beta", "agentflow", false),
        ("classDiagram", "class", false),
        ("classDiagram-v2", "class", false),
        ("stateDiagram", "state", false),
        ("stateDiagram-v2", "state", false),
        ("erDiagram", "er", false),
        ("requirementDiagram", "requirement", false),
        ("requirement", "requirement", false),
        ("usecase-beta", "usecase", false),
        ("C4Context", "c4", false),
        ("C4Container", "c4", false),
        ("C4Component", "c4", false),
        ("C4Dynamic", "c4", false),
        ("C4Deployment", "c4", false),
        ("sequenceDiagram", "sequence", false),
        ("block", "block", false),
        ("block-beta", "block", false),
        ("architecture", "architecture", false),
        ("architecture-beta", "architecture", false),
        ("kanban", "kanban", false),
        ("packet", "packet", false),
        ("packet-beta", "packet", false),
        ("mindmap", "mindmap", false),
        ("treeView-beta", "treeview", false),
        ("ishikawa", "ishikawa", true),
        ("ishikawa-beta", "ishikawa", true),
        ("gitGraph", "gitgraph", false),
        ("eventmodeling", "eventmodeling", false),
        ("timeline", "timeline", false),
        ("journey", "journey", false),
        ("gantt", "gantt", false),
        ("xychart", "xychart", false),
        ("xychart-beta", "xychart", false),
        ("quadrantChart", "quadrant", false),
        ("treemap", "treemap", false),
        ("treemap-beta", "treemap", false),
        ("wardley-beta", "wardley", true),
        ("pie", "pie", false),
        ("radar-beta", "radar", false),
        ("sankey", "sankey", false),
        ("sankey-beta", "sankey", false),
        ("venn-beta", "venn", false),
        ("cynefin-beta", "cynefin", false),
        ("railroad-beta", "railroad", true),
        ("railroad-ebnf-beta", "railroad", true),
        ("railroad-abnf-beta", "railroad", true),
        ("railroad-peg-beta", "railroad", true),
        ("info", "info", false),
    ];

    fn parsed(src: &str) -> Detection {
        detect(src, &preprocess(src).removed)
    }

    #[test]
    fn detect_all_keywords_and_case_rules() {
        assert_eq!(
            KINDS.iter().map(|k| k.headers.len()).sum::<usize>(),
            HEADERS.len()
        );
        for (text, id, insensitive) in HEADERS {
            let d = parsed(text);
            assert_eq!(d.kind.map(DiagramKind::id), Some(id), "{text}");
            assert_eq!(
                d.header,
                Span {
                    start: 0,
                    end: text.len()
                }
            );
            assert!(d.diagnostics.is_empty());
            let upper = text.to_ascii_uppercase();
            assert_eq!(
                parsed(&upper).kind.map(DiagramKind::id),
                insensitive.then_some(id),
                "{text}"
            );
        }
    }

    #[test]
    fn detect_unknown_tokens_and_exact_diagnostics() {
        for token in [
            "blockchain",
            "graphs",
            "pie2",
            "error",
            "flowchart_x",
            "ſequenceDiagram",
        ] {
            let d = parsed(token);
            let end = token
                .bytes()
                .take_while(|b| b.is_ascii_alphanumeric() || *b == b'-' || *b == b'_')
                .count();
            assert_eq!(d.kind, None);
            assert_eq!(d.header, Span { start: 0, end });
            assert_eq!(d.diagnostics.len(), 1);
            let diag = &d.diagnostics[0];
            assert_eq!(diag.code, C_UNKNOWN_KIND);
            assert_eq!(diag.severity, Severity::Error);
            assert_eq!(diag.span, d.header);
            assert_eq!(
                diag.message,
                format!("unknown diagram kind {}", &token[..end])
            );
            assert_eq!(
                diag.help,
                "Start the source with a supported diagram header, for example flowchart."
            );
        }
    }

    #[test]
    fn detect_header_after_preprocessing_for_all_line_endings() {
        for eol in ["\n", "\r\n", "\r"] {
            let prefix = [
                "---",
                "config:",
                "  theme: dark",
                "---",
                "%%{init: {}}%%",
                "%% comment",
                "",
                " \t",
            ]
            .join(eol);
            let src = format!("{prefix}flowchart LR");
            let d = parsed(&src);
            assert_eq!(d.kind, Some(DiagramKind::Flowchart));
            assert_eq!(
                d.header,
                Span {
                    start: prefix.len(),
                    end: prefix.len() + 9
                }
            );
        }
    }

    #[test]
    fn detect_empty_sources_have_zero_span() {
        for src in [
            "",
            " \t\r\n",
            "%% comment",
            "%% comment\r",
            "---\na: 1\n---\n",
            "%%{wrap}%%",
            "%%{init: {}}%%\n%% c\n",
        ] {
            let d = parsed(src);
            assert_eq!(d.kind, None);
            assert_eq!(d.header, Span { start: 0, end: 0 });
            assert_eq!(d.diagnostics.len(), 1);
            let diag = &d.diagnostics[0];
            assert_eq!(diag.code, C_EMPTY_SOURCE);
            assert_eq!(diag.severity, Severity::Error);
            assert_eq!(diag.span, d.header);
            assert_eq!(diag.message, "source is empty");
            assert_eq!(diag.help, "add a diagram header, for example flowchart");
        }
    }
}
