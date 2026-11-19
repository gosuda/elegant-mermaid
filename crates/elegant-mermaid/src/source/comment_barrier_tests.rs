use crate::diag::Diagnostic;
use crate::source::Span;
use crate::syntax::{
    agentflow, c4, class, er, flowchart, requirement, sequence, state, swimlane, usecase,
};

const COMMENT_LINE: &str = "%% c\n";
const ACCESSIBILITY: &str = "accDescr {\nfirst\n%% c\nsecond\n}\n";

type Digest = fn(&str, &[Span]) -> Vec<String>;

fn diagnostics_digest(diagnostics: &[Diagnostic]) -> Vec<String> {
    diagnostics
        .iter()
        .map(|d| format!("diag {} {:?}", d.code, d.message))
        .collect()
}

macro_rules! kind_digest {
    ($kind:ident) => {
        |src: &str, removed: &[Span]| {
            let mut out: Vec<String> = $kind::lexer::lex(src, removed)
                .iter()
                .map(|t| format!("{} {:?}", t.kind, t.text))
                .collect();
            out.extend(diagnostics_digest(&$kind::parse(src, removed).diagnostics));
            out
        }
    };
}

fn flowchart_tokens(src: &str, removed: &[Span]) -> Vec<String> {
    flowchart::lexer::lex_all(src, removed)
        .tokens
        .iter()
        .map(|t| {
            let text = match &t.text {
                flowchart::tokens::TextVal::None => "",
                flowchart::tokens::TextVal::Slice(span) => &src[span.start..span.end],
                flowchart::tokens::TextVal::Owned(text) => text,
            };
            format!("{:?} {text:?}", t.kind)
        })
        .collect()
}

fn flowchart_digest(src: &str, removed: &[Span]) -> Vec<String> {
    let mut out = flowchart_tokens(src, removed);
    out.extend(diagnostics_digest(
        &flowchart::parse(src, removed).diagnostics,
    ));
    out
}

fn swimlane_digest(src: &str, removed: &[Span]) -> Vec<String> {
    let mut out = flowchart_tokens(src, removed);
    out.extend(diagnostics_digest(
        &swimlane::parse(src, removed).diagnostics,
    ));
    out
}

#[test]
fn comment_line_is_invisible_inside_multiline_tokens() -> Result<(), &'static str> {
    let kinds: [(&str, Digest, Vec<String>); 10] = [
        (
            "flowchart",
            flowchart_digest,
            vec![
                format!("flowchart TD\n{ACCESSIBILITY}A-->B\n"),
                format!("flowchart TD\nA[\"one\n{COMMENT_LINE}two\"]-->B\n"),
                format!("flowchart TD\nclick\n{COMMENT_LINE} A callback\n"),
            ],
        ),
        (
            "swimlane",
            swimlane_digest,
            vec![
                format!("swimlane-beta TD\n{ACCESSIBILITY}A-->B\n"),
                format!("swimlane-beta TD\nA --> B\n{COMMENT_LINE}  --> C\n"),
            ],
        ),
        (
            "agentflow",
            kind_digest!(agentflow),
            vec![
                format!("agentflow-beta\n{ACCESSIBILITY}A-->B\n"),
                format!("agentflow-beta\nA[\"one\n{COMMENT_LINE}two\"]-->B\n"),
                format!("agentflow-beta\nA@{{ label: x,\n{COMMENT_LINE} shape: task }}\n"),
            ],
        ),
        (
            "class",
            kind_digest!(class),
            vec![
                format!("classDiagram\n{ACCESSIBILITY}class A\n"),
                format!("classDiagram\nclass A[\"one\n{COMMENT_LINE}two\"]\n"),
            ],
        ),
        (
            "state",
            kind_digest!(state),
            vec![
                format!("stateDiagram-v2\n{ACCESSIBILITY}A --> B\n"),
                format!("stateDiagram-v2\nstate \"one\n{COMMENT_LINE}two\" as A\n"),
                format!("stateDiagram-v2\nnote left of A\nfirst\n{COMMENT_LINE}second\nend note\n"),
            ],
        ),
        (
            "er",
            kind_digest!(er),
            vec![
                format!("erDiagram\n{ACCESSIBILITY}A ||--|| B : r\n"),
                format!("erDiagram\nA {{\n`one\n{COMMENT_LINE}two` int\n}}\n"),
            ],
        ),
        (
            "requirement",
            kind_digest!(requirement),
            vec![
                format!("requirementDiagram\n{ACCESSIBILITY}requirement r {{\nid: 1\n}}\n"),
                format!(
                    "requirementDiagram\nrequirement r {{\nid: 1\ntext: \"one\n{COMMENT_LINE}two\"\n}}\n"
                ),
            ],
        ),
        (
            "usecase",
            kind_digest!(usecase),
            vec![
                format!("usecase-beta\n{ACCESSIBILITY}actor A\n"),
                format!("usecase-beta\nA(\"`one\n{COMMENT_LINE}two`\")\n"),
            ],
        ),
        (
            "c4",
            kind_digest!(c4),
            vec![
                format!("C4Context\n{ACCESSIBILITY}Person(a,\"A\")\n"),
                format!("C4Context\nPerson(a,\"one\n{COMMENT_LINE}two\")\n"),
            ],
        ),
        (
            "sequence",
            kind_digest!(sequence),
            vec![
                format!("sequenceDiagram\n{ACCESSIBILITY}A->>B: x\n"),
                format!(
                    "sequenceDiagram\nparticipant A@{{ \"type\": \"actor\",\n{COMMENT_LINE} \"x\": 1 }}\n"
                ),
            ],
        ),
    ];
    let mut failures = Vec::new();
    for (name, digest, sources) in kinds {
        for with in sources {
            let (before, after) = with
                .split_once(COMMENT_LINE)
                .ok_or("source has no comment line")?;
            let removed = [Span {
                start: before.len(),
                end: before.len() + COMMENT_LINE.len(),
            }];
            let without = format!("{before}{after}");
            if digest(&with, &removed) != digest(&without, &[]) {
                failures.push(format!("{name}: {with:?}"));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "a removed comment line changed the parse of: {failures:#?}"
    );
    Ok(())
}
