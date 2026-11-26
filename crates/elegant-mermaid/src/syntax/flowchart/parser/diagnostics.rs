use super::*;

pub(super) fn diagnostic_row(code: &str) -> (&'static str, &'static str) {
    match code {
        "limit/nesting-depth" => (
            "nesting depth exceeds 64",
            "Reduce the nesting to 64 levels or fewer.",
        ),
        "flowchart/unexpected-token" => (
            "unexpected TOKEN, expected one of: LIST",
            "Remove the token, or replace it with one of the listed tokens.",
        ),
        "flowchart/unknown-statement" => (
            "unknown statement TOKEN",
            "Start the line with a node, an edge, or a flowchart statement such as style or subgraph.",
        ),
        "flowchart/unterminated" => (
            "unterminated TOKEN",
            "Close the opening delimiter before the end of the input.",
        ),
        "flowchart/unclosed-node-bracket" => (
            "node bracket TOKEN is never closed",
            "Add the closing bracket that matches the opening bracket.",
        ),
        "flowchart/arrow-invalid" => (
            "A single arrow -> is used in a flowchart",
            "Replace -> with -->, or use -- text --> for an inline label.",
        ),
        "flowchart/link-unsupported-marker" => (
            "An inline link uses a one-sided end marker, such as --x--> or --o-->",
            "Use a symmetric marker pair such as x--x, or a plain arrow with a label.",
        ),
        "flowchart/label-double-in-double" => (
            "A double-quoted label contains another double quote",
            "Use &quot; for the inner quotes.",
        ),
        "flowchart/label-double-in-single" => (
            "A single-quoted label contains an unescaped double quote",
            "Replace the inner double quote with &quot;, or use a double-quoted label with &quot; inside.",
        ),
        "flowchart/label-escaped-quote" => (
            "A node label contains a backslash-escaped quote, which Mermaid does not support",
            "Use &quot; for the inner quotes instead of a backslash escape.",
        ),
        "flowchart/label-quote-in-unquoted" => (
            "A double quote appears inside an unquoted label",
            "Wrap the whole label in double quotes and write inner quotes as &quot;.",
        ),
        "flowchart/label-parens-unquoted" => (
            "An unquoted label contains an opening or closing parenthesis",
            "Wrap the label in double quotes, or replace ( and ) with &#40; and &#41;.",
        ),
        "flowchart/dir-invalid" => (
            "The direction token after the header is not one of TD, TB, BT, RL, LR",
            "Use one of TD, TB, BT, RL, or LR.",
        ),
        "flowchart/dir-kw-invalid" => (
            "An unknown keyword appears before the direction token",
            "Replace the unknown keyword with direction.",
        ),
        "flowchart/link-missing" => (
            "Two nodes appear on one line without a connecting arrow",
            "Insert --> between the two nodes.",
        ),
        "flowchart/end-without-subgraph" => (
            "end appears without a matching subgraph",
            "Remove this end line, or add a subgraph above it.",
        ),
        "flowchart/node-mixed-brackets" => (
            "The opening and closing brackets of a node shape do not match",
            "Close with the bracket that matches the opener, for example ) for (.",
        ),
        "flowchart/node-empty" => (
            "A node shape has empty content, such as A[]",
            "Write text inside the brackets, or drop the brackets and use the bare node id.",
        ),
        "flowchart/quote-unclosed" => (
            "A node label opens a quote but never closes it",
            "Close the quote, for example A[\"Label\"].",
        ),
        "flowchart/class-malformed" => (
            "A class statement is missing node ids or the class name",
            "Write class A,B classname.",
        ),
        "flowchart/linkstyle-range-not-supported" => (
            "A range such as 0:3 is used in the linkStyle index list",
            "Use comma-separated indices instead, for example linkStyle 0,1,2.",
        ),
        "flowchart/click-call-extra-text" => (
            "A click call statement carries tooltip or target text after call fn()",
            "Write click A call doThing() with no trailing text.",
        ),
        _ => ("", ""),
    }
}

pub(super) fn attach_fixes(src: &str, diagnostics: &mut [Diagnostic]) {
    for d in diagnostics {
        d.fixes.clear();
        if let Some(fix) = diagnostic_fix(src, d) {
            d.fixes.push(fix);
        }
    }
}

pub(super) fn single_fix(
    title: &str,
    safety: FixSafety,
    span: Span,
    text: impl Into<String>,
) -> Fix {
    Fix {
        title: title.to_owned(),
        safety,
        edits: vec![Edit {
            span,
            new_text: text.into(),
        }],
    }
}

pub(super) fn diagnostic_fix(src: &str, d: &Diagnostic) -> Option<Fix> {
    let safe = FixSafety::Safe;
    let unsafe_fix = FixSafety::Unsafe;
    let point = Span {
        start: d.span.start,
        end: d.span.start,
    };
    Some(match d.code {
        "flowchart/arrow-invalid" => single_fix("Replace -> with -->", safe, d.span, "-->"),
        "flowchart/link-missing" => single_fix(
            "Insert --> between the two nodes",
            unsafe_fix,
            point,
            "--> ",
        ),
        "flowchart/end-without-subgraph" | "flowchart/meta-unsupported" => {
            let (start, mut end) = line_bounds(src, d.span.start);
            let bytes = src.as_bytes();
            if end < bytes.len() {
                if bytes[end] == b'\r' && bytes.get(end + 1) == Some(&b'\n') {
                    end += 1;
                }
                end += 1;
            }
            let title = if d.code == "flowchart/end-without-subgraph" {
                "Remove the stray end line"
            } else {
                "Remove the unsupported meta line"
            };
            single_fix(title, unsafe_fix, Span { start, end }, "")
        }
        "flowchart/unclosed-node-bracket"
        | "flowchart/node-mixed-brackets"
        | "flowchart/node-empty" => return bracket_fix(src, d),
        "flowchart/label-escaped-quote" | "flowchart/label-double-in-single" => {
            single_fix("Replace the quote with &quot;", safe, d.span, "&quot;")
        }
        "flowchart/label-backtick" => single_fix("Remove the backtick", safe, d.span, ""),
        "flowchart/dir-kw-invalid" => single_fix(
            "Replace the keyword with direction",
            safe,
            d.span,
            "direction",
        ),
        "flowchart/dir-missing" => single_fix(
            "Insert the default direction TD",
            safe,
            Span {
                start: d.span.end,
                end: d.span.end,
            },
            " TD",
        ),
        "flowchart/link-unsupported-marker" => {
            let text: String = src
                .get(d.span.start..d.span.end)
                .unwrap_or("")
                .chars()
                .filter(|c| *c != 'x' && *c != 'o')
                .collect();
            single_fix(
                "Remove the unsupported one-sided marker",
                unsafe_fix,
                d.span,
                text,
            )
        }
        "flowchart/quote-unclosed" => {
            let (_, mut end) = line_bounds(src, d.span.start);
            for i in d.span.start.saturating_add(1)..end {
                if matches!(src.as_bytes()[i], b']' | b')' | b'}') {
                    end = i;
                    break;
                }
            }
            single_fix(
                "Insert the closing quote",
                unsafe_fix,
                Span { start: end, end },
                "\"",
            )
        }
        "flowchart/label-quote-in-unquoted" => return quote_wrapping_fix(src, d),
        _ => return None,
    })
}

pub(super) fn line_bounds(src: &str, at: usize) -> (usize, usize) {
    let bytes = src.as_bytes();
    let mut start = at.min(bytes.len());
    let mut end = start;
    while start > 0 && !matches!(bytes[start - 1], b'\n' | b'\r') {
        start -= 1;
    }
    while end < bytes.len() && !matches!(bytes[end], b'\n' | b'\r') {
        end += 1;
    }
    (start, end)
}

pub(super) fn bracket_opening(src: &str, at: usize) -> Option<(usize, &'static str, &'static str)> {
    let (start, end) = line_bounds(src, at);
    let pairs = [
        ("(((", ")))"),
        ("((", "))"),
        ("([", "])"),
        ("[[", "]]"),
        ("[(", ")]"),
        ("{{", "}}"),
        ("[/", "/]"),
        ("[\\", "\\]"),
        ("(-", "-)"),
        ("[", "]"),
        ("(", ")"),
        ("{", "}"),
        (">", "]"),
        ("|", "|"),
    ];
    let mut i = start;
    while i <= at && i < end {
        if src.as_bytes()[i] == b'>' && i > 0 && b"-=.".contains(&src.as_bytes()[i - 1]) {
            i += 1;
            continue;
        }
        let Some(text) = src.get(i..) else {
            i += 1;
            continue;
        };
        let Some((open, close)) = pairs.iter().find(|(open, _)| text.starts_with(open)) else {
            i += 1;
            continue;
        };
        let offset = src.get(i + open.len()..end)?.find(close);
        if let Some(offset) = offset {
            let finish = i + open.len() + offset + close.len();
            if finish <= at {
                i = finish;
                continue;
            }
        }
        return Some((i, open, close));
    }
    None
}

pub(super) fn bracket_fix(src: &str, d: &Diagnostic) -> Option<Fix> {
    let (at, open, close) = bracket_opening(src, d.span.start)?;
    match d.code {
        "flowchart/unclosed-node-bracket" => Some(single_fix(
            "Add the closing bracket",
            FixSafety::Unsafe,
            Span {
                start: d.span.end,
                end: d.span.end,
            },
            close,
        )),
        "flowchart/node-mixed-brackets" => Some(single_fix(
            "Close with the matching bracket",
            FixSafety::Safe,
            d.span,
            close,
        )),
        "flowchart/node-empty" => {
            let (_, end) = line_bounds(src, at);
            let offset = src.get(at + open.len()..end)?.find(close)?;
            Some(single_fix(
                "Remove the empty bracket pair",
                FixSafety::Safe,
                Span {
                    start: at,
                    end: at + open.len() + offset + close.len(),
                },
                "",
            ))
        }
        _ => None,
    }
}

pub(super) fn quote_wrapping_fix(src: &str, d: &Diagnostic) -> Option<Fix> {
    let (at, open, close) = bracket_opening(src, d.span.start)?;
    let start = at + open.len();
    let (_, end) = line_bounds(src, start);
    let body = src.get(start..end)?;
    let offset = body.find(close)?;
    let text = format!("\"{}\"", body[..offset].replace('"', "&quot;"));
    Some(single_fix(
        "Wrap the label in quotes",
        FixSafety::Safe,
        Span {
            start,
            end: start + offset,
        },
        text,
    ))
}
