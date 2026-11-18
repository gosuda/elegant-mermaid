use super::*;

const MALFORMED: &str = "malformed config value";
const INVALID_ESCAPE: &str = "invalid escape";
const MULTI_DOCUMENT: &str = "multi-document streams are not supported";
const TAB_INDENT: &str = "tab in indentation";
const PARENT_COLUMN: usize = 0;
const OWNER_COLUMN: usize = 2;

fn read(src: &str) -> (ConfigValue, Vec<Diagnostic>) {
    parse_config_yaml(src, 0, src.len())
}

fn token_end(src: &str, p: usize) -> usize {
    let b = src.as_bytes();
    let Some(&first) = b.get(p) else {
        return b.len();
    };
    match first {
        b'\r' if b.get(p + 1) == Some(&b'\n') => p + 2,
        b'\r' | b' ' | b'\t' | b'\n' => p + 1,
        _ => b[p..]
            .iter()
            .position(|c| matches!(c, b' ' | b'\t' | b'\r' | b'\n'))
            .map_or(b.len(), |n| p + n),
    }
}

fn require_diagnostic(src: &str, ds: &[Diagnostic], message: &str, start: usize) {
    let [d] = ds else {
        unreachable!("input {src:?}: expected one diagnostic; observed {ds:?}")
    };
    assert_eq!(d.code, C_MALFORMED, "input {src:?}");
    assert_eq!(d.message, message, "input {src:?}");
    let end = token_end(src, start);
    assert_eq!(d.span, Span { start, end }, "input {src:?}");
}

fn escape_width(b: &[u8], i: usize) -> usize {
    match b.get(i + 1) {
        Some(b'"' | b'\\' | b'/' | b'b' | b'f' | b'n' | b'r' | b't' | b'\n') => 2,
        Some(b'u')
            if b.get(i + 2..i + 6)
                .is_some_and(|h| h.iter().all(u8::is_ascii_hexdigit)) =>
        {
            6
        }
        _ => 0,
    }
}

struct TailOutcome {
    closed: bool,
    message: &'static str,
    start: usize,
    end: usize,
}

fn quoted_tail_outcome(src: &str, open: usize) -> TailOutcome {
    let b = src.as_bytes();
    let quote = b[open];
    let mut i = open + 1;
    while i < b.len() {
        let c = b[i];
        if c == quote && quote == b'\'' && b.get(i + 1) == Some(&b'\'') {
            i += 2;
        } else if c == quote {
            return TailOutcome {
                closed: true,
                message: "",
                start: 0,
                end: 0,
            };
        } else if c == b'\\' && quote == b'"' {
            let width = escape_width(b, i);
            if width == 0 {
                return TailOutcome {
                    closed: false,
                    message: INVALID_ESCAPE,
                    start: i,
                    end: (i + 2).min(b.len()),
                };
            }
            i += width;
        } else {
            i += 1;
        }
    }
    TailOutcome {
        closed: false,
        message: MALFORMED,
        start: b.len(),
        end: b.len(),
    }
}

fn truncations_of(prefix: &str, scalar: &str) -> Vec<(String, usize)> {
    let mut inputs = Vec::new();
    for cut in 1..scalar.len() {
        for tail in ["", "\n"] {
            inputs.push((format!("{prefix}{}{tail}", &scalar[..cut]), prefix.len()));
        }
    }
    inputs
}

fn quoted_truncations() -> Vec<(String, usize)> {
    let prefixes = [
        "a: ",
        "a:\n  ",
        "a: 1\nb: ",
        "k:\n  a:\n    ",
        "a:\n  - ",
        "config:\n  mindmap:\n    ",
    ];
    let scalars = [
        r##""colorBy: depth""##,
        "'colorBy: depth'",
        r##""esc \" q: \\ \u00e9 end""##,
        "'it''s: ok'",
        "\"multi\n    line: two\"",
        "'one\n\n    two'",
    ];
    let mut inputs = Vec::new();
    for prefix in prefixes {
        for scalar in scalars {
            inputs.extend(truncations_of(prefix, scalar));
        }
    }
    inputs
}

#[test]
fn quoted_value_truncation() {
    let inputs = quoted_truncations();
    assert!(
        inputs.len() > 1000,
        "observed inputs.len()={}",
        inputs.len()
    );
    for (src, open) in inputs {
        let (_, ds) = read(&src);
        let outcome = quoted_tail_outcome(&src, open);
        if outcome.closed {
            assert!(ds.is_empty(), "input {src:?}: observed {ds:?}");
            continue;
        }
        let [d] = ds.as_slice() else {
            unreachable!("input {src:?}: expected one diagnostic; observed {ds:?}")
        };
        assert_eq!(d.code, C_MALFORMED, "input {src:?}");
        assert_eq!(d.message, outcome.message, "input {src:?}");
        let want = Span {
            start: outcome.start,
            end: outcome.end,
        };
        assert_eq!(d.span, want, "input {src:?}");
    }
}

fn quoted_keys_followed_by_non_colon() -> Vec<String> {
    let mut keys = Vec::new();
    for quote in ["\"", "'"] {
        for prefix in ["a: 1\n", ""] {
            keys.push(format!("{prefix}{quote}k: b{quote}"));
        }
    }
    let mut tails = Vec::new();
    for gap in ["", " ", " \t"] {
        for next in ["x", "7", "-", ".", ","] {
            tails.push(format!("{gap}{next}\n"));
        }
    }
    keys.iter()
        .flat_map(|key| tails.iter().map(move |tail| format!("{key}{tail}")))
        .collect()
}

#[test]
fn quoted_key_followed_by_non_colon() {
    let inputs = quoted_keys_followed_by_non_colon();
    assert_eq!(inputs.len(), 60);
    for src in inputs {
        let (_, ds) = read(&src);
        require_diagnostic(&src, &ds, MALFORMED, src.len() - 2);
    }
}

#[test]
fn next_line_plain_value_column() {
    let head = "k:\n  a:\n      plain\n";
    for column in 0..=8usize {
        let src = format!("{head}{}more\n", " ".repeat(column));
        let (value, ds) = read(&src);
        if column > OWNER_COLUMN {
            assert!(ds.is_empty(), "input {src:?}: observed {ds:?}");
            let k = mapping(entry_of(&mapping(value), "k").value.clone());
            assert_eq!(text(entry_of(&k, "a").value.clone()), "plain more");
        } else if column > PARENT_COLUMN && column < OWNER_COLUMN {
            require_diagnostic(&src, &ds, MALFORMED, head.len() + column);
        } else {
            require_diagnostic(&src, &ds, MALFORMED, src.len() - 1);
        }
    }
}

#[test]
fn next_line_flow_value_column() {
    for (head, line) in [
        ("k:\n  a:\n      [1,\n", "2]\n"),
        ("k:\n  a:\n      { \"k\": 1,\n", "\"m\": 2 }\n"),
    ] {
        for column in 0..=8usize {
            let src = format!("{head}{}{line}", " ".repeat(column));
            let (_, ds) = read(&src);
            if column > OWNER_COLUMN {
                assert!(ds.is_empty(), "input {src:?}: observed {ds:?}");
            } else {
                require_diagnostic(&src, &ds, MALFORMED, head.len() + column);
            }
        }
    }
}

#[test]
fn keyless_line_fails_at_line_end() {
    for tail in ["", " # c", "   # c  ", "  ", "\t"] {
        for end in ["\n", ""] {
            let src = format!("a: 1\nb{tail}{end}");
            let (_, ds) = read(&src);
            require_diagnostic(&src, &ds, MALFORMED, "a: 1\nb".len() + tail.len());
        }
    }
}

#[test]
fn tab_during_continuation_probe() {
    for indent in ["", " ", "  "] {
        let src = format!("a: 1\na: 2\n{indent}\tb\n");
        let tab = src.find('\t').unwrap_or(src.len());
        let (_, ds) = read(&src);
        let [d] = ds.as_slice() else {
            unreachable!("input {src:?}: expected one diagnostic; observed {ds:?}")
        };
        assert_eq!(d.code, C_MALFORMED, "input {src:?}");
        assert_eq!(d.message, TAB_INDENT, "input {src:?}");
        assert_eq!(
            d.span,
            Span {
                start: tab,
                end: tab + 1
            },
            "input {src:?}"
        );
    }
}

fn marker_inputs(root: &str, between: &str, marker: &str) -> Vec<(String, usize, bool)> {
    let at = root.len() + 1 + between.len();
    let mut inputs = Vec::new();
    for term in ["\n", " x\n", "\t", ""] {
        inputs.push((format!("{root}\n{between}{marker}{term}"), at, true));
    }
    inputs.push((format!("{root}\n{between}{marker}x\n"), at, false));
    inputs
}

#[test]
fn marker_after_root_value() {
    let mut inputs = Vec::new();
    for root in ["'a'", "\"a\"", "[a]", "{a: b}"] {
        for between in ["", "\n", "# c\n", "  \n"] {
            for marker in ["---", "..."] {
                inputs.extend(marker_inputs(root, between, marker));
            }
        }
    }
    assert_eq!(inputs.len(), 160);
    for (src, at, boundary) in inputs {
        let (_, ds) = read(&src);
        if !boundary {
            require_diagnostic(&src, &ds, MALFORMED, at);
            continue;
        }
        let [d] = ds.as_slice() else {
            unreachable!("input {src:?}: expected one diagnostic; observed {ds:?}")
        };
        assert_eq!(d.code, C_MALFORMED, "input {src:?}");
        assert_eq!(d.message, MULTI_DOCUMENT, "input {src:?}");
        assert_eq!(
            d.span,
            Span {
                start: at,
                end: at + 3
            },
            "input {src:?}"
        );
    }
}

#[test]
fn flow_value_in_sequence_item() {
    let items = sequence(parse_top("- {a: 1 b}\n- [x y]\n- {k: v}\n"));
    assert_eq!(items.len(), 3);
    let first = mapping(items[0].clone());
    assert_eq!(first[0].key, "a");
    assert_eq!(text(first[0].value.clone()), "1 b");
    assert_eq!(
        sequence(items[1].clone()),
        vec![ConfigValue::String(String::from("x y"))]
    );
    assert_eq!(mapping(items[2].clone())[0].key, "k");
}

#[test]
fn node_prefix_inside_flow_sequence_item() {
    for (src, code, message, token) in [
        (
            "- {&a x: 1}\n",
            "config/unsupported-anchor",
            "anchors and aliases are not supported",
            "&a",
        ),
        (
            "- [&a x]\n",
            "config/unsupported-anchor",
            "anchors and aliases are not supported",
            "&a",
        ),
        (
            "- {!t x: 1}\n",
            "config/unsupported-tag",
            "tags are not supported",
            "!t",
        ),
        (
            "- [!t x]\n",
            "config/unsupported-tag",
            "tags are not supported",
            "!t",
        ),
    ] {
        let (_, ds) = read(src);
        let at = src.find(token).unwrap_or(src.len());
        let [d] = ds.as_slice() else {
            unreachable!("input {src:?}: expected one diagnostic; observed {ds:?}")
        };
        assert_eq!(d.code, code, "input {src:?}");
        assert_eq!(d.message, message, "input {src:?}");
        let want = Span {
            start: at,
            end: at + token.len(),
        };
        assert_eq!(d.span, want, "input {src:?}");
    }
}

#[test]
fn next_line_pipe_line_with_map_colon() {
    for header in ["|", ">"] {
        let nested = format!("config:\n {header}\"k\": \"key\"\n");
        let (_, ds) = read(&nested);
        let at = nested.find(header).unwrap_or(nested.len());
        require_diagnostic(&nested, &ds, MALFORMED, at);
        let map_line = format!("a: 1\n{header}k: v\n");
        let (_, ds) = read(&map_line);
        let at = map_line.find(header).unwrap_or(map_line.len());
        require_diagnostic(&map_line, &ds, MALFORMED, at);
    }
}
