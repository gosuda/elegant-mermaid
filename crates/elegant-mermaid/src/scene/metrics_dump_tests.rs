use super::read_dump;

const DUMP: &str = r#"{"version":1,"stage":"layout","kind":"flowchart","profile":"vector","options":{"direction":"LR"},"canvas":{"w":100,"h":50},"boxes":[{"id":"A","role":"node","x":10,"y":10,"w":20,"h":10,"parent":"","exclusive":true},{"id":"B","role":"node","x":60,"y":10,"w":20,"h":10,"parent":"","exclusive":true}],"routes":[{"id":"e0","from":"A","to":"B","orthogonal":true,"points":[[30,15],[60,15]]}],"labels":[{"id":"e0.label","owner":"e0","text":"yes","x":35,"y":5,"w":10,"h":5,"lines":["yes"]}]}"#;

type Edits<'a> = &'a [(&'a str, &'a str)];
type ReasonCase<'a> = (&'a str, Edits<'a>, &'a str);

fn edited(edits: Edits) -> String {
    edits.iter().fold(DUMP.to_owned(), |text, (old, new)| {
        assert!(text.contains(old), "the base dump has no {old:?}");
        text.replacen(old, new, 1)
    })
}

fn reason(text: &str) -> Option<String> {
    read_dump(text).err().map(|error| error.to_string())
}

#[test]
fn dump_reasons_are_fixed() {
    let cases: &[ReasonCase] = &[
        (
            "missing version",
            &[(r#""version":1,"#, "")],
            "missing version",
        ),
        (
            "other version",
            &[(r#""version":1"#, r#""version":2"#)],
            "expected version 1 layout dump",
        ),
        (
            "version text",
            &[(r#""version":1"#, r#""version":"1""#)],
            "expected integer",
        ),
        (
            "version past int32",
            &[(r#""version":1"#, r#""version":99999999999"#)],
            "invalid integer",
        ),
        (
            "model stage",
            &[(r#""stage":"layout""#, r#""stage":"model""#)],
            "expected version 1 layout dump",
        ),
        (
            "cell profile",
            &[(r#""profile":"vector""#, r#""profile":"cell""#)],
            "--metrics needs --profile vector",
        ),
        (
            "TD direction",
            &[(r#""direction":"LR""#, r#""direction":"TD""#)],
            "invalid direction",
        ),
        (
            "missing direction",
            &[(r#""direction":"LR""#, r#""x":0"#)],
            "missing direction",
        ),
        (
            "options array",
            &[(r#""options":{"direction":"LR"}"#, r#""options":[]"#)],
            "expected object",
        ),
        (
            "negative canvas",
            &[(r#""w":100"#, r#""w":-1"#)],
            "canvas has an invalid rectangle",
        ),
        (
            "huge canvas",
            &[(r#""w":100"#, r#""w":600000000"#)],
            "canvas has a coordinate beyond the limit",
        ),
        (
            "canvas text",
            &[(r#""h":50"#, r#""h":"3""#)],
            "expected integer",
        ),
        (
            "box role",
            &[(r#""role":"node""#, r#""role":"frame""#)],
            "invalid box role",
        ),
        (
            "box id number",
            &[(r#""id":"A""#, r#""id":5"#)],
            "expected string",
        ),
        (
            "fractional x",
            &[(r#""x":10"#, r#""x":10.0"#)],
            "expected integer",
        ),
        (
            "x past int32",
            &[(r#""x":10"#, r#""x":3000000000"#)],
            "invalid integer",
        ),
        (
            "negative box width",
            &[(
                r#""w":20,"h":10,"parent":"""#,
                r#""w":-5,"h":10,"parent":"""#,
            )],
            "box A has an invalid rectangle",
        ),
        (
            "box edge past int32",
            &[(r#""x":10,"y":10,"w":20"#, r#""x":2147483647,"y":10,"w":20"#)],
            "box A has an invalid rectangle",
        ),
        (
            "box past the limit",
            &[(r#""x":10,"y":10,"w":20"#, r#""x":600000000,"y":10,"w":20"#)],
            "box A has a coordinate beyond the limit",
        ),
        (
            "exclusive number",
            &[(r#""exclusive":true"#, r#""exclusive":1"#)],
            "expected boolean",
        ),
        (
            "duplicate box",
            &[(r#""id":"B""#, r#""id":"A""#)],
            "box id A appears twice",
        ),
        (
            "unknown parent",
            &[(r#""parent":"""#, r#""parent":"zzz""#)],
            "box A has unknown parent zzz",
        ),
        (
            "own parent",
            &[(r#""parent":"""#, r#""parent":"A""#)],
            "box A is its own ancestor",
        ),
        (
            "parent cycle",
            &[
                (r#""parent":"""#, r#""parent":"B""#),
                (r#""parent":"""#, r#""parent":"A""#),
            ],
            "box A is its own ancestor",
        ),
        (
            "unknown route end",
            &[(r#""to":"B""#, r#""to":"zzz""#)],
            "route e0 names unknown box zzz",
        ),
        (
            "duplicate route",
            &[(
                r#""routes":["#,
                r#""routes":[{"id":"e0","from":"A","to":"B","orthogonal":true,"points":[]},"#,
            )],
            "route id e0 appears twice",
        ),
        (
            "three coordinates",
            &[("[60,15]", "[60,15,1]")],
            "expected point",
        ),
        (
            "point text",
            &[("[60,15]", r#"[60,"15"]"#)],
            "expected integer",
        ),
        ("point not an array", &[("[60,15]", "{}")], "expected array"),
        (
            "point past the limit",
            &[("[60,15]", "[600000000,15]")],
            "route e0 has a coordinate beyond the limit",
        ),
        (
            "unknown label owner",
            &[(r#""owner":"e0""#, r#""owner":"zzz""#)],
            "label e0.label has unknown owner zzz",
        ),
        (
            "negative label height",
            &[(r#""h":5,"lines""#, r#""h":-5,"lines""#)],
            "label e0.label has an invalid rectangle",
        ),
        (
            "line number",
            &[(r#""lines":["yes"]"#, r#""lines":[1]"#)],
            "expected string",
        ),
        (
            "missing lines",
            &[(r#","lines":["yes"]"#, "")],
            "missing lines",
        ),
        (
            "first fault wins",
            &[
                (r#""w":100"#, r#""w":-1"#),
                (r#""parent":"""#, r#""parent":"zzz""#),
            ],
            "canvas has an invalid rectangle",
        ),
        (
            "duplicates before relations",
            &[
                (r#""id":"B""#, r#""id":"A""#),
                (r#""to":"B""#, r#""to":"zzz""#),
            ],
            "box id A appears twice",
        ),
        ("trailing text", &[("}]}", "}]} x")], "invalid JSON"),
        (
            "single quote outside strings",
            &[(r#""version""#, "'version'")],
            "invalid JSON",
        ),
    ];
    for (name, edits, expected) in cases {
        assert_eq!(
            reason(&edited(edits)),
            Some(format!("malformed layout dump: {expected}")),
            "{name}"
        );
    }
}

#[test]
fn dump_input_reasons_are_fixed() {
    let capitalised = DUMP.replacen(r#""version""#, r#""Version""#, 1);
    let byte_order = format!("\u{feff}{DUMP}");
    for (name, text, expected) in [
        ("empty", "", "invalid JSON"),
        ("array", "[]", "invalid JSON"),
        ("empty object", "{}", "missing version"),
        ("byte order", byte_order.as_str(), "invalid JSON"),
        ("capitalised", capitalised.as_str(), "missing version"),
    ] {
        assert_eq!(
            reason(text),
            Some(format!("malformed layout dump: {expected}")),
            "{name}"
        );
    }
}

#[test]
fn dump_accepts_the_shared_valid_documents() {
    for (name, edits) in [
        ("base", &[][..]),
        ("apostrophe", &[(r#""text":"yes""#, r#""text":"it's""#)][..]),
        (
            "unicode escape",
            &[(r#""text":"yes""#, r#""text":"\u00e9""#)][..],
        ),
        (
            "label owner a box",
            &[(r#""owner":"e0""#, r#""owner":"A""#)][..],
        ),
        (
            "unknown member",
            &[(
                r#""kind":"flowchart""#,
                r#""kind":5,"extra":[1,{"a":null}]"#,
            )][..],
        ),
        ("no kind", &[(r#""kind":"flowchart","#, "")][..]),
    ] {
        assert_eq!(reason(&edited(edits)), None, "{name}");
    }
}
