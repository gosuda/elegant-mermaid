use std::fs;
use std::path::{Path, PathBuf};

use super::{Category, Model, resolve};
use crate::diag::{Diagnostic, Severity};
use crate::syntax::eventmodeling::parse;
use crate::syntax::preprocess::preprocess;

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn resolved(source: &str) -> (Model, Vec<Diagnostic>, Vec<Diagnostic>) {
    let prep = preprocess(source);
    let parsed = parse(source, &prep.removed);
    let (model, diagnostics) = resolve(&parsed.document);
    (model, parsed.diagnostics, diagnostics)
}

fn accepted(source: &str) -> bool {
    let (_, parsed, resolved) = resolved(source);
    parsed
        .iter()
        .chain(&resolved)
        .all(|d| d.severity != Severity::Error)
}

fn summary(model: &Model) -> String {
    let boxes: Vec<String> = model
        .frames
        .iter()
        .map(|frame| format!("[\"{}\",{}]", frame.name, frame.lane))
        .collect();
    let lanes: Vec<String> = model
        .lanes
        .iter()
        .map(|lane| format!("[{},\"{}\"]", lane.index, lane.label))
        .collect();
    let relations: Vec<String> = model
        .relations
        .iter()
        .map(|r| {
            format!(
                "[\"{}\",\"{}\"]",
                model.frames[r.source].name, model.frames[r.target].name
            )
        })
        .collect();
    format!(
        "{{\"boxes\":[{}],\"lanes\":[{}],\"relations\":[{}]}}",
        boxes.join(","),
        lanes.join(","),
        relations.join(",")
    )
}

fn compare_state(source_path: &Path, golden_path: &Path) {
    let text = fs::read_to_string(source_path).unwrap();
    let want = fs::read_to_string(golden_path).unwrap();
    let (model, parsed, diagnostics) = resolved(&text);
    assert!(
        parsed.is_empty() && diagnostics.is_empty(),
        "{source_path:?}"
    );
    assert_eq!(want.trim(), summary(&model), "{source_path:?}");
}

fn files_with_extension(dir: &Path, extension: &str) -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = fs::read_dir(dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|e| e == extension))
        .collect();
    files.sort();
    files
}

fn corpus_files() -> Vec<PathBuf> {
    let mut files = Vec::new();
    let base = root().join("corpus/eventmodeling");
    let mut sources: Vec<PathBuf> = fs::read_dir(&base)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.is_dir())
        .collect();
    sources.sort();
    for source in sources {
        files.extend(files_with_extension(&source, "mmd"));
    }
    files
}

#[test]
fn state_matches_upstream() {
    let cases = root().join("spec/golden/eventmodeling/cases");
    let sources = files_with_extension(&cases, "mmd");
    assert!(!sources.is_empty());
    for path in sources {
        compare_state(&path, &path.with_extension("state.json"));
    }
    let corpus = corpus_files();
    assert!(!corpus.is_empty());
    let golden = root().join("spec/golden/eventmodeling/corpus");
    for path in corpus {
        let stem = path.file_stem().unwrap().to_string_lossy().into_owned();
        compare_state(&path, &golden.join(format!("{stem}.state.json")));
    }
}

#[test]
fn corpus_is_accepted() {
    for path in corpus_files() {
        assert!(accepted(&fs::read_to_string(&path).unwrap()), "{path:?}");
    }
}

struct Reader<'a> {
    text: &'a [u8],
    at: usize,
}

impl Reader<'_> {
    fn skip(&mut self) {
        while self.text.get(self.at).is_some_and(u8::is_ascii_whitespace) {
            self.at += 1;
        }
    }

    fn expect(&mut self, byte: u8) {
        self.skip();
        assert_eq!(self.text[self.at], byte);
        self.at += 1;
    }

    fn peek(&mut self) -> u8 {
        self.skip();
        self.text[self.at]
    }

    fn string(&mut self) -> String {
        self.expect(b'"');
        let mut units: Vec<u16> = Vec::new();
        loop {
            let byte = self.text[self.at];
            self.at += 1;
            match byte {
                b'"' => return String::from_utf16(&units).unwrap(),
                b'\\' => {
                    let escape = self.text[self.at];
                    self.at += 1;
                    match escape {
                        b'n' => units.push(10),
                        b'r' => units.push(13),
                        b't' => units.push(9),
                        b'b' => units.push(8),
                        b'f' => units.push(12),
                        b'u' => {
                            let hex =
                                std::str::from_utf8(&self.text[self.at..self.at + 4]).unwrap();
                            units.push(u16::from_str_radix(hex, 16).unwrap());
                            self.at += 4;
                        }
                        other => units.push(u16::from(other)),
                    }
                }
                _ => {
                    let start = self.at - 1;
                    let mut end = self.at;
                    while self.text[end] & 0xc0 == 0x80 {
                        end += 1;
                    }
                    let piece = std::str::from_utf8(&self.text[start..end]).unwrap();
                    units.extend(piece.encode_utf16());
                    self.at = end;
                }
            }
        }
    }
}

struct VerdictCase {
    name: String,
    source: String,
    accept: bool,
}

fn verdict_cases(text: &str) -> Vec<VerdictCase> {
    let mut reader = Reader {
        text: text.as_bytes(),
        at: 0,
    };
    let mut cases = Vec::new();
    reader.expect(b'[');
    while reader.peek() != b']' {
        reader.expect(b'{');
        let (mut name, mut source, mut accept) = (String::new(), String::new(), false);
        while reader.peek() != b'}' {
            let key = reader.string();
            reader.expect(b':');
            match key.as_str() {
                "name" => name = reader.string(),
                "source" => source = reader.string(),
                _ => {
                    reader.skip();
                    accept = reader.text[reader.at..].starts_with(b"true");
                    reader.at += if accept { 4 } else { 5 };
                }
            }
            if reader.peek() == b',' {
                reader.at += 1;
            }
        }
        reader.expect(b'}');
        cases.push(VerdictCase {
            name,
            source,
            accept,
        });
        if reader.peek() == b',' {
            reader.at += 1;
        }
    }
    cases
}

#[test]
fn verdicts_match_upstream() {
    let text =
        fs::read_to_string(root().join("spec/golden/eventmodeling/syntax-cases.json")).unwrap();
    let cases = verdict_cases(&text);
    assert!(cases.len() > 100);
    for case in cases {
        assert_eq!(
            case.accept,
            accepted(&case.source),
            "{}: {:?}",
            case.name,
            case.source
        );
    }
}

#[test]
fn duplicate_frame_ids_report_later_exact_names() -> Result<(), &'static str> {
    let text = "eventmodeling\ntf 01 ui A\nrf 01 cmd B\ntf 1 evt C\ntf 01 evt D\n";
    let (model, parsed, diagnostics) = resolved(text);
    assert!(parsed.is_empty());
    assert_eq!(diagnostics.len(), 2);
    let first = text.find("01").ok_or("first frame")?;
    for (diagnostic, start) in diagnostics.iter().zip([
        text.find("rf 01").ok_or("second frame")? + 3,
        text.rfind("tf 01").ok_or("last frame")? + 3,
    ]) {
        assert_eq!(diagnostic.code, "eventmodeling/duplicate-frame-id");
        assert_eq!(diagnostic.severity, crate::Severity::Error);
        assert_eq!(diagnostic.message, "frame 01 already exists");
        assert_eq!(
            diagnostic.span,
            crate::source::Span {
                start,
                end: start + 2
            }
        );
        assert_eq!(diagnostic.related.len(), 1);
        assert_eq!(
            diagnostic.related[0].span,
            crate::source::Span {
                start: first,
                end: first + 2,
            }
        );
        assert_eq!(diagnostic.related[0].message, "first declared here");
    }
    assert_retained_duplicate_frames(&model);
    Ok(())
}

fn assert_retained_duplicate_frames(model: &Model) {
    assert_eq!(model.frames.len(), 4);
    assert_eq!(model.frames[0].name, "01");
    assert_eq!(model.frames[1].name, "01");
    assert_eq!(model.frames[2].name, "1");
    assert_eq!(model.frames[3].name, "01");
}

#[test]
fn frame_fields() {
    let (model, ..) = resolved("eventmodeling\nrf 07 readmodel Cart.Items\ntf 08 pcr A.B.C\n");
    let (first, second) = (&model.frames[0], &model.frames[1]);
    assert!(first.reset);
    assert_eq!(first.category, Category::ReadModel);
    assert_eq!(first.entity_type, "readmodel");
    assert_eq!(first.display, "Items");
    assert_eq!(first.namespace, "Cart");
    assert!(!second.reset);
    assert_eq!(second.category, Category::Processor);
    assert_eq!(second.display, "A.B.C");
    assert!(second.namespace.is_empty());
    assert_eq!(Category::ReadModel.as_str(), "readmodel");
}

#[test]
fn payload_matches_javascript() {
    let cases = [
        ("tf 01 ui A { a: 1 }", " a: 1"),
        ("tf 01 ui A \"text\"", ""),
        ("tf 01 ui A 'x'", ""),
        ("tf 01 ui A {}", ""),
        ("tf 01 ui A {x}", ""),
        ("tf 01 ui A { \"a\": [1,2] }", " \"a\": [1,2]"),
        ("tf 01 ui A {a}}", "a"),
        ("tf 01 ui A {\u{1f600}}", "\u{fffd}"),
        ("tf 01 ui A {a\u{1f600}}", "a\u{fffd}"),
        ("tf 01 ui A `json` {ab}", "a"),
    ];
    for (source, want) in cases {
        let (model, ..) = resolved(&format!("eventmodeling\n{source}\n"));
        assert!(model.frames[0].has_data, "{source}");
        assert_eq!(model.frames[0].data, want, "{source}");
    }
    let (typed, ..) = resolved("eventmodeling\ntf 01 ui A `json` {ab}\n");
    assert_eq!(typed.frames[0].data_type, "json");
}

#[test]
fn referenced_payload_matches_javascript() {
    let cases = [
        ("{\n a\n b\n}\n", " a\n b\n"),
        ("{\n}\n", "\n"),
        ("{  \n a\n}", "  \n a\n"),
        ("{\n a\n\n}\n", " a\n\n"),
        ("{\n x\u{1f600}\n}\n", " x\u{1f600}\n"),
        ("{\r\n a\r\n}\r\n", " a\n"),
        ("{\r a\r}\r", " a\n"),
    ];
    for (block, want) in cases {
        let (model, ..) = resolved(&format!(
            "eventmodeling\ntf 01 ui A [[D]] {{ inline }}\ndata D {block}"
        ));
        assert!(model.frames[0].has_data, "{block:?}");
        assert_eq!(model.frames[0].data, want, "{block:?}");
    }
}

#[test]
fn unresolved_reference_keeps_inline() {
    let (model, ..) = resolved(
        "eventmodeling\ntf 01 ui A [[Nope]] { keep }\ntf 02 ui B [[Nope]]\ndata D {\n x\n}\n",
    );
    assert!(model.frames[0].has_data);
    assert_eq!(model.frames[0].data, " keep");
    assert!(!model.frames[1].has_data);
}

#[test]
fn first_data_declaration_wins() {
    let (model, ..) =
        resolved("eventmodeling\ntf 01 ui A [[D]]\ndata D {\n first\n}\ndata D {\n second\n}\n");
    assert_eq!(model.frames[0].data, " first\n");
}

#[test]
fn entities_notes_and_gwt_create_nothing() {
    let (model, ..) = resolved(
        "eventmodeling\nentity A\nnote 01 {\n hi\n}\ngwt 01 given ui A then evt A\ntf 01 ui A\n",
    );
    assert_eq!(model.frames.len(), 1);
    assert!(model.relations.is_empty());
}
