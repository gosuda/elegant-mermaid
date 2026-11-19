use crate::DiagramKind;
use crate::cells::{self, Charset};
use crate::error::RenderError;
use crate::geom::Rect;
use crate::layout::families::layout;
use crate::layout::input::{Box as InputBox, Input, Label as InputLabel};
use crate::model::Resolved;
use crate::scene::{
    Align, BoxRole, DumpOptions, DumpValue, Item, Limits, Profile, Scene, TextRole, TextStyle,
};

const PROFILES: [Profile; 2] = [Profile::Vector, Profile::Cell];

fn input_of(source: &str, profile: Profile) -> Result<Input, &'static str> {
    let pre = crate::syntax::preprocess::preprocess(source);
    let (model, diagnostics) = Resolved::parse(DiagramKind::Packet, source, &pre.removed);
    if diagnostics
        .iter()
        .any(|d| d.severity == crate::diag::Severity::Error)
    {
        return Err("source has errors");
    }
    model
        .ok_or("no model")?
        .input(profile, DumpOptions::default())
        .map_err(|_| "input failed")
}

fn scene_of(source: &str, profile: Profile) -> Result<Scene, &'static str> {
    let input = input_of(source, profile)?;
    let (scene, _) = layout(&input).map_err(|_| "layout failed")?;
    let violated = scene.validate().map_err(|_| "validate failed")?;
    assert!(violated.is_none(), "{violated:?}");
    Ok(scene)
}

fn rendered(scene: &Scene, charset: Charset) -> Result<String, &'static str> {
    let options = cells::render::Options {
        charset,
        ..cells::render::Options::default()
    };
    cells::render::render(scene, &options)
        .map(|result| result.text)
        .map_err(|_| "render failed")
}

#[test]
fn corpus_lays_out_validly() -> Result<(), String> {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/packet");
    let mut checked = 0usize;
    for source in std::fs::read_dir(&root).map_err(|e| e.to_string())? {
        let dir = source.map_err(|e| e.to_string())?.path();
        for entry in std::fs::read_dir(&dir).map_err(|e| e.to_string())? {
            let text = std::fs::read_to_string(entry.map_err(|e| e.to_string())?.path())
                .map_err(|e| e.to_string())?;
            for profile in PROFILES {
                scene_of(&text, profile).map_err(String::from)?;
            }
            checked += 1;
        }
    }
    assert!(checked > 0, "corpus/packet holds no file");
    Ok(())
}

#[test]
fn model_dump_encodes_pieces_and_bit_numbers() -> Result<(), &'static str> {
    let input = input_of(
        "packet\ntitle T\n0-3: \"a\"\n4: \"f1\"\n+60: \"c\"\n",
        Profile::Vector,
    )?;
    let ids: Vec<String> = input
        .boxes
        .iter()
        .map(|b| {
            assert!(b.exclusive);
            format!("{} {}", b.id, b.shape)
        })
        .collect();
    assert_eq!(
        ids,
        vec![
            "title title",
            "f0 field;start=0;end=3",
            "f1 field;start=4;end=4",
            "f2 field;start=5;end=31",
            "f3 field;start=32;end=63",
            "f4 field;start=64;end=64",
        ]
    );
    let labels: Vec<String> = input
        .labels
        .iter()
        .map(|l| format!("{}={}", l.id, l.text))
        .collect();
    assert_eq!(
        labels,
        vec![
            "title.label=T",
            "f0.label=a",
            "f0.lead=0",
            "f0.trail=3",
            "f1.bit=4",
            "f2.label=c",
            "f2.lead=5",
            "f2.trail=31",
            "f3.label=c",
            "f3.lead=32",
            "f3.trail=63",
            "f4.label=c",
            "f4.bit=64",
        ]
    );
    Ok(())
}

#[test]
fn model_dump_options_follow_the_config() -> Result<(), &'static str> {
    let source = "---\nconfig:\n  packet:\n    showBits: false\n    bitOrder: descending\n    bitsPerRow: 16\n    rowHeight: 40\n---\npacket\n0-3: \"a\"\n";
    let input = input_of(source, Profile::Vector)?;
    let got: Vec<(&str, &DumpValue)> = input
        .options
        .config
        .iter()
        .map(|(key, value)| (key.as_str(), value))
        .collect();
    assert_eq!(
        got,
        vec![
            ("bitOrder", &DumpValue::String("descending".into())),
            ("bitsPerRow", &DumpValue::Integer(16)),
            ("rowHeight", &DumpValue::Integer(40)),
            ("showBits", &DumpValue::Bool(false)),
        ]
    );
    assert_eq!(input.labels.len(), 1, "no bit numbers without showBits");
    Ok(())
}

#[test]
fn cell_rendering() -> Result<(), &'static str> {
    let scene = scene_of("packet-beta\n0-7: \"Type\"\n8-15: \"Len\"\n", Profile::Cell)?;
    let want = [
        "0             7 8            15",
        "┌─────────────┐ ┌─────────────┐",
        "│    Type     │ │     Len     │",
        "└─────────────┘ └─────────────┘",
        "",
        "",
    ]
    .join("\n");
    assert_eq!(rendered(&scene, Charset::Unicode)?, want);
    assert!(rendered(&scene, Charset::Ascii)?.contains("+-------------+ +-------------+"));
    Ok(())
}

#[test]
fn cell_rows_split_at_the_configured_width() -> Result<(), &'static str> {
    let source = "---\nconfig:\n  packet:\n    bitsPerRow: 8\n    showBits: false\n---\npacket\n0-11: \"a\"\n12-15: \"b\"\n";
    let want = [
        "",
        "┌─────────────┐",
        "│      a      │",
        "└─────────────┘",
        "",
        "┌─────┐ ┌─────┐",
        "│  a  │ │  b  │",
        "└─────┘ └─────┘",
        "",
        "",
    ]
    .join("\n");
    let scene = scene_of(source, Profile::Cell)?;
    assert_eq!(rendered(&scene, Charset::Unicode)?, want);
    Ok(())
}

#[test]
fn descending_numbers_run_high_to_low() -> Result<(), &'static str> {
    let source = "---\nconfig:\n  packet:\n    bitOrder: descending\n    bitsPerRow: 16\n---\npacket\n0-7: \"DATA\"\n8-15: \"HIGH\"\n";
    let text = rendered(&scene_of(source, Profile::Cell)?, Charset::Unicode)?;
    let lines: Vec<&str> = text.split('\n').collect();
    assert!(lines[0].starts_with("15"), "{}", lines[0]);
    assert!(lines[0].ends_with('0'), "{}", lines[0]);
    assert!(lines[2].find("HIGH") < lines[2].find("DATA"));
    Ok(())
}

#[test]
fn vector_config_scales_pixels() -> Result<(), &'static str> {
    let source = "---\nconfig:\n  packet:\n    bitWidth: 10\n    bitsPerRow: 8\n    rowHeight: 20\n    paddingX: 2\n    paddingY: 4\n---\npacket\n0-3: \"a\"\n";
    let scene = scene_of(source, Profile::Vector)?;
    assert_eq!(scene.canvas().w, 8 * 10 * 64 + 128);
    assert_eq!(scene.canvas().h, 2560 + 1280);
    assert_eq!(
        scene.boxes()[0].rect,
        Rect {
            x: 64,
            y: (4 + 16) * 64,
            w: (4 * 10 - 2) * 64,
            h: 20 * 64
        }
    );
    let cell = scene_of(source, Profile::Cell)?;
    assert_eq!(
        cell.canvas().w,
        16,
        "pixel keys are ignored by the cell profile"
    );
    Ok(())
}

#[test]
fn title_forms_the_last_band() -> Result<(), &'static str> {
    for profile in PROFILES {
        let scene = scene_of("packet\ntitle Hello\n0-7: \"a\"\n", profile)?;
        let (title, field) = (&scene.boxes()[0], &scene.boxes()[1]);
        assert_eq!(title.id, "title");
        assert!(title.rect.y >= field.rect.y + field.rect.h);
        assert_eq!(scene.canvas().h, title.rect.y + title.rect.h);
        let group = &scene.items()[0];
        assert_eq!(group.owner, "title");
        assert_eq!(group.items.len(), 1);
        let Item::Text(text) = &group.items[0] else {
            return Err("title draws text");
        };
        assert_eq!(text.role, TextRole::Title);
    }
    Ok(())
}

#[test]
fn scene_items() -> Result<(), &'static str> {
    let scene = scene_of("packet\n0-7: \"a\"\n8: \"b\"\n", Profile::Vector)?;
    assert_eq!(scene.items().len(), 2);
    let first = &scene.items()[0].items;
    assert_eq!(first.len(), 4);
    assert!(matches!(first[0], Item::Rect(_)));
    let texts: Vec<(TextStyle, Align)> = first[1..]
        .iter()
        .filter_map(|item| match item {
            Item::Text(text) => Some((text.style, text.align)),
            _ => None,
        })
        .collect();
    assert_eq!(
        texts,
        vec![
            (TextStyle::Text, Align::Middle),
            (TextStyle::TextMuted, Align::Start),
            (TextStyle::TextMuted, Align::End),
        ]
    );
    let single = &scene.items()[1].items;
    assert_eq!(single.len(), 3);
    let Item::Text(last) = &single[2] else {
        return Err("single bit draws text");
    };
    assert_eq!(last.align, Align::Middle);
    Ok(())
}

#[test]
fn bit_numbers_sit_above_their_row() -> Result<(), &'static str> {
    for profile in PROFILES {
        let scene = scene_of("packet\n0-15: \"a\"\n16-31: \"b\"\n32: \"c\"\n", profile)?;
        for label in scene.labels() {
            let owner = scene
                .boxes()
                .iter()
                .find(|b| b.id == label.owner)
                .ok_or("owner exists")?;
            assert_eq!(owner.rect.y, label.rect.y + label.rect.h, "{}", label.id);
        }
    }
    Ok(())
}

#[test]
fn limits() -> Result<(), &'static str> {
    let mut input = input_of("packet\n0-7: \"a\"\n", Profile::Cell)?;
    input.options.limits = Limits {
        max_nodes: 1,
        max_edges: 1,
        max_text_bytes: 1 << 20,
    };
    input.boxes.push(InputBox {
        icon: false,
        id: "f1".into(),
        role: BoxRole::Node,
        shape: "field;start=8;end=8".into(),
        parent: String::new(),
        exclusive: true,
        text: "f1".into(),
        direction: String::new(),
    });
    assert!(matches!(
        layout(&input),
        Err(RenderError::TooLarge { limit: 1, .. })
    ));
    input.options.limits.max_nodes = 10;
    input.options.limits.max_text_bytes = 2;
    assert!(matches!(
        layout(&input),
        Err(RenderError::TooLarge { limit: 2, .. })
    ));
    Ok(())
}

#[test]
fn rejects_foreign_input() -> Result<(), &'static str> {
    let good = input_of("packet\n0-7: \"a\"\n", Profile::Cell)?;
    type Edit = fn(&mut Input);
    let edits: Vec<(&str, Edit)> = vec![
        ("unknown shape", |i| i.boxes[0].shape = "circle".into()),
        ("bad range", |i| {
            i.boxes[0].shape = "field;start=x;end=3".into()
        }),
        ("missing field", |i| {
            i.boxes[0].shape = "field;start=0".into()
        }),
        ("group box", |i| i.boxes[0].role = BoxRole::Group),
        ("stray label", |i| {
            i.labels.push(InputLabel {
                id: "f0.other".into(),
                owner: "f0".into(),
                role: TextRole::Body,
                text: "x".into(),
            });
        }),
        ("unknown owner", |i| {
            i.labels.push(InputLabel {
                id: "g.lead".into(),
                owner: "g".into(),
                role: TextRole::Body,
                text: "x".into(),
            });
        }),
        ("reversed range", |i| {
            i.boxes[0].shape = "field;start=5;end=3".into()
        }),
    ];
    for (name, edit) in edits {
        let mut input = good.clone();
        edit(&mut input);
        assert!(layout(&input).is_err(), "{name}");
    }
    Ok(())
}

#[test]
fn shapeless_boxes_continue_the_bits() -> Result<(), &'static str> {
    let mut input = input_of("packet\n", Profile::Cell)?;
    for id in ["a", "b"] {
        input.boxes.push(InputBox {
            icon: false,
            id: id.into(),
            role: BoxRole::Node,
            shape: String::new(),
            parent: String::new(),
            exclusive: true,
            text: String::new(),
            direction: String::new(),
        });
    }
    let (scene, _) = layout(&input).map_err(|_| "layout failed")?;
    assert!(scene.boxes()[0].rect.x < scene.boxes()[1].rect.x);
    Ok(())
}

#[test]
fn empty_document() -> Result<(), &'static str> {
    for profile in PROFILES {
        let scene = scene_of("packet\n", profile)?;
        assert!(scene.boxes().is_empty());
        assert!(scene.items().is_empty());
    }
    Ok(())
}

#[test]
fn split_fields_repeat_their_label() -> Result<(), &'static str> {
    let scene = scene_of("packet\n0-63: \"wide\"\n", Profile::Cell)?;
    assert_eq!(scene.items().len(), 2);
    for group in scene.items() {
        let found = group.items.iter().any(|item| match item {
            Item::Text(text) => {
                text.style == TextStyle::Text
                    && text
                        .lines
                        .first()
                        .and_then(|line| line.first())
                        .map(|run| run.text.as_str())
                        == Some("wide")
            }
            _ => false,
        });
        assert!(found, "{}", group.owner);
    }
    Ok(())
}

#[test]
fn corpus_text_contains_every_label() -> Result<(), String> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../corpus/packet/mermaid/packet~0002.mmd");
    let source = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
    let scene = scene_of(&source, Profile::Cell).map_err(String::from)?;
    let text = rendered(&scene, Charset::Unicode).map_err(String::from)?;
    for want in [
        "Source Port",
        "Destination Port",
        "Length",
        "Checksum",
        "Data (variable length)",
        "UDP Packet",
    ] {
        assert!(text.contains(want), "{want}");
    }
    Ok(())
}
