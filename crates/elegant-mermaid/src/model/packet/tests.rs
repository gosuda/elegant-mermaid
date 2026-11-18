use super::{ConfigEntry, ConfigSetting, DEFAULT_BITS_PER_ROW, MAX_WORDS, Model, resolve};
use crate::diag::Diagnostic;
use crate::source::Span;
use crate::syntax::packet::parse;
use crate::syntax::preprocess::preprocess;

fn resolved(source: &str) -> (Model, Vec<Diagnostic>) {
    let removed = preprocess(source).removed;
    let parsed = parse(source, &removed);
    resolve(source, &parsed.document)
}

fn messages(diagnostics: &[Diagnostic]) -> Vec<String> {
    diagnostics
        .iter()
        .map(|d| format!("{}: {}", d.code, d.message))
        .collect()
}

fn spans(model: &Model) -> Vec<(usize, i64, i64)> {
    model
        .pieces
        .iter()
        .map(|p| (p.row, p.start, p.end))
        .collect()
}

#[test]
fn default_bits_per_row_matches_the_constant() {
    let found: Vec<i32> = crate::r#gen::layoutconst::LAYOUT_CONST
        .iter()
        .filter(|row| {
            row.name == "vector.packet.bits_per_row" || row.name == "cell.packet.bits_per_row"
        })
        .map(|row| row.value)
        .collect();
    assert_eq!(found, vec![32, 32]);
    assert_eq!(i64::from(found[0]), DEFAULT_BITS_PER_ROW);
}

#[test]
fn field_forms() {
    let (model, diagnostics) = resolved("packet\n0-3: \"a\"\n4: \"b\"\n+4: \"c\"\n9-15: \"d\"\n");
    assert!(diagnostics.is_empty());
    assert_eq!(model.fields.len(), 4);
    for (i, (start, end, bits)) in [(0, 3, 4), (4, 4, 1), (5, 8, 4), (9, 15, 7)]
        .into_iter()
        .enumerate()
    {
        let field = &model.fields[i];
        assert_eq!(field.index, i);
        assert_eq!(
            (field.start, field.end, field.bits),
            (start, end, bits),
            "{i}"
        );
    }
    let first = &model.fields[0];
    assert!(first.has_start && first.has_end && !first.has_bits);
    let third = &model.fields[2];
    assert!(!third.has_start && third.has_bits);
    assert_eq!(third.label, "c");
    assert_eq!(third.span, Span { start: 23, end: 30 });
    assert_eq!(third.bits_span, Span { start: 24, end: 25 });
}

#[test]
fn equal_endpoints_are_accepted() {
    let (model, diagnostics) = resolved("packet\n0-0: \"a\"\n1-1: \"b\"");
    assert!(diagnostics.is_empty());
    assert_eq!(model.fields[0].bits, 1);
}

#[test]
fn rejections() {
    for (source, want, span) in [
        (
            "packet\n0-3: \"a\"\n8-4: \"b\"",
            "packet/range-reversed: Packet block 8 - 4 is invalid. End must be greater than start.",
            Span { start: 16, end: 19 },
        ),
        (
            "packet\n0-3: \"a\"\n5-6: \"b\"",
            "packet/non-contiguous: Packet block 5 - 6 is not contiguous. It should start from 4.",
            Span { start: 16, end: 17 },
        ),
        (
            "packet\n0-3: \"a\"\n5: \"b\"",
            "packet/non-contiguous: Packet block 5 - 5 is not contiguous. It should start from 4.",
            Span { start: 16, end: 17 },
        ),
        (
            "packet\n1-3: \"a\"",
            "packet/non-contiguous: Packet block 1 - 3 is not contiguous. It should start from 0.",
            Span { start: 7, end: 8 },
        ),
        (
            "packet\n0-3: \"a\"\n+0: \"b\"",
            "packet/zero-bit-field: Packet block 4 is invalid. Cannot have a zero bit field.",
            Span { start: 17, end: 18 },
        ),
        (
            "packet\n3-1: \"a\"",
            "packet/range-reversed: Packet block 3 - 1 is invalid. End must be greater than start.",
            Span { start: 7, end: 10 },
        ),
    ] {
        let (model, diagnostics) = resolved(source);
        assert_eq!(messages(&diagnostics), vec![want], "{source}");
        assert_eq!(diagnostics[0].span, span, "{source}");
        assert!(model.pieces.is_empty(), "{source}");
    }
}

#[test]
fn only_the_first_failure_is_reported() {
    let (_, diagnostics) = resolved("packet\n0-3: \"a\"\n9-4: \"b\"\n20: \"c\"\n+0: \"d\"");
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, "packet/range-reversed");
}

#[test]
fn split_rows() {
    let (model, diagnostics) =
        resolved("packet\n0-15: \"a\"\n16-47: \"b\"\n48-63: \"c\"\n64: \"d\"");
    assert!(diagnostics.is_empty());
    assert_eq!(
        spans(&model),
        vec![
            (0, 0, 15),
            (0, 16, 31),
            (1, 32, 47),
            (1, 48, 63),
            (2, 64, 64)
        ]
    );
    assert_eq!(model.rows, 3);
    let labels: Vec<&str> = model.pieces.iter().map(|p| p.label.as_str()).collect();
    assert_eq!(labels, vec!["a", "b", "b", "c", "d"]);
    assert_eq!(model.pieces[1].field, 1);
    assert_eq!(model.pieces[2].field, 1);
}

#[test]
fn split_stores_the_adapter_bit_counts() {
    let (model, diagnostics) = resolved("packet\n0-63: \"wide\"\n64-71: \"tail\"");
    assert!(diagnostics.is_empty());
    let bits: Vec<i64> = model.pieces.iter().map(|p| p.bits).collect();
    assert_eq!(bits, vec![31, 31, 8]);
    assert_eq!(model.fields[0].bits, 64);
    assert_eq!(model.fields[0].end, 63);
}

#[test]
fn split_across_many_rows() {
    let head = "---\nconfig:\n  packet:\n    bitsPerRow: 8\n---\npacket\n";
    let (_, diagnostics) = resolved(&format!("{head}3-26: \"x\""));
    assert!(!diagnostics.is_empty());
    let (model, diagnostics) = resolved(&format!("{head}0-26: \"x\""));
    assert!(diagnostics.is_empty());
    assert_eq!(
        spans(&model),
        vec![(0, 0, 7), (1, 8, 15), (2, 16, 23), (3, 24, 26)]
    );
}

#[test]
fn word_cap_stops_silently() {
    let source =
        "---\nconfig:\n  packet:\n    bitsPerRow: 1\n---\npacket\n0-20000: \"x\"\n20001: \"y\"";
    let (model, diagnostics) = resolved(source);
    assert!(diagnostics.is_empty());
    assert_eq!(model.rows, MAX_WORDS);
    assert_eq!(model.pieces.len(), MAX_WORDS);
    let last = i64::try_from(MAX_WORDS).unwrap() - 1;
    assert_eq!(model.pieces[MAX_WORDS - 1].end, last);
}

#[test]
fn metadata_last_value_wins() {
    let source =
        "packet\ntitle first\naccTitle: a\naccDescr: d\ntitle second\naccTitle:\ntitle\n0: \"x\"";
    let (model, diagnostics) = resolved(source);
    assert!(diagnostics.is_empty());
    assert_eq!(model.title, "");
    assert_eq!(model.acc_title, "");
    assert_eq!(model.acc_descr, "d");
}

#[test]
fn config_sources() {
    let source = "---\nconfig:\n  packet:\n    showBits: false\n    bitOrder: descending\n    bitsPerRow: 16\n    bitWidth: 20\n    paddingX: 0\n    rowHeight: 40\n    paddingY: 2\n---\n%%{init: {'packet': {'bitsPerRow': 8, 'showBits': true}}}%%\npacket\n0-3: \"x\"";
    let (model, diagnostics) = resolved(source);
    assert!(diagnostics.is_empty());
    assert_eq!(model.bits_per_row, 8);
    assert!(model.show_bits);
    assert!(model.descending);
    let keys: Vec<&str> = model.config.iter().map(|e| e.key).collect();
    assert_eq!(
        keys,
        vec![
            "bitOrder",
            "bitWidth",
            "bitsPerRow",
            "paddingX",
            "paddingY",
            "rowHeight",
            "showBits"
        ]
    );
    assert_eq!(
        model.config[2],
        ConfigEntry {
            key: "bitsPerRow",
            setting: ConfigSetting::Integer(8)
        }
    );
    assert_eq!(
        model.config[6],
        ConfigEntry {
            key: "showBits",
            setting: ConfigSetting::Bool(true)
        }
    );
    assert_eq!(
        model.config[0],
        ConfigEntry {
            key: "bitOrder",
            setting: ConfigSetting::Text("descending".into())
        }
    );
}

#[test]
fn config_ranges_and_types() {
    let source = "---\nconfig:\n  packet:\n    bitsPerRow: 0\n    bitWidth: 2000\n    rowHeight: 1.5\n    paddingX: -1\n    showBits: yes\n    bitOrder: sideways\n    paddingY: 1024\n---\npacket\n0: \"x\"";
    let (model, diagnostics) = resolved(source);
    assert!(diagnostics.is_empty());
    assert_eq!(
        model.config,
        vec![ConfigEntry {
            key: "paddingY",
            setting: ConfigSetting::Integer(1024)
        }]
    );
    assert_eq!(model.bits_per_row, DEFAULT_BITS_PER_ROW);
}

#[test]
fn empty_document() {
    let (model, diagnostics) = resolved("packet");
    assert!(diagnostics.is_empty());
    assert!(model.fields.is_empty());
    assert_eq!(model.rows, 0);
    assert!(model.show_bits);
}
