use super::{AUTO_COLUMNS, Block, ConfigEntry, MAX_SPACE_SLOTS, Model, resolve};
use crate::diag::{Diagnostic, Severity};
use crate::syntax::block::parse;
use crate::syntax::preprocess::preprocess;

fn resolved(source: &str) -> (Model, Vec<Diagnostic>) {
    let removed = preprocess(source).removed;
    let parsed = parse(source, &removed);
    resolve(source, &parsed.document)
}

fn ids(blocks: &[Block]) -> Vec<&str> {
    blocks.iter().map(|block| block.id.as_str()).collect()
}

fn codes(diagnostics: &[Diagnostic]) -> Vec<&'static str> {
    diagnostics.iter().map(|d| d.code).collect()
}

fn found<'m>(model: &'m Model, id: &str) -> Result<&'m Block, String> {
    model.find(id).ok_or_else(|| format!("no block {id}"))
}

fn child(model: &Model, at: usize) -> Result<&Block, &'static str> {
    model.root.children.get(at).ok_or("missing child")
}

#[test]
fn columns_and_spans() -> Result<(), &'static str> {
    let (model, diagnostics) = resolved("block-beta\ncolumns 3\nA B:2 C\n");
    assert!(diagnostics.is_empty());
    assert_eq!(model.root.columns, 3);
    assert_eq!(ids(&model.root.children), ["A", "B", "C"]);
    let spans = [
        child(&model, 0)?.span,
        child(&model, 1)?.span,
        child(&model, 2)?.span,
    ];
    assert_eq!(spans, [1, 2, 1]);
    Ok(())
}

#[test]
fn root_columns_default_to_auto() {
    let (model, _) = resolved("block-beta\nA\n");
    assert_eq!(model.root.columns, AUTO_COLUMNS);
}

#[test]
fn space_expands_into_slots() -> Result<(), &'static str> {
    let (model, diagnostics) = resolved("block-beta\nspace:3\nA\nspace\n");
    assert!(diagnostics.is_empty());
    assert_eq!(
        ids(&model.root.children),
        ["space0-0", "space0-1", "space0-2", "A", "space1-0"]
    );
    for at in [0, 1, 2, 4] {
        assert_eq!(child(&model, at)?.kind, "space");
    }
    Ok(())
}

#[test]
fn space_slots_are_capped() -> Result<(), &'static str> {
    let (model, _) = resolved("block-beta\nspace:99999999999\nspace:5\nA\n");
    let cap = usize::try_from(MAX_SPACE_SLOTS).map_err(|_| "cap")?;
    assert_eq!(model.root.children.len(), cap + 1);
    assert_eq!(child(&model, cap - 1)?.kind, "space");
    assert_eq!(child(&model, cap)?.id, "A");
    Ok(())
}

#[test]
fn composite_blocks() -> Result<(), &'static str> {
    let (model, diagnostics) =
        resolved("block-beta\nblock:outer\ncolumns 2\nx y\nend\nblock\nz\nend\n");
    assert!(diagnostics.is_empty());
    let (outer, anonymous) = (child(&model, 0)?, child(&model, 1)?);
    assert_eq!(outer.kind, "composite");
    assert_eq!(outer.id, "outer");
    assert_eq!(outer.columns, 2);
    assert_eq!(ids(&outer.children), ["x", "y"]);
    assert_eq!(anonymous.id, "block0");
    assert_eq!(ids(&anonymous.children), ["z"]);
    Ok(())
}

#[test]
fn generated_ids_avoid_explicit_ones() -> Result<(), &'static str> {
    let (model, _) = resolved("block-beta\nblock0\nblock\nz\nend\nroot0\n");
    assert_eq!(model.root.id, "root0~1");
    assert_eq!(child(&model, 1)?.id, "block0~1");
    Ok(())
}

#[test]
fn shapes_and_directions() -> Result<(), String> {
    let source = "block-beta\na[\"s\"] b(\"r\") c((\"c\")) d{\"d\"} e{{\"h\"}} f([\"t\"]) g[[\"u\"]] h[(\"y\")] i(((\"o\"))) j>\"k\"] k[/\"p\"/] l[\\\"q\"\\] m[/\"w\"\\] n[\\\"v\"/] o<[\"arr\"]>(right, down)\nplain\n";
    let (model, diagnostics) = resolved(source);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    let kinds: Vec<&str> = model
        .root
        .children
        .iter()
        .map(|b| b.kind.as_str())
        .collect();
    assert_eq!(
        kinds,
        [
            "square",
            "round",
            "circle",
            "diamond",
            "hexagon",
            "stadium",
            "subroutine",
            "cylinder",
            "doublecircle",
            "rect_left_inv_arrow",
            "lean_right",
            "lean_left",
            "trapezoid",
            "inv_trapezoid",
            "block_arrow",
            "na"
        ]
    );
    assert_eq!(found(&model, "o")?.directions, ["right", "down"]);
    assert_eq!(found(&model, "o")?.label, "arr");
    assert_eq!(found(&model, "plain")?.label, "plain");
    Ok(())
}

#[test]
fn edge_styles() {
    let (model, diagnostics) = resolved(
        "block-beta\nA --> B\nB --- C\nC ==> D\nD -.-> E\nE --x F\nA -- \"t\" --> C\nG <--> H\n",
    );
    assert!(diagnostics.is_empty());
    let got: Vec<[&str; 5]> = model
        .edges
        .iter()
        .map(|e| {
            [
                e.thickness.as_str(),
                e.pattern.as_str(),
                e.arrow_start.as_str(),
                e.arrow_end.as_str(),
                e.label.as_str(),
            ]
        })
        .collect();
    assert_eq!(
        got,
        [
            ["normal", "solid", "arrow_open", "arrow_point", ""],
            ["normal", "solid", "arrow_open", "", ""],
            ["thick", "solid", "arrow_open", "arrow_point", ""],
            ["normal", "dotted", "arrow_open", "arrow_point", ""],
            ["normal", "solid", "arrow_open", "arrow_cross", ""],
            ["normal", "solid", "arrow_open", "arrow_point", "t"],
            ["normal", "solid", "arrow_point", "arrow_point", ""],
        ]
    );
}

#[test]
fn chained_edges_link_neighbours() {
    let (model, _) = resolved("block-beta\nA --> B --> C\n");
    let pairs: Vec<(&str, &str)> = model
        .edges
        .iter()
        .map(|e| (e.start.as_str(), e.end.as_str()))
        .collect();
    assert_eq!(pairs, [("A", "B"), ("B", "C")]);
}

#[test]
fn edge_to_composite_keeps_the_edge() {
    let (model, _) = resolved("block-beta\nblock:g\nx\nend\nA --> g\n");
    assert_eq!(model.edges.len(), 1);
    assert_eq!(model.edges[0].end, "g");
}

#[test]
fn label_entities_are_decoded() -> Result<(), String> {
    let (model, _) = resolved("block-beta\nA[\"a #amp; b #35; #nope; #0;\"]\n");
    assert_eq!(found(&model, "A")?.label, "a & b # #nope; #0;");
    Ok(())
}

#[test]
fn second_declaration_relabels() -> Result<(), String> {
    let (model, _) = resolved("block-beta\nA[\"one\"]\nA(\"two\")\nA\n");
    assert_eq!(model.root.children.len(), 1);
    assert_eq!(found(&model, "A")?.label, "two");
    assert_eq!(found(&model, "A")?.kind, "round");
    Ok(())
}

#[test]
fn style_target_must_exist() -> Result<(), String> {
    let (model, diagnostics) = resolved("block-beta\nA\nstyle A fill:#f00\nstyle Z fill:#0f0\n");
    assert_eq!(codes(&diagnostics), ["block/style-target-unknown"]);
    assert_eq!(found(&model, "A")?.styles, ["fill:#f00"]);
    Ok(())
}

#[test]
fn width_beyond_columns_is_reported() {
    let (_, diagnostics) = resolved("block-beta\ncolumns 2\nA:3 B:2\n");
    assert_eq!(codes(&diagnostics), ["block/width-exceeds-columns"]);
    assert!(diagnostics[0].message.contains('A'));
}

#[test]
fn class_defs_and_classes() -> Result<(), String> {
    let (model, _) = resolved("block-beta\nclassDef k fill:#fff,color:#000\nA B\nclass A,B k\n");
    assert_eq!(found(&model, "A")?.classes, ["k"]);
    assert_eq!(found(&model, "B")?.classes, ["k"]);
    assert_eq!(model.classes[0].styles, ["fill:#fff", "color:#000"]);
    assert_eq!(model.classes[0].text_styles, ["fill:#000"]);
    Ok(())
}

#[test]
fn padding_config_accepts_zero_to_the_limit() {
    let cases = [
        (
            "---\nconfig:\n  block:\n    padding: 12\n---\nblock-beta\nA\n",
            12,
        ),
        (
            "%%{init: {\"block\": {\"padding\": 3}}}%%\nblock-beta\nA\n",
            3,
        ),
    ];
    for (source, want) in cases {
        let (model, _) = resolved(source);
        let entry = ConfigEntry {
            key: "padding".into(),
            value: want,
        };
        assert_eq!(model.config, [entry], "{source}");
    }
}

#[test]
fn padding_config_rejects_out_of_range_values() {
    for source in [
        "---\nconfig:\n  block:\n    padding: 5000\n---\nblock-beta\nA\n",
        "---\nconfig:\n  block:\n    padding: -1\n---\nblock-beta\nA\n",
        "---\nconfig:\n  block:\n    padding: x\n---\nblock-beta\nA\n",
    ] {
        let (model, _) = resolved(source);
        assert!(model.config.is_empty(), "{source}");
    }
}

#[test]
fn class_statement_on_an_undeclared_id_leaves_the_block_off_the_tree() {
    let (model, _) = resolved("block-beta\nclass X k\nA\n");
    assert_eq!(ids(&model.root.children), ["A"]);
    assert!(model.find("X").is_none());
}

#[test]
fn corpus_accepted_resolves_without_errors() -> Result<(), String> {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/block");
    let mut checked = 0usize;
    for dir in std::fs::read_dir(&root).map_err(|e| e.to_string())? {
        for entry in
            std::fs::read_dir(dir.map_err(|e| e.to_string())?.path()).map_err(|e| e.to_string())?
        {
            let path = entry.map_err(|e| e.to_string())?.path();
            let source = std::fs::read_to_string(&path).map_err(|e| e.to_string())?;
            let (_, diagnostics) = resolved(&source);
            if let Some(d) = diagnostics.iter().find(|d| d.severity == Severity::Error) {
                return Err(format!("{}: {}: {}", path.display(), d.code, d.message));
            }
            checked += 1;
        }
    }
    assert!(checked > 0, "corpus/block holds no file");
    Ok(())
}
