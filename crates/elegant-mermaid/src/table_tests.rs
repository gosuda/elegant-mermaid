use crate::r#gen::{markers::MARKERS, shapes::SHAPES};

const UPSTREAM_SHAPE_NAMES: &[&str] = &[
    "rect",
    "proc",
    "process",
    "rectangle",
    "squareRect",
    "rounded",
    "event",
    "roundedRect",
    "stadium",
    "terminal",
    "pill",
    "fr-rect",
    "subprocess",
    "subproc",
    "framed-rectangle",
    "subroutine",
    "cyl",
    "db",
    "database",
    "cylinder",
    "datastore",
    "data-store",
    "folder",
    "directory",
    "bucket",
    "console",
    "browser",
    "person",
    "circle",
    "circ",
    "bang",
    "cloud",
    "diam",
    "decision",
    "diamond",
    "question",
    "hex",
    "hexagon",
    "prepare",
    "lean-r",
    "lean-right",
    "in-out",
    "lean_right",
    "lean-l",
    "lean-left",
    "out-in",
    "lean_left",
    "trap-b",
    "priority",
    "trapezoid-bottom",
    "trapezoid",
    "trap-t",
    "manual",
    "trapezoid-top",
    "inv-trapezoid",
    "inv_trapezoid",
    "dbl-circ",
    "double-circle",
    "doublecircle",
    "text",
    "notch-rect",
    "card",
    "notched-rectangle",
    "lin-rect",
    "lined-rectangle",
    "lined-process",
    "lin-proc",
    "shaded-process",
    "sm-circ",
    "start",
    "small-circle",
    "stateStart",
    "fr-circ",
    "stop",
    "framed-circle",
    "stateEnd",
    "fork",
    "join",
    "forkJoin",
    "hourglass",
    "collate",
    "brace",
    "comment",
    "brace-l",
    "brace-r",
    "braces",
    "bolt",
    "com-link",
    "lightning-bolt",
    "doc",
    "document",
    "delay",
    "half-rounded-rectangle",
    "h-cyl",
    "das",
    "horizontal-cylinder",
    "lin-cyl",
    "disk",
    "lined-cylinder",
    "curv-trap",
    "curved-trapezoid",
    "display",
    "div-rect",
    "div-proc",
    "divided-rectangle",
    "divided-process",
    "tri",
    "extract",
    "triangle",
    "win-pane",
    "internal-storage",
    "window-pane",
    "f-circ",
    "junction",
    "filled-circle",
    "notch-pent",
    "loop-limit",
    "notched-pentagon",
    "flip-tri",
    "manual-file",
    "flipped-triangle",
    "sl-rect",
    "manual-input",
    "sloped-rectangle",
    "docs",
    "documents",
    "st-doc",
    "stacked-document",
    "st-rect",
    "procs",
    "processes",
    "stacked-rectangle",
    "bow-rect",
    "stored-data",
    "bow-tie-rectangle",
    "cross-circ",
    "summary",
    "crossed-circle",
    "tag-doc",
    "tagged-document",
    "tag-rect",
    "tagged-rectangle",
    "tag-proc",
    "tagged-process",
    "flag",
    "paper-tape",
    "odd",
    "rect_left_inv_arrow",
    "lin-doc",
    "lined-document",
];

#[test]
fn shape_short_names() {
    assert_eq!(UPSTREAM_SHAPE_NAMES.len(), 150);
    let unresolved: Vec<_> = UPSTREAM_SHAPE_NAMES
        .iter()
        .filter(|name| {
            !SHAPES
                .iter()
                .any(|shape| shape.id == **name || shape.aliases.contains(name))
        })
        .collect();
    assert!(
        unresolved.is_empty(),
        "names without a row in spec/data/shapes.json: {unresolved:?}"
    );
    let mut ids: Vec<_> = SHAPES.iter().map(|shape| shape.id).collect();
    ids.sort_unstable();
    ids.dedup();
    assert_eq!(ids.len(), SHAPES.len(), "shape ids are unique");
    let mut owners = std::collections::BTreeMap::new();
    for shape in SHAPES {
        for name in std::iter::once(&shape.id).chain(shape.aliases) {
            if let Some(previous) = owners.insert(*name, shape.id) {
                assert_eq!(previous, shape.id, "{name} names two shapes");
            }
        }
    }
}

#[test]
fn marker_kinds() {
    assert_eq!(MARKERS.len(), 32, "25 upstream kinds and 7 sequence heads");
    for marker in MARKERS {
        assert!(
            matches!(marker.paint, "filled" | "hollow" | "open"),
            "{} paint {:?}",
            marker.name,
            marker.paint
        );
        assert_eq!(marker.cell.len(), 4, "{} cell glyphs", marker.name);
        assert_eq!(marker.ascii.len(), 4, "{} ascii glyphs", marker.name);
        assert!(
            marker
                .cell
                .iter()
                .chain(marker.ascii)
                .all(|glyph| char::from_u32(*glyph).is_some_and(|c| !c.is_control())),
            "{} glyphs are printable",
            marker.name
        );
        assert!(
            marker.points.len() >= 2,
            "{} needs at least two points, has {}",
            marker.name,
            marker.points.len()
        );
        assert!(
            marker
                .breaks
                .iter()
                .all(|b| { usize::try_from(*b).is_ok_and(|b| b > 0 && b < marker.points.len()) }),
            "{} contour breaks lie inside its points",
            marker.name
        );
        let (x, y) = marker.anchor;
        let xs = marker.points.iter().map(|p| p.0);
        let ys = marker.points.iter().map(|p| p.1);
        assert!(
            xs.clone().min() <= Some(x) && Some(x) <= xs.max(),
            "{} anchor x {x} lies in its outline",
            marker.name
        );
        assert!(
            ys.clone().min() <= Some(y) && Some(y) <= ys.max(),
            "{} anchor y {y} lies in its outline",
            marker.name
        );
    }
}
