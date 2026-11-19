use std::collections::BTreeMap;

use super::{Model, Orientation, resolve, thousandths};
use crate::scene::DumpValue;
use crate::syntax::preprocess::preprocess;
use crate::syntax::xychart::parse;

fn model(text: &str) -> Model {
    let removed = preprocess(text).removed;
    let parsed = parse(text, &removed);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let (model, diagnostics) = resolve(text, &parsed.document);
    assert!(diagnostics.is_empty());
    model
}

#[test]
fn thousandths_rounds_half_away_from_zero() {
    let cases = [
        ("1", 1000),
        ("0.0005", 1),
        ("0.0004", 0),
        ("-0.0005", -1),
        ("2.5", 2500),
        ("-2.5", -2500),
        (".5", 500),
        ("+3", 3000),
        ("0.1239", 124),
        ("10", 10000),
        ("007", 7000),
    ];
    for (literal, want) in cases {
        assert_eq!(thousandths(literal), want, "{literal}");
    }
}

#[test]
fn thousandths_caps_huge_values_above_int32() {
    assert!(thousandths("99999999999999999999999") > i64::from(i32::MAX));
    assert!(thousandths("-99999999999999999999999") < -i64::from(i32::MAX));
}

#[test]
fn first_plot_without_x_axis_fixes_a_linear_domain() {
    let m = model("xychart\nbar [3, 1, 2]\nline [9, 9, 9, 9, 9]\n");
    assert!(!m.x.band);
    assert_eq!((m.x.min, m.x.max), (1000, 3000));
    assert_eq!((m.y.min, m.y.max), (1000, 9000));
    assert_eq!(m.plots[1].points.len(), 5);
    let xs: Vec<i64> = m.plots[0].points.iter().map(|p| p.x).collect();
    assert_eq!(xs, [1000, 2000, 3000]);
}

#[test]
fn linear_axis_spreads_points_evenly() {
    let m = model("xychart\nx-axis 0 --> 10\nline [1, 2, 3]\n");
    assert!(m.plots[0].points.iter().all(|p| p.has_x));
    let xs: Vec<i64> = m.plots[0].points.iter().map(|p| p.x).collect();
    assert_eq!(xs, [0, 5000, 10000]);
}

#[test]
fn single_value_sits_at_the_domain_minimum() {
    let m = model("xychart\nx-axis 4 --> 8\nline [1]\n");
    assert_eq!(m.plots[0].points[0].x, 4000);
}

#[test]
fn band_plot_truncates_excess_and_keeps_missing_values_absent() {
    let m = model("xychart\nx-axis [a, b, c]\nbar [1, 2, 3, 40]\nbar [5]\n");
    assert_eq!(m.y.max, 5000);
    assert_eq!(m.plots[0].points.len(), 3);
    let short = &m.plots[1].points;
    assert_eq!(short.len(), 3);
    assert_eq!(
        short.iter().map(|p| p.present).collect::<Vec<_>>(),
        [true, false, false]
    );
    assert_eq!(m.y.min, 1000);
}

#[test]
fn explicit_y_range_stops_inference() {
    let m = model("xychart\nx-axis [a]\nbar [100]\ny-axis 0 --> 10\nbar [200]\n");
    assert_eq!((m.y.min, m.y.max), (0, 10000));
}

#[test]
fn title_only_axis_keeps_inference() {
    let m = model("xychart\nx-axis \"Months\"\ny-axis Units\nbar [4, 8]\n");
    assert_eq!(m.x.title, "Months");
    assert_eq!(m.y.title, "Units");
    assert_eq!((m.y.min, m.y.max), (4000, 8000));
    assert!(!m.x.band);
}

#[test]
fn axis_data_without_title_clears_the_title() {
    let m = model("xychart\nx-axis Months\nx-axis [a, b]\n");
    assert_eq!(m.x.title, "");
    assert!(m.x.band);
}

#[test]
fn duplicate_categories_use_the_first_slot() {
    let m = model("xychart\nx-axis [a, b, a]\nbar [1, 2, 3]\n");
    let slots: Vec<Option<usize>> = m.plots[0].points.iter().map(|p| p.slot).collect();
    assert_eq!(slots, [Some(0), Some(1), Some(0)]);
}

#[test]
fn redefined_axis_leaves_earlier_plots_unplaced() {
    let m = model("xychart\nx-axis [a, b]\nbar [1, 2]\nx-axis 0 --> 5\n");
    for point in &m.plots[0].points {
        assert_eq!(point.slot, None);
        assert!(!point.has_x);
    }
}

#[test]
fn only_line_plots_keep_point_labels() {
    let m = model("xychart\nx-axis [a, b]\nline [1 \"x\", 2]\nbar [1 \"y\", 2]\n");
    assert_eq!(m.plots[0].points[0].label, "x");
    assert_eq!(m.plots[1].points[0].label, "");
}

#[test]
fn header_orientation_overrides_config() {
    let config = "---\nconfig:\n  xyChart:\n    chartOrientation: horizontal\n---\n";
    let m = model(&format!("{config}xychart\nbar [1]\n"));
    assert_eq!(m.orientation, Orientation::Horizontal);
    let m = model(&format!("{config}xychart vertical\nbar [1]\n"));
    assert_eq!(m.orientation, Orientation::Vertical);
    let m = model("xychart HORIZONTAL\nbar [1]\n");
    assert_eq!(m.orientation, Orientation::Vertical);
}

#[test]
fn titles_and_accessibility_are_trimmed_and_replaced() {
    let m = model(
        "xychart\ntitle \"  First  \"\ntitle Second\naccTitle:  T1 \naccDescr: D1\naccDescr {\n D2 \n}\nbar [1]\n",
    );
    assert_eq!(m.title, "Second");
    assert_eq!(m.acc_title, "T1");
    assert_eq!(m.acc_descr, "D2");
}

#[test]
fn frontmatter_title_is_the_diagram_title() {
    let m = model("---\ntitle: From front\n---\nxychart\nbar [1]\n");
    assert_eq!(m.title, "From front");
}

#[test]
fn honoured_config_keys_are_kept_sorted_and_range_checked() {
    let m = model(
        "---\nconfig:\n  xyChart:\n    width: 900\n    height: 0\n    unknownKey: 0\n    plotReservedSpacePercent: 60\n    showTitle: false\n    xAxis:\n      showLabel: false\n      labelFontSize: 20\n---\nxychart\nbar [1]\n",
    );
    let want: BTreeMap<String, DumpValue> = [
        ("plotReservedSpacePercent", DumpValue::Integer(60)),
        ("width", DumpValue::Integer(900)),
        ("xAxis.labelFontSize", DumpValue::Integer(20)),
        ("xAxis.showLabel", DumpValue::Bool(false)),
    ]
    .into_iter()
    .map(|(key, value)| (key.to_owned(), value))
    .collect();
    assert_eq!(m.config, want);
}

#[test]
fn entities_decode_in_text() {
    let m = model("xychart\ntitle \"a #35; b #amp; c\"\nbar [1]\n");
    assert_eq!(m.title, "a # b & c");
}
