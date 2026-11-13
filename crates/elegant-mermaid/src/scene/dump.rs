//! The canonical layout dump and the model-stage dump writers of `spec/layout-dump.md`
//! and `spec/model-dump.md`.
//!
//! Both writers push onto a caller string and use no JSON crate, so the bytes are fixed by
//! this file alone. The integer form, the string escapes, the key order, and the places a
//! newline falls are the rules of `spec/layout-dump.md`.

use crate::diag::json::push_json_string;
use crate::geom::{Point, Rect, Size};

use super::{Direction, Dump, DumpOptions, DumpValue, Limits, SceneBox, SceneLabel, SceneRoute};

/// The stage of a dump, which selects the members that carry coordinates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Stage {
    /// The stage before measurement and layout: no canvas, no coordinates, and an empty
    /// `lines` array.
    Model,
    /// The stage after layout: the canvas, every rectangle, and every route point.
    Layout,
}

impl Stage {
    /// The stage name of the dump.
    pub const fn as_str(self) -> &'static str {
        match self {
            Stage::Model => "model",
            Stage::Layout => "layout",
        }
    }
}

/// Writes the canonical layout dump of `spec/layout-dump.md`, with one LF after the final
/// `}`.
pub fn push_layout(out: &mut String, dump: &Dump, canvas: Size) {
    push_dump(out, dump, Some(canvas), (Stage::Layout, &[]));
}

/// Writes the model-stage dump of `spec/model-dump.md`: no canvas, no coordinates, and an
/// empty `lines` array on every label.
pub fn push_model(out: &mut String, dump: &Dump, directions: &[(&str, Direction)]) {
    push_dump(out, dump, None, (Stage::Model, directions));
}

fn push_dump(
    out: &mut String,
    dump: &Dump,
    canvas: Option<Size>,
    context: (Stage, &[(&str, Direction)]),
) {
    let (stage, directions) = context;
    out.push_str("{\"version\":1,\"stage\":");
    push_json_string(out, stage.as_str());
    out.push_str(",\"kind\":");
    push_json_string(out, dump.kind);
    out.push_str(",\"profile\":");
    push_json_string(out, dump.options.profile.as_str());
    out.push_str(",\"options\":");
    push_options(out, &dump.options);
    if let Some(canvas) = canvas {
        push_canvas(out, canvas);
    }
    push_boxes(out, &dump.boxes, stage, directions);
    push_routes(out, &dump.routes, stage);
    push_labels(out, &dump.labels, stage);
    out.push_str("}\n");
}

fn push_options(out: &mut String, options: &DumpOptions) {
    out.push_str("{\"profile\":");
    push_json_string(out, options.profile.as_str());
    out.push_str(",\"thoroughness\":");
    push_int(out, i64::from(options.thoroughness));
    out.push_str(",\"max_width\":");
    push_int(out, i64::from(options.max_width));
    out.push_str(",\"direction\":");
    push_json_string(out, options.direction.as_str());
    out.push_str(",\"limits\":");
    push_limits(out, options.limits);
    for (key, value) in &options.config {
        out.push(',');
        push_json_string(out, key);
        out.push(':');
        match value {
            DumpValue::Bool(v) => out.push_str(if *v { "true" } else { "false" }),
            DumpValue::Integer(v) => push_int(out, *v),
            DumpValue::String(v) => push_json_string(out, v),
        }
    }
    out.push('}');
}

fn push_limits(out: &mut String, limits: Limits) {
    out.push_str("{\"max_nodes\":");
    push_int(out, i64::from(limits.max_nodes));
    out.push_str(",\"max_edges\":");
    push_int(out, i64::from(limits.max_edges));
    out.push_str(",\"max_text_bytes\":");
    push_int(out, i64::from(limits.max_text_bytes));
    out.push('}');
}

fn push_canvas(out: &mut String, canvas: Size) {
    out.push_str(",\"canvas\":{\"w\":");
    push_int(out, i64::from(canvas.w));
    out.push_str(",\"h\":");
    push_int(out, i64::from(canvas.h));
    out.push('}');
}

fn push_boxes(
    out: &mut String,
    boxes: &[SceneBox],
    stage: Stage,
    directions: &[(&str, Direction)],
) {
    out.push_str(",\n\"boxes\":[");
    for (index, item) in boxes.iter().enumerate() {
        if index > 0 {
            out.push_str(",\n");
        }
        out.push_str("{\"id\":");
        push_json_string(out, &item.id);
        out.push_str(",\"role\":");
        push_json_string(out, item.role.as_str());
        if stage == Stage::Layout {
            push_geometry(out, item.rect);
        }
        out.push_str(",\"parent\":");
        push_json_string(out, &item.parent);
        out.push_str(",\"exclusive\":");
        out.push_str(if item.exclusive { "true" } else { "false" });
        if stage == Stage::Model && item.role == super::BoxRole::Group {
            out.push_str(",\"direction\":");
            push_json_string(
                out,
                directions
                    .iter()
                    .find(|(id, _)| *id == item.id)
                    .map_or("", |(_, direction)| direction.as_str()),
            );
        }
        out.push('}');
    }
    out.push(']');
}

fn push_routes(out: &mut String, routes: &[SceneRoute], stage: Stage) {
    out.push_str(",\n\"routes\":[");
    for (index, item) in routes.iter().enumerate() {
        if index > 0 {
            out.push_str(",\n");
        }
        out.push_str("{\"id\":");
        push_json_string(out, &item.id);
        out.push_str(",\"from\":");
        push_json_string(out, &item.from);
        out.push_str(",\"to\":");
        push_json_string(out, &item.to);
        out.push_str(",\"orthogonal\":");
        out.push_str(if item.orthogonal { "true" } else { "false" });
        if stage == Stage::Layout {
            push_points(out, &item.points);
        } else {
            push_route_style(out, item);
        }
        out.push('}');
    }
    out.push(']');
}

fn push_route_style(out: &mut String, route: &SceneRoute) {
    if !route.marker_start.is_empty() && route.marker_start != "none" {
        out.push_str(",\"marker_start\":");
        push_json_string(out, &route.marker_start);
    }
    if !route.marker_end.is_empty() && route.marker_end != "point" {
        out.push_str(",\"marker_end\":");
        push_json_string(out, &route.marker_end);
    }
    if !route.stroke.is_empty() && route.stroke != "normal" {
        out.push_str(",\"stroke\":");
        push_json_string(out, &route.stroke);
    }
}

fn push_points(out: &mut String, points: &[Point]) {
    out.push_str(",\"points\":[");
    for (index, point) in points.iter().enumerate() {
        if index > 0 {
            out.push(',');
        }
        out.push('[');
        push_int(out, i64::from(point.x));
        out.push(',');
        push_int(out, i64::from(point.y));
        out.push(']');
    }
    out.push(']');
}

fn push_labels(out: &mut String, labels: &[SceneLabel], stage: Stage) {
    out.push_str(",\n\"labels\":[");
    for (index, item) in labels.iter().enumerate() {
        if index > 0 {
            out.push_str(",\n");
        }
        out.push_str("{\"id\":");
        push_json_string(out, &item.id);
        out.push_str(",\"owner\":");
        push_json_string(out, &item.owner);
        out.push_str(",\"text\":");
        push_json_string(out, &item.text);
        if stage == Stage::Layout {
            push_geometry(out, item.rect);
        }
        out.push_str(",\"lines\":[");
        if stage == Stage::Layout {
            push_lines(out, &item.lines);
        }
        out.push_str("]}");
    }
    out.push(']');
}

fn push_lines(out: &mut String, lines: &[String]) {
    for (index, line) in lines.iter().enumerate() {
        if index > 0 {
            out.push(',');
        }
        push_json_string(out, line);
    }
}

fn push_geometry(out: &mut String, rect: Rect) {
    out.push_str(",\"x\":");
    push_int(out, i64::from(rect.x));
    out.push_str(",\"y\":");
    push_int(out, i64::from(rect.y));
    out.push_str(",\"w\":");
    push_int(out, i64::from(rect.w));
    out.push_str(",\"h\":");
    push_int(out, i64::from(rect.h));
}

/// Writes an integer in minimal decimal: an optional `-`, then digits with no leading
/// zero, with no `+`, fraction, or exponent.
pub fn push_int(out: &mut String, value: i64) {
    if value < 0 {
        out.push('-');
    }
    let mut buffer = [0u8; 20];
    let mut cursor = buffer.len();
    let mut rest = value.unsigned_abs();
    loop {
        cursor -= 1;
        buffer[cursor] = b'0' + u8::try_from(rest % 10).unwrap_or(0);
        rest /= 10;
        if rest == 0 {
            break;
        }
    }
    for &digit in &buffer[cursor..] {
        out.push(char::from(digit));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::geom::{Point, Rect};
    use crate::scene::{BoxRole, Dump, DumpOptions, Profile, SceneBox, SceneLabel, SceneRoute};

    fn rect(x: i32, y: i32, w: i32, h: i32) -> Rect {
        Rect { x, y, w, h }
    }

    fn node(id: &str) -> SceneBox {
        SceneBox {
            id: id.to_owned(),
            role: BoxRole::Node,
            rect: rect(0, 0, 10, 10),
            parent: String::new(),
            exclusive: true,
        }
    }

    fn route() -> SceneRoute {
        SceneRoute {
            id: String::from("e0"),
            from: String::from("A"),
            to: String::from("B"),
            orthogonal: true,
            points: Vec::new(),
            marker_start: String::new(),
            marker_end: String::new(),
            stroke: String::new(),
        }
    }

    fn label(text: &str) -> SceneLabel {
        SceneLabel {
            id: String::from("e0.label"),
            owner: String::from("e0"),
            text: text.to_owned(),
            rect: rect(0, 0, 0, 0),
            lines: Vec::new(),
        }
    }

    fn two_node_model() -> Dump {
        let mut dump = Dump::new("flowchart", DumpOptions::default());
        dump.boxes.push(node("A"));
        dump.boxes.push(node("B"));
        dump.routes.push(route());
        dump.labels.push(label("yes"));
        dump
    }

    const MODEL_GOLDEN: &str = concat!(
        "{\"version\":1,\"stage\":\"model\",\"kind\":\"flowchart\",\"profile\":\"vector\",",
        "\"options\":{\"profile\":\"vector\",\"thoroughness\":3,\"max_width\":0,",
        "\"direction\":\"TB\",\"limits\":{\"max_nodes\":2000,\"max_edges\":5000,",
        "\"max_text_bytes\":1048576}},\n",
        "\"boxes\":[{\"id\":\"A\",\"role\":\"node\",\"parent\":\"\",\"exclusive\":true},\n",
        "{\"id\":\"B\",\"role\":\"node\",\"parent\":\"\",\"exclusive\":true}],\n",
        "\"routes\":[{\"id\":\"e0\",\"from\":\"A\",\"to\":\"B\",\"orthogonal\":true}],\n",
        "\"labels\":[{\"id\":\"e0.label\",\"owner\":\"e0\",\"text\":\"yes\",\"lines\":[]}]}\n",
    );

    #[test]
    fn model_dump_matches_the_golden_example_byte_for_byte() {
        assert_eq!(two_node_model().dump_model(&[]), MODEL_GOLDEN);
    }

    #[test]
    fn model_dump_never_writes_measured_lines() {
        let mut dump = two_node_model();
        if let Some(item) = dump.labels.first_mut() {
            item.lines = vec![String::from("ye"), String::from("s")];
        }
        let out = dump.dump_model(&[]);
        assert!(
            out.contains("\"text\":\"yes\",\"lines\":[]}"),
            "{}; observed: {:?}",
            "Invariant failed: out.contains(\"\\\"text\\\":\\\"yes\\\",\\\"lines\\\":[]}\")",
            out
        );
        assert!(
            !out.contains("\"lines\":[\"ye\""),
            "{}; observed: {:?}",
            "Invariant failed: !out.contains(\"\\\"lines\\\":[\\\"ye\\\"\")",
            out
        );
    }

    #[test]
    fn layout_dump_matches_the_two_node_shape() {
        let mut dump = two_node_model();
        if let Some(b) = dump.boxes.get_mut(1) {
            b.rect = rect(0, 20, 10, 10);
        }
        if let Some(r) = dump.routes.first_mut() {
            r.points = vec![Point { x: 0, y: 10 }, Point { x: 0, y: 20 }];
        }
        if let Some(l) = dump.labels.first_mut() {
            l.rect = rect(0, 10, 8, 5);
            l.lines = vec![String::from("yes")];
        }
        let out = dump.dump_layout(Size { w: 30, h: 40 });
        let expected = concat!(
            "{\"version\":1,\"stage\":\"layout\",\"kind\":\"flowchart\",\"profile\":\"vector\",",
            "\"options\":{\"profile\":\"vector\",\"thoroughness\":3,\"max_width\":0,",
            "\"direction\":\"TB\",\"limits\":{\"max_nodes\":2000,\"max_edges\":5000,",
            "\"max_text_bytes\":1048576}},\"canvas\":{\"w\":30,\"h\":40},\n",
            "\"boxes\":[{\"id\":\"A\",\"role\":\"node\",\"x\":0,\"y\":0,\"w\":10,\"h\":10,",
            "\"parent\":\"\",\"exclusive\":true},\n",
            "{\"id\":\"B\",\"role\":\"node\",\"x\":0,\"y\":20,\"w\":10,\"h\":10,",
            "\"parent\":\"\",\"exclusive\":true}],\n",
            "\"routes\":[{\"id\":\"e0\",\"from\":\"A\",\"to\":\"B\",\"orthogonal\":true,",
            "\"points\":[[0,10],[0,20]]}],\n",
            "\"labels\":[{\"id\":\"e0.label\",\"owner\":\"e0\",\"text\":\"yes\",\"x\":0,\"y\":10,",
            "\"w\":8,\"h\":5,\"lines\":[\"yes\"]}]}\n",
        );
        assert_eq!(out, expected);
    }

    #[test]
    fn empty_arrays_are_written_compactly() {
        let dump = Dump::new("flowchart", DumpOptions::default());
        let out = dump.dump_layout(Size { w: 0, h: 0 });
        assert!(
            out.contains("\"boxes\":[]"),
            "{}; observed: {:?}",
            "Invariant failed: out.contains(\"\\\"boxes\\\":[]\")",
            out
        );
        assert!(
            out.contains("\"routes\":[]"),
            "{}; observed: {:?}",
            "Invariant failed: out.contains(\"\\\"routes\\\":[]\")",
            out
        );
        assert!(
            out.contains("\"labels\":[]"),
            "{}; observed: {:?}",
            "Invariant failed: out.contains(\"\\\"labels\\\":[]\")",
            out
        );
        assert!(
            out.ends_with("}\n"),
            "{}; observed: {:?}",
            "Invariant failed: out.ends_with(\"}\\n\")",
            out
        );
    }

    #[test]
    fn newlines_fall_only_before_the_three_arrays_and_between_their_elements() {
        for body in [
            two_node_model().dump_model(&[]),
            two_node_model().dump_layout(Size { w: 30, h: 40 }),
        ] {
            assert_eq!(body.matches('\n').count(), 5);
            assert_eq!(body.matches(",\n\"boxes\":[").count(), 1);
            assert_eq!(body.matches(",\n\"routes\":[").count(), 1);
            assert_eq!(body.matches(",\n\"labels\":[").count(), 1);
            assert!(
                body.contains("},\n{\"id\":\"B\""),
                "{}; observed: {:?}",
                "Invariant failed: body.contains(\"},\\n{\\\"id\\\":\\\"B\\\"\")",
                body
            );
            assert_eq!(body.matches("],\n\"routes\"").count(), 1);
        }
    }

    #[test]
    fn no_space_or_tab_appears_outside_a_string() {
        let mut dump = two_node_model();
        if let Some(l) = dump.labels.first_mut() {
            l.text = String::from("a b\tc");
        }
        let out = dump.dump_layout(Size { w: 30, h: 40 });
        let mut in_string = false;
        let mut escaped = false;
        for ch in out.chars() {
            if in_string {
                if escaped {
                    escaped = false;
                } else if ch == '\\' {
                    escaped = true;
                } else if ch == '"' {
                    in_string = false;
                }
                continue;
            }
            if ch == '"' {
                in_string = true;
            }
            assert!(ch != ' ' && ch != '\t', "space outside a string");
        }
    }

    #[test]
    fn strings_escape_every_class_and_keep_non_ascii_raw() {
        let mut dump = two_node_model();
        if let Some(l) = dump.labels.first_mut() {
            l.text = String::from("\"\\\u{8}\t\n\u{c}\r\u{1}\u{1f}/\u{7f}é世😀");
        }
        let out = dump.dump_layout(Size { w: 30, h: 40 });
        let expected = "\"text\":\"\\\"\\\\\\b\\t\\n\\f\\r\\u0001\\u001f/\u{7f}é世😀\"";
        assert!(out.contains(expected), "{out}");
        assert!(
            !out.contains("\\u007f"),
            "{}; observed: {:?}",
            "Invariant failed: !out.contains(\"\\\\u007f\")",
            out
        );
    }

    #[test]
    fn integers_have_no_leading_zero_and_no_plus() {
        let mut dump = two_node_model();
        if let Some(a) = dump.boxes.first_mut() {
            a.rect = rect(-5, 0, 0, 0);
        }
        let out = dump.dump_layout(Size { w: 0, h: 0 });
        assert!(
            out.contains("\"x\":-5,"),
            "{}; observed: {:?}",
            "Invariant failed: out.contains(\"\\\"x\\\":-5,\")",
            out
        );
        assert!(
            out.contains("\"w\":0,"),
            "{}; observed: {:?}",
            "Invariant failed: out.contains(\"\\\"w\\\":0,\")",
            out
        );
        assert!(
            !out.contains('+'),
            "{}; observed: {:?}",
            "Invariant failed: !out.contains('+')",
            out
        );
    }

    #[test]
    fn push_int_writes_minimal_decimal() {
        let cases: [(i64, &str); 7] = [
            (0, "0"),
            (1, "1"),
            (-1, "-1"),
            (9, "9"),
            (10, "10"),
            (2_147_483_647, "2147483647"),
            (i64::MIN, "-9223372036854775808"),
        ];
        for (value, want) in cases {
            let mut out = String::new();
            push_int(&mut out, value);
            assert_eq!(out, want);
        }
    }

    #[test]
    fn options_carry_the_config_keys_in_key_order() {
        let mut options = DumpOptions {
            profile: Profile::Cell,
            ..DumpOptions::default()
        };
        options
            .config
            .insert(String::from("zeta"), DumpValue::Integer(7));
        options
            .config
            .insert(String::from("alpha"), DumpValue::Bool(true));
        options
            .config
            .insert(String::from("mid"), DumpValue::String(String::from("x")));
        let dump = Dump::new("flowchart", options);
        let out = dump.dump_layout(Size { w: 1, h: 1 });
        let alpha = out.find("\"alpha\":true");
        let mid = out.find("\"mid\":\"x\"");
        let zeta = out.find("\"zeta\":7");
        assert!(
            alpha.is_some() && mid.is_some() && zeta.is_some(),
            "{}; observed: {:?}",
            "Invariant failed: alpha.is_some() && mid.is_some() && zeta.is_some()",
            out
        );
        assert!(
            alpha < mid && mid < zeta,
            "{}; observed: {:?}",
            "Invariant failed: alpha < mid && mid < zeta",
            out
        );
        assert!(
            out.contains("\"profile\":\"cell\""),
            "{}; observed: {:?}",
            "Invariant failed: out.contains(\"\\\"profile\\\":\\\"cell\\\"\")",
            out
        );
    }

    #[test]
    fn model_dump_omits_canvas_and_coordinates() {
        let mut dump = two_node_model();
        if let Some(r) = dump.routes.first_mut() {
            r.points = vec![Point { x: 3, y: 4 }];
        }
        let out = dump.dump_model(&[]);
        assert!(
            !out.contains("canvas"),
            "{}; observed: {:?}",
            "Invariant failed: !out.contains(\"canvas\")",
            out
        );
        assert!(
            !out.contains("\"x\":"),
            "{}; observed: {:?}",
            "Invariant failed: !out.contains(\"\\\"x\\\":\")",
            out
        );
        assert!(
            !out.contains("\"points\""),
            "{}; observed: {:?}",
            "Invariant failed: !out.contains(\"\\\"points\\\"\")",
            out
        );
        assert!(
            out.contains("\"orthogonal\":true}"),
            "{}; observed: {:?}",
            "Invariant failed: out.contains(\"\\\"orthogonal\\\":true}\")",
            out
        );
        assert_eq!(Stage::Model.as_str(), "model");
        assert_eq!(Stage::Layout.as_str(), "layout");
    }

    #[test]
    fn a_parent_and_a_group_role_reach_the_bytes() {
        let mut dump = two_node_model();
        if let Some(b) = dump.boxes.first_mut() {
            b.role = BoxRole::Group;
            b.parent = String::from("A");
            b.exclusive = false;
        }
        let out = dump.dump_model(&[]);
        assert!(out.contains("{\"id\":\"A\",\"role\":\"group\",\"parent\":\"A\",\"exclusive\":false,\"direction\":\"\"}"), "{}; observed: {:?}", "Invariant failed: out.contains(\"{\\\"id\\\":\\\"A\\\",\\\"role\\\":\\\"group\\\",\\\"parent\\\":\\\"A\\\",\\\"exclusive\\\":false,\\\"direction\\\":\\\"\\\"}\")", out);
    }
    #[test]
    fn route_styles_are_model_stage_only() {
        let mut dump = two_node_model();
        let route = &mut dump.routes[0];
        route.marker_start = "circle".into();
        route.marker_end = "cross".into();
        route.stroke = "dotted".into();
        let layout = dump.dump_layout(Size { w: 20, h: 20 });
        for key in ["\"marker_start\"", "\"marker_end\"", "\"stroke\""] {
            assert!(
                !layout.contains(key),
                "{}; observed: {:?}",
                "Invariant failed: !layout.contains(key)",
                layout
            );
        }
        {
            let observed = dump.dump_model(&[]);
            assert!(observed.contains("\"orthogonal\":true,\"marker_start\":\"circle\",\"marker_end\":\"cross\",\"stroke\":\"dotted\""), "{}; observed: {:?}", "Invariant failed: dump.dump_model(&[]).contains(\"\\\"orthogonal\\\":true,\\\"marker_start\\\":\\\"circle\\\",\\\"marker_end\\\":\\\"cross\\\",\\\"stroke\\\":\\\"dotted\\\"\")", observed);
        };
    }
}
