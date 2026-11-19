use super::input::{Box as InputBox, Input, Route};
use crate::geom::Rect;
use crate::scene::{Dump, SceneBox, SceneLabel, SceneRoute};
use std::collections::BTreeSet;

pub fn model_dump(input: &Input) -> String {
    let mut options = input.options.clone();
    options.profile = input.profile;
    options.direction = input.direction;
    let boxes = input
        .boxes
        .iter()
        .map(|b| SceneBox {
            id: b.id.clone(),
            role: b.role,
            rect: Rect {
                x: 0,
                y: 0,
                w: 0,
                h: 0,
            },
            parent: b.parent.clone(),
            exclusive: b.exclusive,
        })
        .collect();
    let routes = input
        .routes
        .iter()
        .map(|r| SceneRoute {
            id: r.id.clone(),
            from: r.from.clone(),
            to: r.to.clone(),
            orthogonal: r.orthogonal,
            points: Vec::new(),
            marker_start: if r.marker_start == "none" {
                String::new()
            } else {
                r.marker_start.clone()
            },
            marker_end: model_marker_end(&r.marker_end),
            stroke: r.line.clone(),
        })
        .collect();
    let labels = input
        .labels
        .iter()
        .map(|l| SceneLabel {
            id: l.id.clone(),
            owner: l.owner.clone(),
            text: l.text.clone(),
            rect: Rect {
                x: 0,
                y: 0,
                w: 0,
                h: 0,
            },
            lines: Vec::new(),
        })
        .collect();
    let dump = Dump {
        boxes,
        routes,
        labels,
        ..Dump::new(input.kind, options)
    };
    let owners: BTreeSet<&str> = input.labels.iter().map(|l| l.owner.as_str()).collect();
    let boxes = input.boxes.iter().map(|b| crate::scene::dump::ModelBox {
        direction: model_direction(&b.direction),
        shape: &b.shape,
        icon: b.icon,
        text: if input.kind == "architecture" {
            Some(b.text.as_str())
        } else {
            let text = model_box_text(b, &owners);
            (!text.is_empty()).then_some(text)
        },
    });
    let routes = input.routes.iter().map(|r| crate::scene::dump::ModelRoute {
        from_side: r.from_side.map(super::input::RouteSide::token),
        to_side: r.to_side.map(super::input::RouteSide::token),
        min_length: model_min_length(r, &owners),
    });
    let regions: Vec<Vec<i64>> = input
        .region_sets
        .iter()
        .map(|set| {
            std::iter::once(set.parent)
                .chain(set.regions.iter().copied())
                .map(model_region_value)
                .collect()
        })
        .collect();
    let mut out = String::new();
    crate::scene::dump::push_model_records(&mut out, &dump, boxes, routes, &regions);
    out
}

fn model_direction(token: &str) -> &str {
    match crate::scene::Direction::from_token(token) {
        Some(direction) => direction.as_str(),
        None => token,
    }
}

fn model_region_value(value: usize) -> i64 {
    i64::try_from(value).unwrap_or(-1)
}

fn model_box_text<'a>(b: &'a InputBox, owners: &BTreeSet<&str>) -> &'a str {
    if owners.contains(b.id.as_str()) || b.text == b.id {
        ""
    } else {
        &b.text
    }
}

fn model_min_length(r: &Route, owners: &BTreeSet<&str>) -> usize {
    let default = if owners.contains(r.id.as_str()) { 2 } else { 1 };
    if r.min_length > default {
        r.min_length
    } else {
        0
    }
}

fn model_marker_end(marker: &str) -> String {
    if marker.is_empty() {
        "none".into()
    } else {
        marker.into()
    }
}

#[cfg(test)]
mod tests {
    use crate::{layout, model, scene, syntax};

    #[test]
    fn architecture_model_dump_text_presence() -> Result<(), &'static str> {
        use syntax::config_value::ConfigValue;

        for (source, expected) in [
            ("architecture-beta\ngroup g\n", ""),
            ("architecture-beta\ngroup g[g]\n", "g"),
        ] {
            let (model, diagnostics) =
                model::Resolved::parse(crate::DiagramKind::Architecture, source, &[]);
            assert!(diagnostics.is_empty(), "{diagnostics:?}");
            let model = model.ok_or("no architecture model")?;
            for profile in [scene::Profile::Vector, scene::Profile::Cell] {
                let input = model
                    .input(profile, scene::DumpOptions::default())
                    .map_err(|_| "architecture input failed")?;
                let dump = super::model_dump(&input);
                let (value, diagnostics) =
                    syntax::config_value::parse_config_json(&dump, 0, dump.len());
                assert!(diagnostics.is_empty(), "{diagnostics:?}");
                let ConfigValue::Sequence(boxes) = json_field(&value, "boxes")? else {
                    return Err("expected boxes array");
                };
                let group = boxes
                    .iter()
                    .find(|entry| {
                        json_field(entry, "id").ok() == Some(&ConfigValue::String("g".into()))
                    })
                    .ok_or("missing architecture group")?;
                assert_eq!(
                    json_field(group, "text")?,
                    &ConfigValue::String(expected.into()),
                    "{profile:?}: {dump}"
                );
            }
        }
        Ok(())
    }

    #[test]
    fn model_icon_tracks_nonempty_attribute_not_shape() -> Result<(), &'static str> {
        for (attributes, expected) in [
            ("shape: icon", false),
            ("icon: \"\"", false),
            ("icon: \"fa:home\"", true),
            ("icon: \"fa:home\", form: circle", true),
        ] {
            let source = format!("flowchart\nA@{{{attributes}, label: Home}}\n");
            let parsed = syntax::flowchart::parse(&source, &[]);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let (model, diagnostics) = model::flowchart::resolve(&source, &parsed.document);
            assert!(diagnostics.is_empty(), "{diagnostics:?}");
            for profile in [scene::Profile::Vector, scene::Profile::Cell] {
                let input = layout::flowchart::from_flowchart(
                    &model,
                    profile,
                    scene::DumpOptions::default(),
                );
                let dump = super::model_dump(&input);
                assert_model_icon(&dump, expected)?;
            }
        }
        Ok(())
    }

    fn json_field<'a>(
        value: &'a syntax::config_value::ConfigValue,
        key: &str,
    ) -> Result<&'a syntax::config_value::ConfigValue, &'static str> {
        let syntax::config_value::ConfigValue::Mapping(entries) = value else {
            return Err("expected JSON object");
        };
        entries
            .iter()
            .find(|entry| entry.key == key)
            .map(|entry| &entry.value)
            .ok_or("missing JSON field")
    }

    fn assert_model_icon(dump: &str, expected: bool) -> Result<(), &'static str> {
        use syntax::config_value::ConfigValue;
        let (value, diagnostics) = syntax::config_value::parse_config_json(dump, 0, dump.len());
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let ConfigValue::Sequence(boxes) = json_field(&value, "boxes")? else {
            return Err("expected boxes array");
        };
        let node = boxes.first().ok_or("missing node")?;
        assert_eq!(json_field(node, "id")?, &ConfigValue::String("A".into()));
        assert_eq!(
            json_field(node, "icon").ok(),
            expected.then_some(&ConfigValue::Bool(true))
        );
        assert!(json_field(node, "text").is_err(), "{dump}");
        let ConfigValue::Mapping(fields) = node else {
            return Err("expected node object");
        };
        assert_eq!(
            fields
                .windows(2)
                .any(|pair| pair[0].key == "shape" && pair[1].key == "icon"),
            expected,
            "{dump}"
        );
        let ConfigValue::Sequence(labels) = json_field(&value, "labels")? else {
            return Err("expected labels array");
        };
        let label = labels.first().ok_or("missing label")?;
        assert_eq!(
            json_field(label, "owner")?,
            &ConfigValue::String("A".into())
        );
        assert_eq!(
            json_field(label, "text")?,
            &ConfigValue::String("Home".into())
        );
        Ok(())
    }

    #[test]
    fn source_default_rectangles_omit_model_shape() {
        let source = "flowchart\nA -->|yes| B\n";
        let parsed = syntax::flowchart::parse(source, &[]);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let (model, diagnostics) = model::flowchart::resolve(source, &parsed.document);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        for profile in [scene::Profile::Vector, scene::Profile::Cell] {
            let input =
                layout::flowchart::from_flowchart(&model, profile, scene::DumpOptions::default());
            let dump = super::model_dump(&input);
            assert!(
                dump.contains("\"id\":\"A\",\"role\":\"node\""),
                "{profile:?}: {dump}"
            );
            assert!(
                dump.contains("\"id\":\"B\",\"role\":\"node\""),
                "{profile:?}: {dump}"
            );
            assert!(!dump.contains("\"shape\":"), "{profile:?}: {dump}");
        }
    }

    fn dump_of(kind: crate::DiagramKind, source: &str) -> Result<String, &'static str> {
        let (model, diagnostics) = model::Resolved::parse(kind, source, &[]);
        if !diagnostics.is_empty() {
            return Err("source has diagnostics");
        }
        let input = model
            .ok_or("no model")?
            .input(scene::Profile::Vector, scene::DumpOptions::default())
            .map_err(|_| "input failed")?;
        Ok(super::model_dump(&input))
    }

    fn record(dump: &str, id: &str) -> Result<String, &'static str> {
        let needle = format!("{{\"id\":\"{id}\",");
        dump.lines()
            .find_map(|line| {
                let start = line.find(&needle)?;
                let rest = line.get(start..)?;
                Some(format!("{}}}", rest.trim_end_matches([',', ']', '}'])))
            })
            .ok_or("record not found")
    }

    #[test]
    fn er_boxes_carry_the_measured_table() -> Result<(), &'static str> {
        let dump = dump_of(
            crate::DiagramKind::Er,
            "erDiagram\nCUSTOMER ||--o{ ORDER : places\nCUSTOMER {\n  string name PK \"the <br> name\"\n  int age\n}\nORDER { int id }\n",
        )?;
        assert_eq!(
            record(&dump, "CUSTOMER")?,
            r#"{"id":"CUSTOMER","role":"node","parent":"","exclusive":true,"shape":"erBox","text":"CUSTOMER<br/><br/>string|name|PK|the \\n name<br/>int|age||"}"#
        );
        assert_eq!(
            record(&dump, "ORDER")?,
            r#"{"id":"ORDER","role":"node","parent":"","exclusive":true,"shape":"erBox","text":"ORDER<br/><br/>int|id||"}"#
        );
        Ok(())
    }

    #[test]
    fn er_group_title_and_empty_table() -> Result<(), &'static str> {
        let dump = dump_of(
            crate::DiagramKind::Er,
            "erDiagram\nsubgraph G [Group]\nA\nend\n",
        )?;
        assert_eq!(
            record(&dump, "A")?,
            r#"{"id":"A","role":"node","parent":"G","exclusive":true,"shape":"erBox","text":"A<br/><br/>"}"#
        );
        assert_eq!(
            record(&dump, "G")?,
            r#"{"id":"G","role":"group","parent":"","exclusive":false,"direction":"","text":"Group"}"#
        );
        Ok(())
    }

    #[test]
    fn boxes_with_label_records_carry_no_text() -> Result<(), &'static str> {
        for (kind, source) in [
            (crate::DiagramKind::Flowchart, "flowchart\nA[Start] --> B\n"),
            (
                crate::DiagramKind::Class,
                "classDiagram\nclass Animal {\n  +name\n}\n",
            ),
            (
                crate::DiagramKind::Requirement,
                "requirementDiagram\nrequirement r {\n  id: 1\n  text: x\n  risk: low\n  verifymethod: test\n}\n",
            ),
        ] {
            let dump = dump_of(kind, source)?;
            let boxes = dump
                .lines()
                .filter(|line| line.contains("\"exclusive\":"))
                .count();
            assert!(boxes > 0, "{dump}");
            for line in dump.lines().filter(|line| line.contains("\"exclusive\":")) {
                assert!(!line.contains("\"text\":"), "{line}");
            }
        }
        Ok(())
    }

    #[test]
    fn min_length_key_follows_the_route_default() -> Result<(), &'static str> {
        let usecase = dump_of(
            crate::DiagramKind::Usecase,
            "usecase-beta\nactor A\nA ----> B\nA --> C\n",
        )?;
        assert_eq!(
            record(&usecase, "e0")?,
            r#"{"id":"e0","from":"A","to":"B","orthogonal":true,"min_length":3}"#
        );
        assert_eq!(
            record(&usecase, "e1")?,
            r#"{"id":"e1","from":"A","to":"C","orthogonal":true}"#
        );
        let agentflow = dump_of(
            crate::DiagramKind::Agentflow,
            "agentflow-beta TB\n  a[\"a\"]\n  b[\"b\"]\n  c[\"c\"]\n  d[\"d\"]\n  a ---> b\n  a --->|x| c\n  c ---->|y| d\n  c --> d\n",
        )?;
        for (id, expected) in [
            (
                "e0",
                r#"{"id":"e0","from":"a","to":"b","orthogonal":true,"min_length":2}"#,
            ),
            ("e1", r#"{"id":"e1","from":"a","to":"c","orthogonal":true}"#),
            (
                "e2",
                r#"{"id":"e2","from":"c","to":"d","orthogonal":true,"min_length":3}"#,
            ),
            ("e3", r#"{"id":"e3","from":"c","to":"d","orthogonal":true}"#),
        ] {
            assert_eq!(record(&agentflow, id)?, expected);
        }
        Ok(())
    }

    #[test]
    fn min_length_default_depends_on_labels() {
        let route = |id: &str, min_length: usize| super::Route {
            id: id.into(),
            from: String::new(),
            to: String::new(),
            orthogonal: true,
            marker_start: String::new(),
            marker_end: String::new(),
            line: String::new(),
            min_length,
            from_side: None,
            to_side: None,
        };
        let owners = std::collections::BTreeSet::from(["e1"]);
        for (id, min_length, expected) in [
            ("e0", 1, 0),
            ("e0", 2, 2),
            ("e1", 2, 0),
            ("e1", 3, 3),
            ("e0", 0, 0),
        ] {
            assert_eq!(
                super::model_min_length(&route(id, min_length), &owners),
                expected,
                "{id} {min_length}"
            );
        }
    }

    #[test]
    fn layout_stage_dump_carries_no_model_only_keys() -> Result<(), &'static str> {
        for (kind, source) in [
            (
                crate::DiagramKind::Er,
                "erDiagram\nCUSTOMER ||--o{ ORDER : places\nCUSTOMER { string name }\n",
            ),
            (
                crate::DiagramKind::Usecase,
                "usecase-beta\nactor A\nA ----> B\n",
            ),
        ] {
            let (model, diagnostics) = model::Resolved::parse(kind, source, &[]);
            assert!(diagnostics.is_empty(), "{diagnostics:?}");
            let input = model
                .ok_or("no model")?
                .input(scene::Profile::Vector, scene::DumpOptions::default())
                .map_err(|_| "input failed")?;
            let (scene, _) = layout::families::layout(&input).map_err(|_| "layout failed")?;
            let dump = scene.dump();
            assert!(!dump.contains("min_length"), "{dump}");
            for line in dump.lines().filter(|line| line.contains("\"exclusive\":")) {
                assert!(!line.contains("\"text\":"), "{line}");
            }
        }
        Ok(())
    }

    #[test]
    fn absent_target_marker_is_written_as_none() -> Result<(), &'static str> {
        let er = dump_of(
            crate::DiagramKind::Er,
            "erDiagram\nA u--o{ B : x\nA ||--|| B : y\n",
        )?;
        assert_eq!(
            record(&er, "e0")?,
            r#"{"id":"e0","from":"A","to":"B","orthogonal":true,"marker_start":"zero_or_more","marker_end":"none"}"#
        );
        assert_eq!(
            record(&er, "e1")?,
            r#"{"id":"e1","from":"A","to":"B","orthogonal":true,"marker_start":"only_one","marker_end":"only_one"}"#
        );
        let flowchart = dump_of(
            crate::DiagramKind::Flowchart,
            "flowchart\nA --- B\nA --> C\nA --x D\n",
        )?;
        for (id, expected) in [
            (
                "e0",
                r#"{"id":"e0","from":"A","to":"B","orthogonal":true,"marker_end":"none"}"#,
            ),
            ("e1", r#"{"id":"e1","from":"A","to":"C","orthogonal":true}"#),
            (
                "e2",
                r#"{"id":"e2","from":"A","to":"D","orthogonal":true,"marker_end":"cross"}"#,
            ),
        ] {
            assert_eq!(record(&flowchart, id)?, expected);
        }
        Ok(())
    }

    #[test]
    fn sequence_dump_carries_node_wrap_token_and_regions() -> Result<(), &'static str> {
        let dump = dump_of(
            crate::DiagramKind::Sequence,
            "sequenceDiagram\nparticipant A\nparticipant B\nNote over A,B: nowrap:nw\n",
        )?;
        assert_eq!(
            record(&dump, "note0")?,
            r#"{"id":"note0","role":"node","parent":"","exclusive":false,"direction":"n","shape":"note"}"#
        );
        assert!(dump.ends_with("\n\"regions\":[[0,545,0,1,2]]}\n"), "{dump}");
        Ok(())
    }

    #[test]
    fn dump_without_region_sets_omits_regions_and_node_direction() -> Result<(), &'static str> {
        let dump = dump_of(
            crate::DiagramKind::Flowchart,
            "flowchart\nsubgraph g\nA --> B\nend\n",
        )?;
        assert!(!dump.contains("\"regions\""), "{dump}");
        assert_eq!(
            record(&dump, "A")?,
            r#"{"id":"A","role":"node","parent":"g","exclusive":true}"#
        );
        Ok(())
    }
}
