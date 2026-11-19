use super::*;

fn input(source: &str, profile: Profile) -> Result<Input, &'static str> {
    let parsed = crate::syntax::er::parse(source, &[]);
    if !parsed.diagnostics.is_empty() {
        return Err("ER syntax diagnostics");
    }
    let (model, diagnostics) = crate::model::er::resolve(source, &parsed.document);
    if !diagnostics.is_empty() {
        return Err("ER semantic diagnostics");
    }
    from_er(&model, profile, DumpOptions::default()).map_err(|_| "ER input error")
}

#[test]
fn er_shapes_and_minimum_sizes() -> Result<(), &'static str> {
    for (profile, expected) in [
        (Profile::Cell, Size { w: 13, h: 5 }),
        (Profile::Vector, Size { w: 6400, h: 4800 }),
    ] {
        let input = input("erDiagram\nA\n", profile)?;
        let node = input.boxes.first().ok_or("missing entity")?;
        assert_eq!((node.id.as_str(), node.shape.as_str()), ("A", "erBox"));
        let Some(SizeRule::Content(size)) = input.sizes.first() else {
            return Err("missing content size");
        };
        assert_eq!(*size, expected);
    }
    Ok(())
}

#[test]
fn er_cardinality_and_line_kinds() -> Result<(), &'static str> {
    let input = input(
        "erDiagram\nA ||--o{ B : owns\nA |o..|{ B : uses\n",
        Profile::Cell,
    )?;
    let values = input
        .routes
        .iter()
        .map(|route| {
            (
                route.marker_start.as_str(),
                route.marker_end.as_str(),
                route.line.as_str(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        values,
        [
            ("zero_or_more", "only_one", "normal"),
            ("one_or_more", "zero_or_one", "dashed")
        ]
    );
    assert_eq!(
        input
            .labels
            .iter()
            .map(|label| label.text.as_str())
            .collect::<Vec<_>>(),
        ["owns", "uses"]
    );
    Ok(())
}

#[test]
fn er_table_keeps_columns() -> Result<(), &'static str> {
    let input = input("erDiagram\nA { int id PK \"identifier\" }\n", Profile::Cell)?;
    let node = input.boxes.first().ok_or("missing entity")?;
    assert_eq!(node.text, "A<br/><br/>int|id|PK|identifier");
    let items = table_items(
        &node.text,
        Rect {
            x: 0,
            y: 0,
            w: 27,
            h: 5,
        },
        Profile::Cell,
    )
    .map_err(|_| "table failure")?;
    assert_eq!(
        items
            .iter()
            .filter(|item| matches!(item, crate::scene::Item::Text(_)))
            .count(),
        5
    );
    Ok(())
}

#[test]
fn er_groups_and_route_ids() -> Result<(), &'static str> {
    let input = input(
        "erDiagram\ne0\nsubgraph G [Group]\nA\nend\nG ||--|| A : owns\n",
        Profile::Cell,
    )?;
    assert_eq!(input.groups.len(), 1);
    assert_eq!(
        input.routes.first().map(|route| route.id.as_str()),
        Some("e1")
    );
    assert_eq!(
        input
            .boxes
            .iter()
            .find(|node| node.id == "A")
            .map(|node| node.parent.as_str()),
        Some("G")
    );
    Ok(())
}

#[test]
fn er_md_parent_has_no_marker() -> Result<(), &'static str> {
    let input = input(
        "erDiagram\nA u--|| B : parent\nA ||--u-B : child\n",
        Profile::Cell,
    )?;
    let markers = input
        .routes
        .iter()
        .map(|route| (route.marker_start.as_str(), route.marker_end.as_str()))
        .collect::<Vec<_>>();
    assert_eq!(markers, [("only_one", ""), ("", "only_one")]);
    Ok(())
}

#[test]
fn er_height_reserves_only_the_header_divider_in_cells() -> Result<(), &'static str> {
    let text = "A<br/><br/>int|a||<br/>int|b||";
    assert_eq!(
        table_size(text, Profile::Cell).map_err(|_| "cell size")?,
        Size { w: 13, h: 6 }
    );
    assert_eq!(
        table_size(text, Profile::Vector).map_err(|_| "vector size")?,
        Size { w: 6400, h: 5760 }
    );
    Ok(())
}

#[test]
fn er_escaped_fields_keep_multiline_text_and_column_delimiters() -> Result<(), &'static str> {
    let encoded = encode_field("line1<br/>line2|literal\\n");
    assert_eq!(encoded, "line1\\nline2\\pliteral\\\\n");
    assert_eq!(decode_field(&encoded), "line1\nline2|literal\\n");
    let table =
        Table::new(&format!("A<br/><br/>{encoded}|name||"), Profile::Cell).map_err(|_| "table")?;
    assert_eq!(table.row_heights, [2]);
    Ok(())
}

#[test]
fn er_hidden_entity_endpoints_bind_to_final_group_box() -> Result<(), &'static str> {
    let input = input(
        "erDiagram\nG ||--|| A : before\nsubgraph G\nB\nend\nG ||--|| A : after\n",
        Profile::Cell,
    )?;
    assert_eq!(input.boxes.iter().filter(|node| node.id == "G").count(), 1);
    assert_eq!(
        input
            .boxes
            .iter()
            .find(|node| node.id == "G")
            .map(|node| node.role),
        Some(BoxRole::Group)
    );
    assert_eq!(
        input
            .routes
            .iter()
            .map(|route| route.from.as_str())
            .collect::<Vec<_>>(),
        ["G", "G"]
    );
    Ok(())
}

#[test]
fn er_fields_emit_flagged_runs_and_keep_field_lines() -> Result<(), &'static str> {
    let text = "A<br/><br/>x\\ny|**id**||";
    let px = constant(Profile::Cell, "padding_x").map_err(|_| "padding_x")?;
    let py = constant(Profile::Cell, "padding_y").map_err(|_| "padding_y")?;
    let min_width = constant(Profile::Cell, "min_width").map_err(|_| "min_width")?;
    let field_widths = [1, 2];
    let content_width = field_widths.iter().sum::<i32>() + px;
    let size = table_size(text, Profile::Cell).map_err(|_| "cell size")?;
    assert_eq!(
        size,
        Size {
            w: min_width.max(content_width + 2 * px),
            h: 1 + 2 + 1 + 2 * py
        }
    );
    let items = table_items(
        text,
        Rect {
            x: 0,
            y: 0,
            w: size.w,
            h: size.h,
        },
        Profile::Cell,
    )
    .map_err(|_| "table items")?;
    let texts = items
        .iter()
        .filter_map(|item| match item {
            crate::scene::Item::Text(text) => Some(text),
            _ => None,
        })
        .collect::<Vec<_>>();
    let bold = texts
        .iter()
        .find(|text| {
            text.lines
                .iter()
                .any(|line| line.iter().any(|run| run.bold))
        })
        .ok_or("missing bold cell")?;
    assert_eq!(
        bold.lines,
        [vec![crate::scene::Run {
            text: "id".into(),
            bold: true,
            italic: false
        }]]
    );
    let split = texts
        .iter()
        .find(|text| text.lines.len() == 2)
        .ok_or("missing two-line field")?;
    assert_eq!(
        split.lines,
        [
            vec![crate::scene::Run::plain("x")],
            vec![crate::scene::Run::plain("y")]
        ]
    );
    Ok(())
}

#[test]
fn er_layout_draws_table_compartments_under_both_profiles() -> Result<(), &'static str> {
    for profile in [Profile::Cell, Profile::Vector] {
        let input = input("erDiagram\nA { int id PK \"key\" }\n", profile)?;
        let (scene, _) = layout(&input).map_err(|_| "ER layout")?;
        let group = scene
            .items()
            .iter()
            .find(|group| group.owner == "A")
            .ok_or("missing node group")?;
        let texts = group
            .items
            .iter()
            .filter_map(|item| match item {
                crate::scene::Item::Text(text) => Some(text),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(texts.len(), 5);
        assert_eq!(
            scene.boxes().first().map(|node| node.id.as_str()),
            Some("A")
        );
    }
    Ok(())
}
