use super::input::{Box, Input, Label, Route, SizeRule};
use crate::{
    geom::{GeomError, Rect, Size},
    model::requirement::{Model, NodeRef},
    scene::{BoxRole, Direction, DumpOptions, Profile, TextRole},
};

pub fn from_requirement(
    model: &Model,
    profile: Profile,
    options: DumpOptions,
) -> Result<Input, GeomError> {
    let mut input = Input {
        kind: "requirement",
        profile,
        direction: Direction::from_token(&model.direction).unwrap_or_default(),
        options,
        boxes: Vec::new(),
        routes: Vec::new(),
        labels: Vec::new(),
        groups: Vec::new(),
        sizes: Vec::new(),
        attachments: Vec::new(),
        region_sets: Vec::new(),
        spacing: super::input::Spacing::default(),
    };
    for requirement in &model.requirements {
        append_box(&mut input, requirement.name.clone(), requirement.rows())?;
    }
    for (index, element) in model.elements.iter().enumerate() {
        let id = element_id(model, index);
        append_box(&mut input, id, element.rows())?;
    }
    append_relations(&mut input, model);
    Ok(input)
}

fn element_id(model: &Model, index: usize) -> String {
    let Some(element) = model.elements.get(index) else {
        return String::new();
    };
    if !model
        .requirements
        .iter()
        .any(|node| node.name == element.name)
    {
        return element.name.clone();
    }
    let mut candidate = format!("element:{index}");
    while model.requirements.iter().any(|node| node.name == candidate)
        || model.elements.iter().any(|node| node.name == candidate)
    {
        candidate.push(':');
    }
    candidate
}

fn append_box(input: &mut Input, id: String, rows: Vec<String>) -> Result<(), GeomError> {
    let text = rows.join("\n");
    input
        .sizes
        .push(SizeRule::Content(table_size(&text, input.profile)?));
    input.labels.push(Label {
        id: format!("{id}.label"),
        owner: id.clone(),
        role: TextRole::Label,
        text: text.clone(),
    });
    input.boxes.push(Box {
        id,
        role: BoxRole::Node,
        shape: "requirementBox".into(),
        icon: false,
        parent: String::new(),
        exclusive: true,
        text,
        direction: String::new(),
    });
    Ok(())
}

fn endpoint(model: &Model, node: Option<NodeRef>, name: &str) -> String {
    match node {
        Some(NodeRef::Requirement(index)) => model
            .requirements
            .get(index)
            .map_or_else(|| name.into(), |node| node.name.clone()),
        Some(NodeRef::Element(index)) => element_id(model, index),
        None => name.into(),
    }
}

fn append_relations(input: &mut Input, model: &Model) {
    let mut next = 0usize;
    for relation in &model.relationships {
        if relation.from_node.is_none() || relation.to_node.is_none() {
            continue;
        }
        let mut id = format!("e{next}");
        while input.boxes.iter().any(|node| node.id == id) {
            next += 1;
            id = format!("e{next}");
        }
        next += 1;
        let contains = relation.kind == "contains";
        input.labels.push(Label {
            id: format!("{id}.label"),
            owner: id.clone(),
            role: TextRole::Label,
            text: relation.label.clone(),
        });
        input.routes.push(Route {
            id,
            from: endpoint(model, relation.from_node, &relation.from.value),
            to: endpoint(model, relation.to_node, &relation.to.value),
            orthogonal: true,
            marker_start: if contains {
                "requirement_contains"
            } else {
                "none"
            }
            .into(),
            marker_end: if contains {
                "none"
            } else {
                "requirement_arrow"
            }
            .into(),
            line: if contains { "normal" } else { "dashed" }.into(),
            min_length: 2,
            from_side: None,
            to_side: None,
        });
    }
}

fn constant(profile: Profile, name: &str) -> Result<i32, GeomError> {
    let key = format!("{}.requirement.{name}", profile.as_str());
    crate::r#gen::layoutconst::LAYOUT_CONST
        .iter()
        .find(|row| row.name == key)
        .map(|row| row.value)
        .ok_or(GeomError::Domain)
}

fn line_height(profile: Profile) -> i32 {
    match profile {
        Profile::Cell => 1,
        Profile::Vector => crate::measure::Role::Label.line_height_px() * 64,
    }
}

fn metric(profile: Profile) -> crate::measure::Metric {
    if profile == Profile::Cell {
        crate::measure::Metric::Cell
    } else {
        crate::measure::Metric::for_role(crate::measure::Role::Label)
    }
}

/// The styled lines of one structural row piece: accepted br tags force
/// lines (math-05), bold and italic runs measure at their own weights
/// (math-03, math-04), escapes lose their backslash, unsupported markup
/// stays literal (math-07, math-08), and math spans stay opaque. An empty
/// piece yields no line.
fn piece_lines<'a>(
    piece: &'a str,
    profile: Profile,
) -> Result<Vec<crate::measure::StyledLine<'a>>, GeomError> {
    crate::measure::styled_lines(piece, i32::MAX, metric(profile))
}

/// The scene runs of one structural row piece: one line per styled line,
/// each carrying its bold and italic flags. An empty piece keeps one empty
/// plain line, so plain rows emit exactly what `Run::plain` emitted.
fn run_lines(piece: &str, profile: Profile) -> Result<Vec<Vec<crate::scene::Run>>, GeomError> {
    let lines = piece_lines(piece, profile)?;
    let mapped = lines
        .iter()
        .map(|line| {
            let runs: Vec<crate::scene::Run> = line
                .runs
                .iter()
                .map(|run| crate::scene::Run {
                    text: run.text.to_string(),
                    bold: run.bold,
                    italic: run.italic,
                })
                .collect();
            if runs.is_empty() {
                vec![crate::scene::Run::plain(String::new())]
            } else {
                runs
            }
        })
        .collect::<Vec<_>>();
    if mapped.is_empty() {
        return Ok(vec![vec![crate::scene::Run::plain(String::new())]]);
    }
    Ok(mapped)
}

fn layout_error(error: GeomError) -> super::layered::LayoutError {
    match error {
        GeomError::Domain => super::layered::LayoutError::Domain,
        GeomError::Overflow => super::layered::LayoutError::Overflow,
    }
}

fn table_size(text: &str, profile: Profile) -> Result<Size, GeomError> {
    let mut width = 0i32;
    let mut rows = 0i32;
    let padding_y = constant(profile, "padding_y")?;
    for piece in text.split('\n') {
        let lines = piece_lines(piece, profile)?;
        rows = rows
            .checked_add(i32::try_from(lines.len().max(1)).map_err(|_| GeomError::Overflow)?)
            .ok_or(GeomError::Overflow)?;
        for line in &lines {
            width = width.max(line.width);
        }
    }
    Ok(Size {
        w: width
            .checked_add(constant(profile, "padding_x")?)
            .ok_or(GeomError::Overflow)?,
        h: rows
            .checked_mul(line_height(profile))
            .and_then(|height| height.checked_add(padding_y))
            .ok_or(GeomError::Overflow)?,
    })
}

pub fn layout(input: &Input) -> Result<(crate::scene::Scene, bool), super::layered::LayoutError> {
    let edges = input
        .routes
        .iter()
        .map(|route| super::layered::pipeline::EdgeOptions {
            marker_start: marker(&route.marker_start),
            marker_end: marker(&route.marker_end),
            stroke: &route.line,
            min_length: 1,
        })
        .collect::<Vec<_>>();
    let (scene, budget) = super::layered::pipeline::layout_family(input, &edges)?;
    Ok((table_scene(input, scene)?, budget))
}

fn marker(name: &str) -> Option<crate::scene::MarkerName> {
    crate::r#gen::markers::MARKERS
        .iter()
        .find(|row| row.name == name)
        .and_then(|row| crate::scene::MarkerName::new(row.name))
}

fn table_scene(
    input: &Input,
    scene: crate::scene::Scene,
) -> Result<crate::scene::Scene, super::layered::LayoutError> {
    let mut groups = scene.items().to_vec();
    for group in &mut groups {
        let Some(node) = input.boxes.iter().find(|node| node.id == group.owner) else {
            continue;
        };
        let Some(bounds) = scene.boxes().iter().find(|bounds| bounds.id == node.id) else {
            continue;
        };
        group.items = table_items(&node.text, bounds.rect, input.profile)?;
    }
    Ok(crate::scene::Scene::new(
        scene.canvas(),
        scene.dump_part().clone(),
        groups,
    ))
}

fn table_items(
    text: &str,
    rect: Rect,
    profile: Profile,
) -> Result<Vec<crate::scene::Item>, super::layered::LayoutError> {
    use crate::scene::*;
    let padding_x = constant(profile, "padding_x")?;
    let padding_y = constant(profile, "padding_y")?;
    let pieces: Vec<&str> = text.split('\n').collect();
    let gap = match profile {
        Profile::Vector if pieces.len() > 2 => padding_y / 2,
        _ => 0,
    };
    let rows = pieces
        .iter()
        .map(|piece| run_lines(piece, profile).map_err(layout_error))
        .collect::<Result<Vec<_>, super::layered::LayoutError>>()?;
    let header_rows = rows.iter().take(2).try_fold(0i32, |sum, lines| {
        let count = i32::try_from(lines.len()).map_err(|_| GeomError::Overflow)?;
        sum.checked_add(count).ok_or(GeomError::Overflow)
    });
    let x = rect
        .x
        .checked_add(padding_x / 2)
        .ok_or(GeomError::Overflow)?;
    let top = rect
        .y
        .checked_add((padding_y - gap) / 2)
        .ok_or(GeomError::Overflow)?;
    let width = rect.w.checked_sub(padding_x).ok_or(GeomError::Overflow)?;
    let height = line_height(profile);
    let divider = if gap > 0 {
        let header = header_rows.map_err(layout_error)?;
        Some(
            top.checked_add(header.checked_mul(height).ok_or(GeomError::Overflow)?)
                .and_then(|shifted| shifted.checked_add(gap / 2))
                .ok_or(GeomError::Overflow)?,
        )
    } else {
        None
    };
    let mut items = table_outline(rect, divider)?;
    let mut y = top;
    for (index, lines) in rows.iter().enumerate() {
        if index == 2 {
            y = y.checked_add(gap).ok_or(GeomError::Overflow)?;
        }
        let span = i32::try_from(lines.len())
            .map_err(|_| GeomError::Overflow)?
            .checked_mul(height)
            .ok_or(GeomError::Overflow)?;
        items.push(Item::Text(TextItem {
            rect: Rect {
                x,
                y,
                w: width,
                h: span,
            },
            role: TextRole::Label,
            size: 14,
            align: if index < 2 {
                Align::Middle
            } else {
                Align::Start
            },
            style: TextStyle::Text,
            series: 0,
            lines: lines.clone(),
        }));
        y = y.checked_add(span).ok_or(GeomError::Overflow)?;
    }
    Ok(items)
}

fn table_outline(rect: Rect, divider: Option<i32>) -> Result<Vec<crate::scene::Item>, GeomError> {
    use crate::scene::*;
    let mut items = vec![Item::Rect(RectItem {
        shape: Shape::plain(ShapeStyle::Node),
        rect,
    })];
    if let Some(y) = divider {
        let right = rect.x.checked_add(rect.w).ok_or(GeomError::Overflow)?;
        items.push(Item::Polyline(PolylineItem {
            shape: Shape::plain(ShapeStyle::Rule),
            points: vec![
                crate::geom::Point { x: rect.x, y },
                crate::geom::Point { x: right, y },
            ],
            corner: 0,
        }));
    }
    Ok(items)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unresolved_relations_are_retained_only_by_the_model() -> Result<(), &'static str> {
        let input = input(
            "requirementDiagram\nrequirement R {\n}\nR - verifies -> Missing\n",
            Profile::Cell,
        )?;
        assert_eq!(input.routes.len(), 0);
        assert_eq!(
            input
                .labels
                .iter()
                .map(|label| label.owner.as_str())
                .collect::<Vec<_>>(),
            ["R"]
        );
        Ok(())
    }

    #[test]
    fn requirements_precede_elements_and_colliding_names_get_distinct_ids()
    -> Result<(), &'static str> {
        let input = input(
            "requirementDiagram\nelement X {\n}\nelement Y {\n}\nrequirement X {\n}\nrequirement Y {\n}\nX - copies -> Y\n",
            Profile::Cell,
        )?;
        assert_eq!(
            input
                .boxes
                .iter()
                .map(|node| node.id.as_str())
                .collect::<Vec<_>>(),
            ["X", "Y", "element:0", "element:1"]
        );
        let route = input.routes.first().ok_or("missing route")?;
        assert_eq!((&*route.from, &*route.to), ("X", "Y"));
        Ok(())
    }

    #[test]
    fn all_noncontains_relationships_use_dashed_target_arrows() -> Result<(), &'static str> {
        let input = input(
            "requirementDiagram\nrequirement R {\n}\nelement E {\n}\nR - copies -> E\nR - derives -> E\nR - satisfies -> E\nR - verifies -> E\nR - refines -> E\nR - traces -> E\n",
            Profile::Vector,
        )?;
        assert_eq!(input.routes.len(), 6);
        for route in &input.routes {
            assert_eq!(
                (&*route.line, &*route.marker_start, &*route.marker_end),
                ("dashed", "none", "requirement_arrow")
            );
            assert_eq!((route.orthogonal, route.min_length), (true, 2));
        }
        assert_eq!(
            input
                .labels
                .iter()
                .filter(|label| label.owner.starts_with('e'))
                .map(|label| label.text.as_str())
                .collect::<Vec<_>>(),
            [
                "<<copies>>",
                "<<derives>>",
                "<<satisfies>>",
                "<<verifies>>",
                "<<refines>>",
                "<<traces>>"
            ]
        );
        Ok(())
    }

    #[test]
    fn vector_divider_uses_padding_without_adding_height() -> Result<(), &'static str> {
        let items = table_items(
            "<<Element>>\nE\nType: service",
            Rect {
                x: 0,
                y: 0,
                w: 20000,
                h: 5120,
            },
            Profile::Vector,
        )
        .map_err(|_| "table items")?;
        let dividers = items
            .iter()
            .filter_map(|item| match item {
                crate::scene::Item::Polyline(line) => Some(line),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(dividers.len(), 1);
        let divider = dividers.first().ok_or("missing divider")?;
        assert_eq!(
            divider.points,
            [
                crate::geom::Point { x: 0, y: 3200 },
                crate::geom::Point { x: 20000, y: 3200 }
            ]
        );
        let rows = items
            .iter()
            .filter_map(|item| match item {
                crate::scene::Item::Text(text) => Some(text.rect.y),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(rows, [320, 1600, 3520]);
        Ok(())
    }

    #[test]
    fn layered_pipeline_returns_requirement_table_groups() -> Result<(), &'static str> {
        let input = input(
            "requirementDiagram\nrequirement R {\n}\nelement E {\n}\nR - contains -> E\n",
            Profile::Cell,
        )?;
        let (scene, _) = layout(&input).map_err(|_| "requirement layout")?;
        assert_eq!(
            scene
                .boxes()
                .iter()
                .map(|node| node.id.as_str())
                .collect::<Vec<_>>(),
            ["R", "E"]
        );
        let group = scene
            .items()
            .iter()
            .find(|group| group.owner == "R")
            .ok_or("missing table group")?;
        assert_eq!(
            group
                .items
                .iter()
                .filter(|item| matches!(item, crate::scene::Item::Text(_)))
                .count(),
            2
        );
        Ok(())
    }

    #[test]
    fn requirement_rows_carry_flags_and_math_stays_opaque() -> Result<(), &'static str> {
        let rect = Rect {
            x: 0,
            y: 0,
            w: 4000,
            h: 4000,
        };
        let lines_of = |source: &str| -> Result<Vec<Vec<Vec<crate::scene::Run>>>, &'static str> {
            let items = table_items(source, rect, Profile::Vector).map_err(|_| "items")?;
            Ok(items
                .iter()
                .filter_map(|item| match item {
                    crate::scene::Item::Text(text) => Some(text.lines.clone()),
                    _ => None,
                })
                .collect())
        };
        let heading = vec![vec![
            crate::scene::Run {
                text: "H".into(),
                bold: true,
                italic: false,
            },
            crate::scene::Run {
                text: " ".into(),
                bold: false,
                italic: false,
            },
            crate::scene::Run {
                text: "i".into(),
                bold: false,
                italic: true,
            },
        ]];
        assert_eq!(
            lines_of("**H** *i*\nR\nf")?
                .first()
                .ok_or("missing heading")?,
            &heading
        );
        let math = lines_of("$$x$$\nR\nf")?;
        let run = math
            .first()
            .and_then(|lines| lines.first())
            .and_then(|line| line.first())
            .ok_or("missing math run")?;
        assert_eq!(
            (run.text.as_str(), run.bold, run.italic),
            ("$$x$$", false, false)
        );
        Ok(())
    }

    #[test]
    fn requirement_escapes_and_forced_breaks_affect_size_and_lines() -> Result<(), &'static str> {
        let profile = Profile::Vector;
        let px = constant(profile, "padding_x").map_err(|_| "padding_x")?;
        let py = constant(profile, "padding_y").map_err(|_| "padding_y")?;
        let height = line_height(profile);
        let star = crate::measure::vector_width("*x", 14, crate::measure::Weight::Semibold)
            .map_err(|_| "width")?;
        assert_eq!(
            table_size(r"\*x", profile).map_err(|_| "size")?,
            Size {
                w: star + px,
                h: height + py
            }
        );
        let a = crate::measure::vector_width("a", 14, crate::measure::Weight::Semibold)
            .map_err(|_| "width")?;
        let b = crate::measure::vector_width("b", 14, crate::measure::Weight::Semibold)
            .map_err(|_| "width")?;
        assert_eq!(
            table_size("a<br>b", profile).map_err(|_| "size")?,
            Size {
                w: a.max(b) + px,
                h: 2 * height + py
            }
        );
        let items = table_items(
            "a<br>b\nhead\nfield",
            Rect {
                x: 0,
                y: 0,
                w: 20000,
                h: 20000,
            },
            profile,
        )
        .map_err(|_| "items")?;
        let dividers = items
            .iter()
            .filter_map(|item| match item {
                crate::scene::Item::Polyline(line) => Some(line.points.clone()),
                _ => None,
            })
            .collect::<Vec<_>>();
        let start_y = (py - py / 2) / 2;
        assert_eq!(dividers.len(), 1);
        assert_eq!(
            dividers
                .first()
                .and_then(|points| points.first())
                .map(|point| point.y),
            Some(start_y + 3 * height + py / 4)
        );
        let rows = items
            .iter()
            .filter_map(|item| match item {
                crate::scene::Item::Text(text) => {
                    Some((text.rect.y, text.rect.h, text.lines.len()))
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(
            rows,
            [
                (start_y, 2 * height, 2),
                (start_y + 2 * height, height, 1),
                (start_y + 3 * height + py / 2, height, 1)
            ]
        );
        Ok(())
    }

    fn input(source: &str, profile: Profile) -> Result<Input, &'static str> {
        let parsed = crate::syntax::requirement::parse(source, &[]);
        if !parsed.diagnostics.is_empty() {
            return Err("requirement syntax diagnostics");
        }
        let (model, diagnostics) = crate::model::requirement::resolve(source, &parsed.document);
        if !diagnostics.is_empty() {
            return Err("requirement semantic diagnostics");
        }
        from_requirement(&model, profile, DumpOptions::default()).map_err(|_| "requirement input")
    }

    #[test]
    fn requirement_table_rows_and_cell_dimensions() -> Result<(), &'static str> {
        let input = input(
            "requirementDiagram\nrequirement R {\nid: 1\ntext: hello\nrisk: low\nverifyMethod: test\n}\n",
            Profile::Cell,
        )?;
        let node = input.boxes.first().ok_or("missing requirement")?;
        assert_eq!((&*node.id, &*node.shape), ("R", "requirementBox"));
        assert_eq!(
            node.text,
            "<<Requirement>>\nR\nID: 1\nText: hello\nRisk: Low\nVerification: Test"
        );
        let Some(SizeRule::Content(size)) = input.sizes.first() else {
            return Err("missing table size");
        };
        assert_eq!(*size, Size { w: 21, h: 8 });
        Ok(())
    }

    #[test]
    fn vector_table_uses_measured_width_and_single_padding() -> Result<(), &'static str> {
        let profile = Profile::Vector;
        let size = table_size("A\nB", profile).map_err(|_| "table size")?;
        let a = crate::measure::vector_width("A", 14, crate::measure::Weight::Semibold)
            .map_err(|_| "A width")?;
        let b = crate::measure::vector_width("B", 14, crate::measure::Weight::Semibold)
            .map_err(|_| "B width")?;
        assert_eq!(
            size,
            Size {
                w: a.max(b) + 1280,
                h: 3840
            }
        );
        Ok(())
    }

    #[test]
    fn relationship_labels_strokes_markers_and_collision_ids() -> Result<(), &'static str> {
        let input = input(
            "requirementDiagram\nrequirement e0 {\n}\nelement E {\n}\ne0 - contains -> E\nE - satisfies -> e0\n",
            Profile::Cell,
        )?;
        let routes = input
            .routes
            .iter()
            .map(|r| {
                (
                    r.id.as_str(),
                    r.line.as_str(),
                    r.marker_start.as_str(),
                    r.marker_end.as_str(),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(
            routes,
            [
                ("e1", "normal", "requirement_contains", "none"),
                ("e2", "dashed", "none", "requirement_arrow")
            ]
        );
        assert_eq!(
            input
                .labels
                .iter()
                .filter(|l| l.owner.starts_with('e') && l.text.starts_with("<<"))
                .map(|l| l.text.as_str())
                .collect::<Vec<_>>(),
            ["<<Requirement>>\ne0", "<<contains>>", "<<satisfies>>"]
        );
        Ok(())
    }

    #[test]
    fn table_scene_preserves_rows_inside_cell_borders() -> Result<(), &'static str> {
        let items = table_items(
            "<<Element>>\nE\nType: service",
            Rect {
                x: 0,
                y: 0,
                w: 16,
                h: 5,
            },
            Profile::Cell,
        )
        .map_err(|_| "table items")?;
        let text = items
            .iter()
            .filter_map(|item| match item {
                crate::scene::Item::Text(text) => Some(text),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(
            text.iter().map(|text| text.rect.y).collect::<Vec<_>>(),
            [1, 2, 3]
        );
        assert_eq!(
            text.first().ok_or("missing heading")?.align,
            crate::scene::Align::Middle
        );
        assert_eq!(
            text.last().ok_or("missing body")?.align,
            crate::scene::Align::Start
        );
        Ok(())
    }
}
