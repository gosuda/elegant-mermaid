use super::input::{Box, Group, Input, Label, Route, SizeRule};
use crate::{
    geom::{GeomError, Size},
    model::class::Model,
    scene::{BoxRole, Direction, DumpOptions, Profile, TextRole},
};

pub fn from_class(
    model: &Model,
    profile: Profile,
    options: DumpOptions,
) -> Result<Input, GeomError> {
    let mut input = Input {
        kind: "class",
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
    append_classes(&mut input, model, profile)?;
    append_notes(&mut input, model);
    append_namespaces(&mut input, model);
    input.labels = input
        .boxes
        .iter()
        .filter(|node| node.text != node.id)
        .map(|node| Label {
            id: format!("{}.label", node.id),
            owner: node.id.clone(),
            role: TextRole::Label,
            text: node.text.clone(),
        })
        .collect();
    append_relations(&mut input, model);
    Ok(input)
}

fn append_classes(input: &mut Input, model: &Model, profile: Profile) -> Result<(), GeomError> {
    let font_family = crate::scene::has_font_family(&input.options.config);
    for class in &model.classes {
        let rows = class.rows();
        let text = rows
            .iter()
            .map(|rows| {
                if rows.is_empty() {
                    String::new()
                } else {
                    rows.join("\n")
                }
            })
            .collect::<Vec<_>>()
            .join("\n\n");
        input
            .sizes
            .push(SizeRule::Content(compartment_size_with_font_family(
                &rows,
                profile,
                font_family,
            )?));
        input.boxes.push(Box {
            id: class.id.clone(),
            role: BoxRole::Node,
            shape: "classBox".into(),
            icon: false,
            parent: class.parent.clone(),
            exclusive: true,
            text,
            direction: String::new(),
        });
    }
    Ok(())
}

fn append_notes(input: &mut Input, model: &Model) {
    for note in &model.notes {
        input.sizes.push(SizeRule::Measured);
        input.boxes.push(Box {
            id: note.id.clone(),
            role: BoxRole::Node,
            shape: "note".into(),
            icon: false,
            parent: note.parent.clone(),
            exclusive: true,
            text: note.text.clone(),
            direction: String::new(),
        });
    }
}

fn append_namespaces(input: &mut Input, model: &Model) {
    for namespace in &model.namespaces {
        input.boxes.push(Box {
            id: namespace.id.clone(),
            role: BoxRole::Group,
            shape: String::new(),
            icon: false,
            parent: namespace.parent.clone(),
            exclusive: false,
            text: namespace.label.clone(),
            direction: String::new(),
        });
        input.groups.push(Group {
            id: namespace.id.clone(),
            parent: namespace.parent.clone(),
            direction: String::new(),
            direction_span: crate::source::Span { start: 0, end: 0 },
        });
    }
}

fn append_relations(input: &mut Input, model: &Model) {
    let ids = route_ids(&input.boxes, model.relations.len() + model.notes.len());
    for (index, relation) in model.relations.iter().enumerate() {
        let id = ids[index].clone();
        if !relation.label.is_empty() {
            input.labels.push(Label {
                id: format!("{id}.label"),
                owner: id.clone(),
                role: TextRole::Label,
                text: relation.label.clone(),
            });
        }
        input.routes.push(Route {
            id,
            from: relation.from.clone(),
            to: relation.to.clone(),
            orthogonal: true,
            marker_start: relation.marker_start.clone(),
            marker_end: relation.marker_end.clone(),
            line: if relation.dashed { "dashed" } else { "normal" }.into(),
            min_length: 1,
            from_side: None,
            to_side: None,
        });
    }
    for (index, note) in model
        .notes
        .iter()
        .enumerate()
        .filter(|(_, note)| !note.target.is_empty())
    {
        input.routes.push(Route {
            id: ids[model.relations.len() + index].clone(),
            from: note.id.clone(),
            to: note.target.clone(),
            orthogonal: true,
            marker_start: "none".into(),
            marker_end: "none".into(),
            line: "dashed".into(),
            min_length: 1,
            from_side: None,
            to_side: None,
        });
    }
}

fn route_ids(boxes: &[Box], count: usize) -> Vec<String> {
    let mut next = 0usize;
    let mut ids = Vec::with_capacity(count);
    while ids.len() < count {
        let id = format!("e{next}");
        next += 1;
        if !boxes.iter().any(|node| node.id == id) {
            ids.push(id);
        }
    }
    ids
}

fn constant(profile: Profile, name: &str) -> Result<i32, GeomError> {
    let key = format!("{}.class.{name}", profile.as_str());
    crate::r#gen::layoutconst::LAYOUT_CONST
        .iter()
        .find(|row| row.name == key)
        .map(|row| row.value)
        .ok_or(GeomError::Domain)
}

pub fn compartment_size(compartments: &[Vec<String>], profile: Profile) -> Result<Size, GeomError> {
    compartment_size_with_font_family(compartments, profile, false)
}

fn compartment_size_with_font_family(
    compartments: &[Vec<String>],
    profile: Profile,
    font_family: bool,
) -> Result<Size, GeomError> {
    let padding = i64::from(constant(profile, "padding")?);
    let separator = i64::from(constant(profile, "separator")?);
    let mut width = 0i64;
    let mut rows = 0i64;
    for (index, compartment) in compartments.iter().enumerate() {
        let mut compartment_rows = 0i64;
        for row in compartment {
            let lines = piece_lines(row, profile, compartment_role(index), font_family)?;
            compartment_rows = compartment_rows
                .checked_add(i64::try_from(lines.len().max(1)).map_err(|_| GeomError::Overflow)?)
                .ok_or(GeomError::Overflow)?;
            for line in &lines {
                width = width.max(i64::from(line.width));
            }
        }
        rows = rows
            .checked_add(compartment_rows.max(1))
            .ok_or(GeomError::Overflow)?;
    }
    let line_height = if profile == Profile::Cell {
        1
    } else {
        crate::measure::Role::Label.line_height_px() * 64
    };
    let count =
        i64::try_from(compartments.len().saturating_sub(1)).map_err(|_| GeomError::Overflow)?;
    let height = rows
        .checked_mul(i64::from(line_height))
        .and_then(|h| count.checked_mul(separator).and_then(|s| h.checked_add(s)))
        .ok_or(GeomError::Overflow)?;
    let height = height
        .checked_add(if profile == Profile::Cell { 2 } else { 0 })
        .ok_or(GeomError::Overflow)?;
    Ok(Size {
        w: i32::try_from(width + 2 * padding).map_err(|_| GeomError::Overflow)?,
        h: i32::try_from(height).map_err(|_| GeomError::Overflow)?,
    })
}

fn compartment_role(index: usize) -> crate::measure::Role {
    if index == 0 {
        crate::measure::Role::Label
    } else {
        crate::measure::Role::Body
    }
}

fn metric(
    profile: Profile,
    role: crate::measure::Role,
    font_family: bool,
) -> crate::measure::Metric {
    let metric = if profile == Profile::Cell {
        crate::measure::Metric::Cell
    } else {
        crate::measure::Metric::for_role(role)
    };
    if font_family {
        metric.with_font_family()
    } else {
        metric
    }
}

/// The styled lines of one structural text piece: accepted br tags force
/// lines (math-05), bold and italic runs measure at their own weights
/// (math-03, math-04), escapes lose their backslash, unsupported markup
/// stays literal (math-07, math-08), and math spans stay opaque. An empty
/// piece yields no line.
fn piece_lines<'a>(
    piece: &'a str,
    profile: Profile,
    role: crate::measure::Role,
    font_family: bool,
) -> Result<Vec<crate::measure::StyledLine<'a>>, GeomError> {
    crate::measure::styled_lines(piece, i32::MAX, metric(profile, role, font_family))
}

/// The scene runs of one structural text piece: one line per styled line,
/// each carrying its bold and italic flags. An empty piece keeps one empty
/// plain line, so plain rows emit exactly what `Run::plain` emitted.
fn run_lines(
    piece: &str,
    profile: Profile,
    role: crate::measure::Role,
    font_family: bool,
) -> Result<Vec<Vec<crate::scene::Run>>, GeomError> {
    let lines = piece_lines(piece, profile, role, font_family)?;
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
        if node.shape == "note" {
            for item in &mut group.items {
                if let crate::scene::Item::Rect(rect) = item {
                    rect.shape.style = crate::scene::ShapeStyle::Note;
                }
            }
        }
        if node.shape != "classBox" {
            continue;
        }
        let Some(bounds) = scene.boxes().iter().find(|bounds| bounds.id == group.owner) else {
            continue;
        };
        group.items = table_items(
            &node.text,
            bounds.rect,
            input.profile,
            crate::scene::has_font_family(&input.options.config),
        )?;
    }
    Ok(crate::scene::Scene::new(
        scene.canvas(),
        scene.dump_part().clone(),
        groups,
    ))
}

fn table_items(
    text: &str,
    rect: crate::geom::Rect,
    profile: Profile,
    font_family: bool,
) -> Result<Vec<crate::scene::Item>, super::layered::LayoutError> {
    use crate::scene::*;
    struct TableItems {
        items: Vec<Item>,
        texts: Vec<Item>,
        cell: bool,
        profile: Profile,
        font_family: bool,
        line_height: i32,
        separator: i32,
        padding: i32,
        y: i32,
    }
    impl TableItems {
        fn append(
            &mut self,
            index: usize,
            compartment: &str,
            rect: crate::geom::Rect,
        ) -> Result<(), super::layered::LayoutError> {
            if index > 0 {
                let right = rect
                    .x
                    .checked_add(rect.w - i32::from(self.cell))
                    .ok_or(super::layered::LayoutError::Overflow)?;
                self.items.push(Item::Polyline(PolylineItem {
                    shape: Shape::plain(ShapeStyle::Rule),
                    points: vec![
                        crate::geom::Point {
                            x: rect.x,
                            y: self.y,
                        },
                        crate::geom::Point {
                            x: right,
                            y: self.y,
                        },
                    ],
                    corner: 0,
                }));
                self.y = self
                    .y
                    .checked_add(self.separator)
                    .ok_or(super::layered::LayoutError::Overflow)?;
            }
            let role = compartment_role(index);
            let lines = if compartment.is_empty() {
                Vec::new()
            } else {
                let mut lines = Vec::new();
                for piece in compartment.split('\n') {
                    lines.extend(
                        run_lines(piece, self.profile, role, self.font_family)
                            .map_err(layout_error)?,
                    );
                }
                lines
            };
            let height = i32::try_from(lines.len().max(1))
                .ok()
                .and_then(|n| n.checked_mul(self.line_height))
                .ok_or(super::layered::LayoutError::Overflow)?;
            let x = rect
                .x
                .checked_add(self.padding)
                .ok_or(super::layered::LayoutError::Overflow)?;
            let width = rect
                .w
                .checked_sub(2 * self.padding)
                .ok_or(super::layered::LayoutError::Overflow)?;
            self.texts.push(Item::Text(TextItem {
                rect: crate::geom::Rect {
                    x,
                    y: self.y,
                    w: width,
                    h: height,
                },
                role: match role {
                    crate::measure::Role::Label => TextRole::Label,
                    crate::measure::Role::Body => TextRole::Body,
                    crate::measure::Role::Title => TextRole::Title,
                },
                size: 14,
                align: Align::Start,
                style: TextStyle::Text,
                series: 0,
                lines,
            }));
            self.y = self
                .y
                .checked_add(height)
                .ok_or(super::layered::LayoutError::Overflow)?;
            Ok(())
        }
    }
    let items = vec![Item::Rect(RectItem {
        shape: Shape::plain(ShapeStyle::Node),
        rect,
    })];
    let texts = Vec::new();
    let cell = profile == Profile::Cell;
    let line_height = if cell { 1 } else { 1280 };
    let separator =
        constant(profile, "separator").map_err(|_| super::layered::LayoutError::Domain)?;
    let padding = constant(profile, "padding").map_err(|_| super::layered::LayoutError::Domain)?;
    let y = rect
        .y
        .checked_add(i32::from(cell))
        .ok_or(super::layered::LayoutError::Overflow)?;
    let mut table = TableItems {
        items,
        texts,
        cell,
        profile,
        font_family,
        line_height,
        separator,
        padding,
        y,
    };
    for (index, compartment) in text.split("\n\n").enumerate() {
        table.append(index, compartment, rect)?;
    }
    table.items.extend(table.texts);
    Ok(table.items)
}

#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests {
    use super::*;
    #[test]
    fn class_default_stroke() {
        let source = "classDiagram\nA --> B\nA ..> B\n";
        let parsed = crate::syntax::class::parse(source, &[]);
        assert!(
            parsed.diagnostics.is_empty(),
            "class_default_stroke: input violates parsed.diagnostics.is_empty(); observed {:?}",
            parsed.diagnostics
        );
        let (model, diagnostics) = crate::model::class::resolve(source, &parsed.document);
        assert!(
            diagnostics.is_empty(),
            "class_default_stroke: input violates diagnostics.is_empty(); observed {:?}",
            diagnostics
        );
        let input = from_class(&model, Profile::Vector, DumpOptions::default()).unwrap();
        assert_eq!(input.routes[0].line, "normal");
        assert_eq!(input.routes[1].line, "dashed");
    }
    #[test]
    fn class_compartment_size() {
        let rows = vec![
            vec!["Account".into()],
            vec!["+name".into(), "+balance".into()],
            vec![],
        ];
        assert_eq!(
            compartment_size(&rows, Profile::Cell).unwrap(),
            Size { w: 12, h: 8 }
        );
    }
    #[test]
    fn class_empty_vector_compartments() {
        assert_eq!(
            compartment_size(&[Vec::new(), Vec::new(), Vec::new()], Profile::Vector).unwrap(),
            Size { w: 2048, h: 3968 }
        );
    }
    #[test]
    fn class_rows_measure_rendered_runs_and_force_lines() {
        let padding = constant(Profile::Vector, "padding").unwrap();
        let line_height = crate::measure::Role::Label.line_height_px() * 64;
        let hot =
            crate::measure::vector_width("hot", 14, crate::measure::Weight::Semibold).unwrap();
        assert_eq!(
            compartment_size(&[vec!["**hot**".into()]], Profile::Vector).unwrap(),
            Size {
                w: hot + 2 * padding,
                h: line_height
            }
        );
        let a = crate::measure::vector_width("a", 14, crate::measure::Weight::Semibold).unwrap();
        let b = crate::measure::vector_width("b", 14, crate::measure::Weight::Semibold).unwrap();
        assert_eq!(
            compartment_size(&[vec!["a<br>b".into()]], Profile::Vector).unwrap(),
            Size {
                w: a.max(b) + 2 * padding,
                h: 2 * line_height
            }
        );
        let items = table_items(
            "a<br>b",
            crate::geom::Rect {
                x: 0,
                y: 0,
                w: 4000,
                h: 4000,
            },
            Profile::Vector,
            false,
        )
        .unwrap();
        let text = items
            .iter()
            .filter_map(|item| match item {
                crate::scene::Item::Text(text) => Some(text.clone()),
                _ => None,
            })
            .next()
            .unwrap();
        assert_eq!(
            text.lines
                .iter()
                .map(|line| line.iter().map(|run| run.text.as_str()).collect::<Vec<_>>())
                .collect::<Vec<_>>(),
            [["a"], ["b"]]
        );
    }
    #[test]
    fn class_runs_carry_flags_and_markup_edges() {
        let rect = crate::geom::Rect {
            x: 0,
            y: 0,
            w: 8000,
            h: 8000,
        };
        let first_text = |text: &str| {
            table_items(text, rect, Profile::Vector, false)
                .unwrap()
                .iter()
                .filter_map(|item| match item {
                    crate::scene::Item::Text(text) => Some(text.clone()),
                    _ => None,
                })
                .next()
                .unwrap()
        };
        assert_eq!(
            first_text("**b** *i* tail").lines,
            vec![vec![
                crate::scene::Run {
                    text: "b".into(),
                    bold: true,
                    italic: false
                },
                crate::scene::Run {
                    text: " ".into(),
                    bold: false,
                    italic: false
                },
                crate::scene::Run {
                    text: "i".into(),
                    bold: false,
                    italic: true
                },
                crate::scene::Run {
                    text: " tail".into(),
                    bold: false,
                    italic: false
                },
            ]]
        );
        assert_eq!(
            first_text(r"a\*b").lines,
            vec![vec![
                crate::scene::Run {
                    text: "a".into(),
                    bold: false,
                    italic: false
                },
                crate::scene::Run {
                    text: "*".into(),
                    bold: false,
                    italic: false
                },
                crate::scene::Run {
                    text: "b".into(),
                    bold: false,
                    italic: false
                },
            ]]
        );
        assert_eq!(
            first_text("a_b *x").lines,
            vec![vec![crate::scene::Run {
                text: "a_b *x".into(),
                bold: false,
                italic: false
            }]]
        );
        assert_eq!(
            first_text("**b** $$\\frac{a}{b}$$").lines,
            vec![vec![
                crate::scene::Run {
                    text: "b".into(),
                    bold: true,
                    italic: false
                },
                crate::scene::Run {
                    text: " ".into(),
                    bold: false,
                    italic: false
                },
                crate::scene::Run {
                    text: "$$\\frac{a}{b}$$".into(),
                    bold: false,
                    italic: false
                },
            ]]
        );
    }
    #[test]
    fn class_cell_profile_measures_rendered_cells_but_keeps_flags() {
        let padding = constant(Profile::Cell, "padding").unwrap();
        let ab = crate::measure::cell_width("ab").unwrap();
        assert_eq!(
            compartment_size(&[vec!["**ab**".into()]], Profile::Cell).unwrap(),
            Size {
                w: ab + 2 * padding,
                h: 3
            }
        );
        assert_eq!(
            compartment_size(&[vec!["a<br>b".into()]], Profile::Cell)
                .unwrap()
                .h,
            4
        );
        let items = table_items(
            "**ab**",
            crate::geom::Rect {
                x: 0,
                y: 0,
                w: 4000,
                h: 4000,
            },
            Profile::Cell,
            false,
        )
        .unwrap();
        let text = items
            .iter()
            .filter_map(|item| match item {
                crate::scene::Item::Text(text) => Some(text.clone()),
                _ => None,
            })
            .next()
            .unwrap();
        assert_eq!(
            text.lines,
            vec![vec![crate::scene::Run {
                text: "ab".into(),
                bold: true,
                italic: false
            }]]
        );
    }
    fn member_advance_width(segments: &[(&str, u8)]) -> i32 {
        let upem = crate::r#gen::advancesupem::ADVANCES_UPEM;
        let denominator = i64::from(upem[0]) * i64::from(upem[1]);
        let numerator: i64 = segments
            .iter()
            .map(|&(text, weight)| {
                let units: i64 = text
                    .chars()
                    .map(|ch| {
                        i64::from(
                            crate::r#gen::advances::ADVANCES
                                .iter()
                                .find(|row| row.weight == weight && row.cp == u32::from(ch))
                                .unwrap()
                                .units,
                        )
                    })
                    .sum();
                units * 14 * 64 * (denominator / i64::from(upem[usize::from(weight)]))
            })
            .sum();
        i32::try_from((numerator + denominator - 1) / denominator).unwrap()
    }

    #[test]
    fn class_member_roles_measure_and_render_at_declared_weights() {
        let rendered = "+AAAAAAAAx";
        for (member, bold, italic) in [
            ("+AAAAAAAAx", false, false),
            ("+**AAAAAAAA**x", true, false),
            ("+*AAAAAAAA*x", false, true),
        ] {
            let segments = [("+", 0), ("AAAAAAAA", u8::from(bold)), ("x", 0)];
            let expected_runs = if bold || italic {
                vec![
                    crate::scene::Run {
                        text: "+".into(),
                        bold: false,
                        italic: false,
                    },
                    crate::scene::Run {
                        text: "AAAAAAAA".into(),
                        bold,
                        italic,
                    },
                    crate::scene::Run {
                        text: "x".into(),
                        bold: false,
                        italic: false,
                    },
                ]
            } else {
                vec![crate::scene::Run {
                    text: rendered.into(),
                    bold: false,
                    italic: false,
                }]
            };
            let source = format!("classDiagram\nclass C {{\n{member}\n}}\n");
            let parsed = crate::syntax::class::parse(&source, &[]);
            let (model, _) = crate::model::class::resolve(&source, &parsed.document);
            for profile in [Profile::Vector, Profile::Cell] {
                let input = from_class(&model, profile, DumpOptions::default()).unwrap();
                let (scene, _) = layout(&input).unwrap();
                let expected_width = if profile == Profile::Vector {
                    member_advance_width(&[("C", 1)]).max(member_advance_width(&segments))
                        + 2 * 1024
                } else {
                    10 + 2 * 2
                };
                assert_eq!(scene.boxes()[0].rect.w, expected_width);
                let texts = scene
                    .items()
                    .iter()
                    .flat_map(|group| &group.items)
                    .filter_map(|item| match item {
                        crate::scene::Item::Text(text) => Some(text),
                        _ => None,
                    })
                    .collect::<Vec<_>>();
                assert_eq!(texts[0].role, crate::scene::TextRole::Label);
                assert_eq!(
                    texts[0].lines,
                    vec![vec![crate::scene::Run {
                        text: "C".into(),
                        bold: false,
                        italic: false,
                    }]]
                );
                let member_text = texts
                    .iter()
                    .find(|text| {
                        text.lines
                            .iter()
                            .flatten()
                            .map(|run| run.text.as_str())
                            .collect::<String>()
                            == rendered
                    })
                    .unwrap();
                assert_eq!(member_text.role, crate::scene::TextRole::Body);
                assert_eq!(
                    member_text.rect.w,
                    expected_width
                        - if profile == Profile::Vector {
                            2 * 1024
                        } else {
                            2 * 2
                        }
                );
                assert_eq!(member_text.lines, vec![expected_runs.clone()]);
            }
        }
    }
}
