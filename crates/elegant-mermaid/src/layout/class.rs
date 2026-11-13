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
            .push(SizeRule::Content(compartment_size(&rows, profile)?));
        input.boxes.push(Box {
            id: class.id.clone(),
            role: BoxRole::Node,
            shape: "classBox".into(),
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
    let padding = i64::from(constant(profile, "padding")?);
    let separator = i64::from(constant(profile, "separator")?);
    let mut width = 0i64;
    let mut rows = 0i64;
    for compartment in compartments {
        rows = rows
            .checked_add(i64::try_from(compartment.len().max(1)).map_err(|_| GeomError::Overflow)?)
            .ok_or(GeomError::Overflow)?;
        for row in compartment {
            width = width.max(i64::from(text_width(row, profile)?));
        }
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

fn text_width(text: &str, profile: Profile) -> Result<i32, GeomError> {
    match profile {
        Profile::Cell => crate::measure::cell_width(text),
        Profile::Vector => crate::measure::vector_width(text, 14, crate::measure::Weight::Semibold),
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
    rect: crate::geom::Rect,
    profile: Profile,
) -> Result<Vec<crate::scene::Item>, super::layered::LayoutError> {
    use crate::scene::*;
    struct TableItems {
        items: Vec<Item>,
        texts: Vec<Item>,
        cell: bool,
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
            let lines = if compartment.is_empty() {
                Vec::new()
            } else {
                compartment
                    .split('\n')
                    .map(|line| vec![Run::plain(line)])
                    .collect::<Vec<_>>()
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
                role: TextRole::Label,
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
}
