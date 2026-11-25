use super::input::{Box, Group, Input, Label, Route, SizeRule};
use crate::{
    geom::{GeomError, Point, Rect, Size},
    model::er::{Model, Target},
    scene::{BoxRole, Direction, DumpOptions, Profile, TextRole},
};

type LayoutError = super::layered::LayoutError;

pub fn from_er(model: &Model, profile: Profile, options: DumpOptions) -> Result<Input, GeomError> {
    let mut input = Input {
        kind: "er",
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
        spacing: Default::default(),
    };
    let group_ids = group_ids(model);
    let font_family = crate::scene::has_font_family(&input.options.config);
    for entity in &model.entities {
        if model.groups.iter().any(|group| group.id == entity.id) {
            continue;
        }
        let text = table_text(entity);
        input
            .sizes
            .push(SizeRule::Content(table_size(&text, profile, font_family)?));
        input.boxes.push(Box {
            id: entity.id.clone(),
            role: BoxRole::Node,
            shape: "erBox".into(),
            icon: false,
            parent: parent_id(entity.parent, &group_ids),
            exclusive: true,
            text,
            direction: String::new(),
        });
    }
    append_groups(&mut input, model, &group_ids);
    append_relationships(&mut input, model, &group_ids);
    Ok(input)
}

fn group_ids(model: &Model) -> Vec<String> {
    let mut ids = Vec::with_capacity(model.groups.len());
    for (index, group) in model.groups.iter().enumerate() {
        let mut id = group.id.clone();
        let mut ordinal = index;
        while ids.contains(&id)
            || model
                .entities
                .iter()
                .any(|entity| entity.id == id && id != group.id)
            || model
                .groups
                .iter()
                .any(|other| other.id == id && id != group.id)
        {
            id = format!("{}.group{ordinal}", group.id);
            ordinal += 1;
        }
        ids.push(id);
    }
    ids
}

fn parent_id(parent: Option<usize>, ids: &[String]) -> String {
    parent
        .and_then(|index| ids.get(index))
        .cloned()
        .unwrap_or_default()
}

fn append_groups(input: &mut Input, model: &Model, ids: &[String]) {
    for (group, id) in model.groups.iter().zip(ids) {
        let parent = parent_id(group.parent, ids);
        input.boxes.push(Box {
            id: id.clone(),
            role: BoxRole::Group,
            shape: String::new(),
            icon: false,
            parent: parent.clone(),
            exclusive: false,
            text: label_lines(&group.label),
            direction: group.direction.clone(),
        });
        input.groups.push(Group {
            id: id.clone(),
            parent,
            direction: group.direction.clone(),
            direction_span: group.direction_span,
        });
    }
}

fn target_id(model: &Model, target: Target, groups: &[String]) -> String {
    match target {
        Target::Group(index) => groups.get(index).cloned().unwrap_or_default(),
        Target::Entity(index) => {
            let Some(entity) = model.entities.get(index) else {
                return String::new();
            };
            model
                .groups
                .iter()
                .rposition(|group| group.id == entity.id)
                .and_then(|index| groups.get(index))
                .cloned()
                .unwrap_or_else(|| entity.id.clone())
        }
    }
}

fn append_relationships(input: &mut Input, model: &Model, groups: &[String]) {
    let mut ordinal = 0usize;
    for relation in &model.relationships {
        let mut id = format!("e{ordinal}");
        while input.boxes.iter().any(|node| node.id == id) {
            ordinal += 1;
            id = format!("e{ordinal}");
        }
        ordinal += 1;
        if !relation.label.is_empty() {
            input.labels.push(Label {
                id: format!("{id}.label"),
                owner: id.clone(),
                role: TextRole::Label,
                text: label_lines(&relation.label),
            });
        }
        input.routes.push(Route {
            id,
            from: target_id(model, relation.from_target, groups),
            to: target_id(model, relation.to_target, groups),
            orthogonal: true,
            marker_start: relation.marker_start.into(),
            marker_end: relation.marker_end.into(),
            line: if relation.identifying {
                "normal"
            } else {
                "dashed"
            }
            .into(),
            min_length: 1,
            from_side: None,
            to_side: None,
        });
    }
}

fn label_lines(text: &str) -> String {
    let mut output = String::with_capacity(text.len());
    let mut characters = text.chars().peekable();
    while let Some(character) = characters.next() {
        if character == '\r' && characters.peek() == Some(&'\n') {
            continue;
        }
        match character {
            '\r' | '\n' => output.push_str("<br/>"),
            _ => output.push(character),
        }
    }
    output
}

fn table_text(entity: &crate::model::er::Entity) -> String {
    let rows = entity
        .table_rows()
        .iter()
        .map(|row| {
            row.iter()
                .map(|field| encode_field(field))
                .collect::<Vec<_>>()
                .join("|")
        })
        .collect::<Vec<_>>();
    format!(
        "{}<br/><br/>{}",
        encode_field(&entity.display_name()),
        rows.join("<br/>")
    )
}

fn encode_field(text: &str) -> String {
    let mut output = String::with_capacity(text.len());
    let mut characters = text.chars();
    while let Some(character) = characters.next() {
        if let Some(length) = break_length(character, characters.as_str()) {
            output.push_str("\\n");
            characters = characters.as_str().get(length..).unwrap_or("").chars();
            continue;
        }
        match character {
            '\\' => output.push_str("\\\\"),
            '|' => output.push_str("\\p"),
            '<' => output.push_str("\\l"),
            '\t' => output.push_str("\\t"),
            '\n' => output.push_str("\\n"),
            _ => output.push(character),
        }
    }
    output
}

fn break_length(character: char, tail: &str) -> Option<usize> {
    if character != '<' {
        return None;
    }
    ["br>", "br/>", "br />"].iter().find_map(|ending| {
        tail.get(..ending.len())
            .filter(|prefix| prefix.eq_ignore_ascii_case(ending))
            .map(str::len)
    })
}

fn decode_field(text: &str) -> String {
    let mut output = String::with_capacity(text.len());
    let mut characters = text.chars();
    while let Some(character) = characters.next() {
        if character != '\\' {
            output.push(character);
            continue;
        }
        match characters.next() {
            Some('n') => output.push('\n'),
            Some('t') => output.push('\t'),
            Some('p') => output.push('|'),
            Some('l') => output.push('<'),
            Some(character) => output.push(character),
            None => output.push('\\'),
        }
    }
    output
}

fn constant(profile: Profile, name: &str) -> Result<i32, GeomError> {
    let key = format!("{}.er.{name}", profile.as_str());
    crate::r#gen::layoutconst::LAYOUT_CONST
        .iter()
        .find(|row| row.name == key)
        .map(|row| row.value)
        .ok_or(GeomError::Domain)
}

fn metric(profile: Profile, font_family: bool) -> crate::measure::Metric {
    let metric = if profile == Profile::Cell {
        crate::measure::Metric::Cell
    } else {
        crate::measure::Metric::for_role(crate::measure::Role::Label)
    };
    if font_family {
        metric.with_font_family()
    } else {
        metric
    }
}

/// The styled lines of one decoded field piece: bold and italic runs
/// measure at their own weights (math-03, math-04), escapes lose their
/// backslash, unsupported markup stays literal (math-07, math-08), and math
/// spans stay opaque. An empty piece yields no line.
fn piece_lines<'a>(
    piece: &'a str,
    metric: crate::measure::Metric,
) -> Result<Vec<crate::measure::StyledLine<'a>>, GeomError> {
    crate::measure::styled_lines(piece, i32::MAX, metric)
}

/// The width of one decoded field piece: its widest styled line.
fn piece_width(piece: &str, metric: crate::measure::Metric) -> Result<i32, GeomError> {
    Ok(piece_lines(piece, metric)?
        .iter()
        .map(|line| line.width)
        .max()
        .unwrap_or(0))
}

/// The scene runs of one decoded field piece: one line per styled line,
/// each carrying its bold and italic flags. An empty piece keeps one empty
/// plain line, so plain fields emit exactly what `Run::plain` emitted.
fn run_lines(
    piece: &str,
    metric: crate::measure::Metric,
) -> Result<Vec<Vec<crate::scene::Run>>, GeomError> {
    let lines = piece_lines(piece, metric)?;
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

fn text_width(text: &str, metric: crate::measure::Metric) -> Result<i32, GeomError> {
    text.split('\n')
        .map(|piece| piece_width(piece, metric))
        .try_fold(0i32, |width, next| next.map(|next| width.max(next)))
}

fn line_height(profile: Profile) -> i32 {
    if profile == Profile::Cell {
        1
    } else {
        crate::measure::Role::Label.line_height_px() * 64
    }
}

struct Table {
    heading: String,
    rows: Vec<Vec<String>>,
    columns: Vec<(usize, i32)>,
    row_heights: Vec<i32>,
    heading_height: i32,
    padding_x: i32,
    padding_y: i32,
    separator: i32,
    metric: crate::measure::Metric,
}

impl Table {
    fn new(text: &str, profile: Profile, font_family: bool) -> Result<Self, GeomError> {
        let metric = metric(profile, font_family);
        let (heading, attributes) = text.split_once("<br/><br/>").unwrap_or((text, ""));
        let heading = decode_field(heading);
        let rows = if attributes.is_empty() {
            Vec::new()
        } else {
            attributes
                .split("<br/>")
                .map(|row| row.split('|').map(decode_field).collect::<Vec<_>>())
                .collect::<Vec<_>>()
        };
        let columns = column_widths(&rows, metric)?;
        let row_heights = rows
            .iter()
            .map(|row| row_height(row, profile))
            .collect::<Result<Vec<_>, _>>()?;
        let heading_height = row_height(std::slice::from_ref(&heading), profile)?;
        Ok(Self {
            heading,
            rows,
            columns,
            row_heights,
            heading_height,
            padding_x: constant(profile, "padding_x")?,
            padding_y: constant(profile, "padding_y")?,
            separator: i32::from(profile == Profile::Cell),
            metric,
        })
    }

    fn width(&self) -> Result<i32, GeomError> {
        let columns = self.columns.iter().try_fold(0i32, |sum, (_, width)| {
            sum.checked_add(*width).ok_or(GeomError::Overflow)
        })?;
        let gaps =
            i32::try_from(self.columns.len().saturating_sub(1)).map_err(|_| GeomError::Overflow)?;
        let gap_width = gaps
            .checked_mul(self.padding_x)
            .ok_or(GeomError::Overflow)?;
        let width = columns
            .checked_add(gap_width)
            .ok_or(GeomError::Overflow)?
            .max(text_width(&self.heading, self.metric)?);
        width
            .checked_add(self.padding_x.checked_mul(2).ok_or(GeomError::Overflow)?)
            .ok_or(GeomError::Overflow)
    }

    fn height(&self, profile: Profile) -> Result<i32, GeomError> {
        let attributes = self.row_heights.iter().try_fold(0i32, |sum, height| {
            sum.checked_add(*height).ok_or(GeomError::Overflow)
        })?;
        self.heading_height
            .checked_add(attributes.max(line_height(profile)))
            .and_then(|height| height.checked_add(self.separator))
            .and_then(|height| height.checked_add(2 * self.padding_y))
            .ok_or(GeomError::Overflow)
    }
}

fn column_widths(
    rows: &[Vec<String>],
    metric: crate::measure::Metric,
) -> Result<Vec<(usize, i32)>, GeomError> {
    let mut widths = [0i32; 4];
    for row in rows {
        for (width, field) in widths.iter_mut().zip(row) {
            *width = (*width).max(text_width(field, metric)?);
        }
    }
    Ok(widths
        .into_iter()
        .enumerate()
        .filter(|(index, width)| *index < 2 || *width > 0)
        .collect())
}

fn row_height(row: &[String], profile: Profile) -> Result<i32, GeomError> {
    let lines = row
        .iter()
        .map(|field| field.split('\n').count())
        .max()
        .unwrap_or(1);
    i32::try_from(lines)
        .ok()
        .and_then(|count| count.checked_mul(line_height(profile)))
        .ok_or(GeomError::Overflow)
}
fn table_size(text: &str, profile: Profile, font_family: bool) -> Result<Size, GeomError> {
    let table = Table::new(text, profile, font_family)?;
    Ok(Size {
        w: table.width()?.max(constant(profile, "min_width")?),
        h: table.height(profile)?.max(constant(profile, "min_height")?),
    })
}

pub fn layout(input: &Input) -> Result<(crate::scene::Scene, bool), LayoutError> {
    let edges = input
        .routes
        .iter()
        .map(|route| {
            Ok(super::layered::pipeline::EdgeOptions {
                marker_start: marker(&route.marker_start),
                marker_end: marker(&route.marker_end),
                stroke: &route.line,
                min_length: i32::try_from(route.min_length).map_err(|_| LayoutError::Overflow)?,
            })
        })
        .collect::<Result<Vec<_>, LayoutError>>()?;
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
) -> Result<crate::scene::Scene, LayoutError> {
    let mut groups = scene.items().to_vec();
    for group in &mut groups {
        let Some(node) = input
            .boxes
            .iter()
            .find(|node| node.id == group.owner && node.shape == "erBox")
        else {
            continue;
        };
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

fn rule(start: Point, end: Point) -> crate::scene::Item {
    use crate::scene::*;
    Item::Polyline(PolylineItem {
        shape: Shape::plain(ShapeStyle::Rule),
        points: vec![start, end],
        corner: 0,
    })
}

fn text_item(
    text: &str,
    rect: Rect,
    align: crate::scene::Align,
    metric: crate::measure::Metric,
) -> Result<crate::scene::Item, LayoutError> {
    use crate::scene::*;
    let mut lines = Vec::new();
    for piece in text.split('\n') {
        lines.extend(run_lines(piece, metric).map_err(layout_error)?);
    }
    Ok(Item::Text(TextItem {
        rect,
        role: TextRole::Label,
        size: 14,
        align,
        style: TextStyle::Text,
        series: 0,
        lines,
    }))
}

fn coordinate(value: i64) -> Result<i32, LayoutError> {
    i32::try_from(value).map_err(|_| LayoutError::Overflow)
}

fn table_items(
    text: &str,
    rect: Rect,
    profile: Profile,
    font_family: bool,
) -> Result<Vec<crate::scene::Item>, LayoutError> {
    use crate::scene::*;
    let table = Table::new(text, profile, font_family).map_err(layout_error)?;
    let mut shapes = vec![Item::Rect(RectItem {
        shape: Shape::plain(ShapeStyle::Node),
        rect,
    })];
    let mut texts = Vec::new();
    let top = coordinate(i64::from(rect.y) + i64::from(table.padding_y))?;
    texts.push(text_item(
        &table.heading,
        Rect {
            x: rect.x,
            y: top,
            w: rect.w,
            h: table.heading_height,
        },
        Align::Middle,
        table.metric,
    )?);
    let divider = coordinate(i64::from(top) + i64::from(table.heading_height))?;
    let right = coordinate(i64::from(rect.x) + i64::from(rect.w) - i64::from(table.separator))?;
    shapes.push(rule(
        Point {
            x: rect.x,
            y: divider,
        },
        Point {
            x: right,
            y: divider,
        },
    ));
    append_attribute_items(&table, rect, divider, (&mut shapes, &mut texts))?;
    shapes.extend(texts);
    Ok(shapes)
}

fn append_attribute_items(
    table: &Table,
    rect: Rect,
    divider: i32,
    items: (&mut Vec<crate::scene::Item>, &mut Vec<crate::scene::Item>),
) -> Result<(), LayoutError> {
    let bottom = coordinate(i64::from(rect.y) + i64::from(rect.h) - i64::from(table.separator))?;
    let mut x = coordinate(i64::from(rect.x) + i64::from(table.padding_x))?;
    for (position, column) in table.columns.iter().enumerate() {
        append_column(table, *column, Point { x, y: divider }, items.1)?;
        x = coordinate(i64::from(x) + i64::from(column.1) + i64::from(table.padding_x))?;
        if position + 1 < table.columns.len() {
            let line_x = coordinate(i64::from(x) - i64::from(table.padding_x / 2))?;
            items.0.push(rule(
                Point {
                    x: line_x,
                    y: divider,
                },
                Point {
                    x: line_x,
                    y: bottom,
                },
            ));
        }
    }
    Ok(())
}

fn append_column(
    table: &Table,
    column: (usize, i32),
    origin: Point,
    texts: &mut Vec<crate::scene::Item>,
) -> Result<(), LayoutError> {
    let mut y = coordinate(i64::from(origin.y) + i64::from(table.separator))?;
    for (row, height) in table.rows.iter().zip(&table.row_heights) {
        let text = row.get(column.0).map_or("", String::as_str);
        texts.push(text_item(
            text,
            Rect {
                x: origin.x,
                y,
                w: column.1,
                h: *height,
            },
            crate::scene::Align::Start,
            table.metric,
        )?);
        y = coordinate(i64::from(y) + i64::from(*height))?;
    }
    Ok(())
}

fn layout_error(error: GeomError) -> LayoutError {
    match error {
        GeomError::Domain => LayoutError::Domain,
        GeomError::Overflow => LayoutError::Overflow,
    }
}

#[cfg(test)]
mod tests;
