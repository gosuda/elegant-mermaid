use super::{
    LayoutError,
    pipeline::{self, EdgeOptions},
};
use crate::{
    geom::{Point, Rect},
    layout::input::Input,
    scene::*,
};

pub struct Fixed<'a> {
    pub id: &'a str,
    pub scene: &'a Scene,
    pub direction: Direction,
}

pub fn layout(
    input: &Input,
    edges: &[EdgeOptions<'_>],
) -> Result<Option<(Scene, bool)>, LayoutError> {
    let selected = select_isolated_groups(input);
    if selected.is_empty() {
        return Ok(None);
    }
    let (children, child_budget) = layout_children(input, edges, &selected)?;
    let (parent, parent_edges) = parent_input(input, edges, &selected, &children);
    let fixed: Vec<_> = children
        .iter()
        .map(|(id, scene)| Fixed {
            id,
            scene,
            direction: input
                .groups
                .iter()
                .find(|g| g.id == *id)
                .and_then(|g| Direction::from_token(&g.direction))
                .unwrap_or_default(),
        })
        .collect();
    let (scene, exhausted) = pipeline::layout_unisolated(&parent, &parent_edges, &fixed)?;
    drop(fixed);
    let scene = compose_children(input, scene, children)?;
    Ok(Some((scene, child_budget | exhausted)))
}

fn layout_children(
    input: &Input,
    edges: &[EdgeOptions<'_>],
    selected: &[(&crate::layout::input::Group, Vec<String>)],
) -> Result<(Vec<(String, Scene)>, bool), LayoutError> {
    let mut children = Vec::new();
    let mut budget = false;
    for (group, ids) in selected {
        let (child, child_edges) = child_input(input, edges, group, ids)?;
        let (scene, exhausted) = pipeline::layout_family(&child, &child_edges)?;
        budget |= exhausted;
        children.push((group.id.clone(), without_margin(scene, input.profile)?));
    }
    Ok((children, budget))
}

fn child_input<'a>(
    input: &Input,
    edges: &[EdgeOptions<'a>],
    group: &crate::layout::input::Group,
    ids: &[String],
) -> Result<(Input, Vec<EdgeOptions<'a>>), LayoutError> {
    let mut child = input.clone();
    child.sizes = input
        .boxes
        .iter()
        .zip(&input.sizes)
        .filter(|(b, _)| ids.contains(&b.id))
        .map(|(_, size)| *size)
        .collect();
    child.boxes.retain(|b| ids.contains(&b.id));
    for b in &mut child.boxes {
        if b.parent == group.id {
            b.parent.clear();
        }
    }
    let mut child_edges = Vec::new();
    child.routes = input
        .routes
        .iter()
        .zip(edges)
        .filter(|(r, _)| ids.contains(&r.from) && ids.contains(&r.to))
        .map(|(r, edge)| {
            child_edges.push(*edge);
            r.clone()
        })
        .collect();
    child
        .labels
        .retain(|l| ids.contains(&l.owner) || child.routes.iter().any(|r| r.id == l.owner));
    child.groups.retain(|g| ids.contains(&g.id));
    for g in &mut child.groups {
        if g.parent == group.id {
            g.parent.clear();
        }
    }
    child.direction = Direction::from_token(&group.direction).ok_or(LayoutError::Domain)?;
    Ok((child, child_edges))
}

fn parent_input<'a>(
    input: &Input,
    edges: &[EdgeOptions<'a>],
    selected: &[(&crate::layout::input::Group, Vec<String>)],
    children: &[(String, Scene)],
) -> (Input, Vec<EdgeOptions<'a>>) {
    let hidden: Vec<_> = selected
        .iter()
        .flat_map(|(_, ids)| ids.iter().cloned())
        .collect();
    let mut parent = input.clone();
    parent.sizes = input
        .boxes
        .iter()
        .zip(&input.sizes)
        .filter(|(b, _)| !hidden.contains(&b.id))
        .map(|(_, size)| *size)
        .collect();
    parent.boxes.retain(|b| !hidden.contains(&b.id));
    parent.groups.retain(|g| {
        !hidden.contains(&g.id) && !selected.iter().any(|(selected, _)| selected.id == g.id)
    });
    let mut parent_edges = Vec::new();
    parent.routes = input
        .routes
        .iter()
        .zip(edges)
        .filter(|(r, _)| !hidden.contains(&r.from) && !hidden.contains(&r.to))
        .map(|(r, edge)| {
            parent_edges.push(*edge);
            r.clone()
        })
        .collect();
    parent.labels.retain(|l| {
        !hidden.contains(&l.owner)
            && !children
                .iter()
                .any(|(_, s)| s.routes().iter().any(|r| r.id == l.owner))
    });
    (parent, parent_edges)
}

struct ComposedChildren {
    dump: Dump,
    items: Vec<Group>,
}

fn compose_children(
    input: &Input,
    scene: Scene,
    children: Vec<(String, Scene)>,
) -> Result<Scene, LayoutError> {
    let pad = pipeline::constant(input.profile, "cluster_pad");
    let mut composed = ComposedChildren {
        dump: scene.dump_part().clone(),
        items: scene.items().to_vec(),
    };
    for (id, child) in children {
        let offset = composed.child_offset(input, &id, pad)?;
        composed.append_child(input, &child, offset)?;
    }
    composed.sort_declarations(input);
    Ok(Scene::new(scene.canvas(), composed.dump, composed.items))
}

impl ComposedChildren {
    fn child_offset(&self, input: &Input, id: &str, pad: i32) -> Result<Point, LayoutError> {
        let container = self
            .dump
            .boxes
            .iter()
            .find(|b| b.id == id)
            .ok_or(LayoutError::Domain)?
            .rect;
        let title = self
            .items
            .iter()
            .find(|group| group.owner == id)
            .and_then(|group| {
                group.items.iter().find_map(|item| {
                    if let Item::Text(text) = item {
                        Some(text.rect)
                    } else {
                        None
                    }
                })
            })
            .ok_or(LayoutError::Domain)?;
        let direction = input
            .groups
            .iter()
            .find(|g| g.id == id)
            .and_then(|g| Direction::from_token(&g.direction))
            .ok_or(LayoutError::Domain)?;
        content_offset(container, title, direction, pad)
    }

    fn append_child(
        &mut self,
        input: &Input,
        child: &Scene,
        offset: Point,
    ) -> Result<(), LayoutError> {
        for b in child.boxes() {
            let mut b = b.clone();
            b.rect = translated_rect(b.rect, offset)?;
            b.parent = input
                .boxes
                .iter()
                .find(|original| original.id == b.id)
                .ok_or(LayoutError::Domain)?
                .parent
                .clone();
            self.dump.boxes.push(b);
        }
        for r in child.routes() {
            let mut r = r.clone();
            for p in &mut r.points {
                *p = translated_point(*p, offset)?;
            }
            self.dump.routes.push(r);
        }
        for l in child.labels() {
            let mut l = l.clone();
            l.rect = translated_rect(l.rect, offset)?;
            self.dump.labels.push(l);
        }
        for group in child.items() {
            let mut group = group.clone();
            for item in &mut group.items {
                translate_item(item, offset)?;
            }
            self.items.push(group);
        }
        Ok(())
    }

    fn sort_declarations(&mut self, input: &Input) {
        self.dump
            .boxes
            .sort_by_key(|b| input.boxes.iter().position(|v| v.id == b.id));
        self.dump
            .routes
            .sort_by_key(|r| input.routes.iter().position(|v| v.id == r.id));
        self.dump
            .labels
            .sort_by_key(|l| input.labels.iter().position(|v| v.id == l.id));
        self.items.sort_by_key(|group| match group.role {
            GroupRole::Group => (0, input.boxes.iter().position(|b| b.id == group.owner)),
            GroupRole::Edge => (1, input.routes.iter().position(|r| r.id == group.owner)),
            GroupRole::Node => (2, input.boxes.iter().position(|b| b.id == group.owner)),
            GroupRole::Decor => (3, None),
        });
    }
}

fn without_margin(scene: Scene, profile: Profile) -> Result<Scene, LayoutError> {
    let margin = pipeline::constant(profile, "canvas_margin");
    let by = Point {
        x: -margin,
        y: -margin,
    };
    let mut dump = scene.dump_part().clone();
    for b in &mut dump.boxes {
        b.rect = translated_rect(b.rect, by)?;
    }
    for route in &mut dump.routes {
        for point in &mut route.points {
            *point = translated_point(*point, by)?;
        }
    }
    for label in &mut dump.labels {
        label.rect = translated_rect(label.rect, by)?;
    }
    let mut items = scene.items().to_vec();
    for group in &mut items {
        for item in &mut group.items {
            translate_item(item, by)?;
        }
    }
    let canvas = crate::geom::Size {
        w: scene
            .canvas()
            .w
            .checked_sub(2 * margin)
            .ok_or(LayoutError::Domain)?,
        h: scene
            .canvas()
            .h
            .checked_sub(2 * margin)
            .ok_or(LayoutError::Domain)?,
    };
    Ok(Scene::new(canvas, dump, items))
}

fn select_isolated_groups(input: &Input) -> Vec<(&crate::layout::input::Group, Vec<String>)> {
    let mut selected: Vec<(&crate::layout::input::Group, Vec<String>)> = Vec::new();
    for group in &input.groups {
        if group.direction.is_empty() || selected.iter().any(|(_, ids)| ids.contains(&group.id)) {
            continue;
        }
        let ids: Vec<_> = input
            .boxes
            .iter()
            .filter(|b| {
                super::clusters::ancestors(input, &b.id)
                    .iter()
                    .any(|&i| input.boxes[i].id == group.id)
            })
            .map(|b| b.id.clone())
            .collect();
        if input
            .routes
            .iter()
            .any(|r| ids.contains(&r.from) != ids.contains(&r.to))
        {
            continue;
        }
        selected.push((group, ids));
    }
    selected
}

pub(super) fn content_offset(
    frame: Rect,
    title: Rect,
    direction: Direction,
    pad: i32,
) -> Result<Point, LayoutError> {
    match direction {
        Direction::Tb => Ok(Point {
            x: add(frame.x, pad)?,
            y: add(title.y, title.h)?,
        }),
        Direction::Bt | Direction::Rl => Ok(Point {
            x: add(frame.x, pad)?,
            y: add(frame.y, pad)?,
        }),
        Direction::Lr => Ok(Point {
            x: add(title.x, title.w)?,
            y: add(frame.y, pad)?,
        }),
    }
}

fn add(a: i32, b: i32) -> Result<i32, LayoutError> {
    a.checked_add(b).ok_or(LayoutError::Overflow)
}
fn translated_point(p: Point, by: Point) -> Result<Point, LayoutError> {
    Ok(Point {
        x: add(p.x, by.x)?,
        y: add(p.y, by.y)?,
    })
}
fn translated_rect(r: Rect, by: Point) -> Result<Rect, LayoutError> {
    Ok(Rect {
        x: add(r.x, by.x)?,
        y: add(r.y, by.y)?,
        ..r
    })
}
fn translate_item(item: &mut Item, by: Point) -> Result<(), LayoutError> {
    match item {
        Item::Rect(v) => v.rect = translated_rect(v.rect, by)?,
        Item::RoundRect(v) => v.rect = translated_rect(v.rect, by)?,
        Item::Text(v) => v.rect = translated_rect(v.rect, by)?,
        Item::Ellipse(v) => {
            v.cx = add(v.cx, by.x)?;
            v.cy = add(v.cy, by.y)?;
        }
        Item::Polygon(v) => {
            for p in &mut v.points {
                *p = translated_point(*p, by)?;
            }
        }
        Item::Polyline(v) => {
            for p in &mut v.points {
                *p = translated_point(*p, by)?;
            }
        }
        Item::MarkerRef(v) => v.at = translated_point(v.at, by)?,
        Item::SymbolRef(v) => v.at = translated_point(v.at, by)?,
        Item::Path(v) => {
            for command in &mut v.commands {
                translate_command(command, by)?;
            }
        }
    }
    Ok(())
}
fn translate_command(command: &mut PathCommand, by: Point) -> Result<(), LayoutError> {
    match command {
        PathCommand::Move(p) | PathCommand::Line(p) => *p = translated_point(*p, by)?,
        PathCommand::Curve { c1, c2, to } => {
            *c1 = translated_point(*c1, by)?;
            *c2 = translated_point(*c2, by)?;
            *to = translated_point(*to, by)?;
        }
        PathCommand::Arc { centre, .. } => *centre = translated_point(*centre, by)?,
        PathCommand::Close => {}
    }
    Ok(())
}
