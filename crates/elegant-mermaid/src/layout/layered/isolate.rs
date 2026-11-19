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
    let metadata = super::regions::Metadata::validate(input)?;
    let selected = select_isolated_groups(input, &metadata.parents);
    if selected.is_empty() {
        return Ok(None);
    }
    let (children, child_budget) = layout_children(input, edges, &selected)?;
    let (parent, parent_edges) = parent_input(input, edges, &selected, &children)?;
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
        let scene = without_margin(scene, pipeline::margin(input))?;
        let scene = strip_isolated_region_root(scene, &group.id);
        children.push((group.id.clone(), scene));
    }
    Ok((children, budget))
}

fn child_input<'a>(
    input: &Input,
    edges: &[EdgeOptions<'a>],
    group: &crate::layout::input::Group,
    ids: &[String],
) -> Result<(Input, Vec<EdgeOptions<'a>>), LayoutError> {
    let metadata = super::regions::Metadata::validate(input)?;
    let owns_regions = input
        .region_sets
        .iter()
        .any(|set| input.groups[set.parent].id == group.id);
    let retained_groups: Vec<_> = input
        .groups
        .iter()
        .map(|item| ids.contains(&item.id) || (owns_regions && item.id == group.id))
        .collect();
    let (routes, child_edges): (Vec<_>, Vec<_>) = input
        .routes
        .iter()
        .zip(edges)
        .filter(|(route, _)| ids.contains(&route.from) && ids.contains(&route.to))
        .map(|(route, edge)| (route.clone(), *edge))
        .unzip();
    let labels = input
        .labels
        .iter()
        .filter(|label| {
            ids.contains(&label.owner) || routes.iter().any(|route| route.id == label.owner)
        })
        .cloned()
        .collect();
    let boxes = input
        .boxes
        .iter()
        .filter(|item| ids.contains(&item.id) || (owns_regions && item.id == group.id))
        .map(|item| {
            let mut item = item.clone();
            if item.id == group.id || (!owns_regions && item.parent == group.id) {
                item.parent.clear();
            }
            item
        })
        .collect();
    let groups = input
        .groups
        .iter()
        .filter(|item| ids.contains(&item.id) || (owns_regions && item.id == group.id))
        .map(|item| {
            let mut item = item.clone();
            if item.id == group.id || (!owns_regions && item.parent == group.id) {
                item.parent.clear();
            }
            if item.id == group.id {
                item.direction.clear();
            }
            item
        })
        .collect();
    let child = Input {
        kind: input.kind,
        profile: input.profile,
        direction: Direction::from_token(&group.direction).ok_or(LayoutError::Domain)?,
        options: input.options.clone(),
        boxes,
        routes,
        labels,
        groups,
        sizes: input
            .boxes
            .iter()
            .enumerate()
            .filter(|(_, item)| ids.contains(&item.id) || (owns_regions && item.id == group.id))
            .map(|(index, _)| input.sizes.get(index).copied().unwrap_or_default())
            .collect(),
        attachments: pipeline::attachment_metadata::project(
            input,
            &input
                .boxes
                .iter()
                .map(|item| ids.contains(&item.id) || (owns_regions && item.id == group.id))
                .collect::<Vec<_>>(),
        )?,
        region_sets: metadata.project(&retained_groups)?,
        spacing: input.spacing,
    };
    Ok((child, child_edges))
}

fn parent_input<'a>(
    input: &Input,
    edges: &[EdgeOptions<'a>],
    selected: &[(&crate::layout::input::Group, Vec<String>)],
    children: &[(String, Scene)],
) -> Result<(Input, Vec<EdgeOptions<'a>>), LayoutError> {
    let hidden: Vec<_> = selected
        .iter()
        .flat_map(|(_, ids)| ids.iter().cloned())
        .collect();
    let mut parent = input.clone();
    parent.attachments = pipeline::attachment_metadata::project(
        input,
        &input
            .boxes
            .iter()
            .map(|b| !hidden.contains(&b.id))
            .collect::<Vec<_>>(),
    )?;
    parent.sizes = input
        .boxes
        .iter()
        .enumerate()
        .filter(|(_, b)| !hidden.contains(&b.id))
        .map(|(index, _)| input.sizes.get(index).copied().unwrap_or_default())
        .collect();
    parent.boxes.retain(|b| !hidden.contains(&b.id));
    parent.groups.retain(|g| {
        !hidden.contains(&g.id) && !selected.iter().any(|(selected, _)| selected.id == g.id)
    });
    let retained_groups: Vec<_> = input
        .groups
        .iter()
        .map(|g| parent.groups.iter().any(|kept| kept.id == g.id))
        .collect();
    parent.region_sets = super::regions::Metadata::validate(input)?.project(&retained_groups)?;
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
    Ok((parent, parent_edges))
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

fn strip_isolated_region_root(scene: Scene, id: &str) -> Scene {
    let mut dump = scene.dump_part().clone();
    dump.boxes.retain(|b| b.id != id);
    let mut items = scene.items().to_vec();
    items.retain(|group| group.owner != id);
    Scene::new(scene.canvas(), dump, items)
}

fn without_margin(scene: Scene, margin: i32) -> Result<Scene, LayoutError> {
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

fn select_isolated_groups<'a>(
    input: &'a Input,
    parents: &[Option<usize>],
) -> Vec<(&'a crate::layout::input::Group, Vec<String>)> {
    let mut selected = Vec::new();
    let mut eligible = vec![false; input.groups.len()];
    for (index, group) in input.groups.iter().enumerate() {
        if input
            .region_sets
            .iter()
            .any(|set| set.regions.iter().any(|&r| input.groups[r].id == group.id))
        {
            continue;
        }
        if group.direction.is_empty() {
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
        eligible[index] = true;
        selected.push((index, ids));
    }
    selected
        .into_iter()
        .filter(|(index, _)| {
            let mut parent = parents[*index];
            while let Some(index) = parent {
                if eligible[index] {
                    return false;
                }
                parent = parents[index];
            }
            true
        })
        .map(|(index, ids)| (&input.groups[index], ids))
        .collect()
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

#[cfg(test)]
mod sizing_tests {
    use super::*;
    use crate::geom::Size;
    use crate::layout::input::{Box, Group, SizeRule};
    use crate::scene::{BoxRole, DumpOptions};

    #[test]
    fn postorder_er_groups_render_nested_directions() -> Result<(), crate::RenderError> {
        let source = include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../corpus/er/mermaid/entityRelationshipDiagram~0020.mmd"
        ));
        let document = crate::parse(source);
        assert!(
            !document.has_errors(),
            "corpus fixture entityRelationshipDiagram~0020.mmd must parse without error diagnostics; got: {:?}",
            document.diagnostics()
        );
        for profile in [crate::Profile::Vector, crate::Profile::Cell] {
            let options = crate::LayoutOptions {
                profile,
                ..crate::LayoutOptions::default()
            };
            let scene = crate::layout(&document, &options)?;
            let dump = scene.dump();
            for id in ["TOP", "B1", "B2", "I1", "F1", "I2", "F2", "A", "B"] {
                assert!(
                    dump.contains(&format!("\"id\":\"{id}\"")),
                    "the {:?} layout dump must contain a box for every declared ER entity; missing id {id:?}",
                    profile
                );
            }
        }
        assert!(
            !crate::render_svg(&document, &crate::SvgOptions::default())?.is_empty(),
            "render_svg must produce non-empty SVG bytes for the ER corpus fixture"
        );
        assert!(
            !crate::render_text(&document, &crate::TextOptions::default())?.is_empty(),
            "render_text must produce non-empty text bytes for the ER corpus fixture"
        );
        Ok(())
    }

    const NESTED_DIRECTION_SOURCE: &str = "flowchart TB\n\
  subgraph outer[Outer]\n\
    a1[A1] --> a2[A2]\n\
    subgraph inner[Inner]\n\
      direction LR\n\
      b1[B1] --> b2[B2] --> b3[B3]\n\
    end\n\
    a2 --> a3[A3]\n\
  end\n\
  s[Start] --> a1\n\
  a3 --> e[End]\n";

    #[derive(Debug, thiserror::Error)]
    enum NestedError {
        #[error("layout failed: {0}")]
        Layout(#[from] crate::RenderError),
        #[error("{0} is missing from the scene")]
        Missing(String),
    }

    fn nested_rect(scene: &Scene, id: &str) -> Result<Rect, NestedError> {
        scene
            .boxes()
            .iter()
            .find(|b| b.id == id)
            .map(|b| b.rect)
            .or_else(|| scene.labels().iter().find(|l| l.id == id).map(|l| l.rect))
            .ok_or_else(|| NestedError::Missing(id.to_owned()))
    }

    #[test]
    fn nested_direction_subgraph_is_ranked_member_of_parent_cluster() -> Result<(), NestedError> {
        let document = crate::parse(NESTED_DIRECTION_SOURCE);
        assert!(!document.has_errors(), "{:?}", document.diagnostics());
        for profile in [crate::Profile::Vector, crate::Profile::Cell] {
            let options = crate::LayoutOptions {
                profile,
                ..crate::LayoutOptions::default()
            };
            let scene = crate::layout(&document, &options)?;
            assert_eq!(scene.validate(), Ok(None), "{profile:?}");
            let outer = nested_rect(&scene, "outer")?;
            let inner = nested_rect(&scene, "inner")?;
            let title = nested_rect(&scene, "outer.label")?;
            let peer = nested_rect(&scene, "a1")?;
            assert!(
                inner.y >= title.y + title.h,
                "{profile:?}: inner {inner:?} starts above the outer title {title:?}"
            );
            assert_eq!(
                crate::geom::contains(outer, inner),
                Ok(true),
                "{profile:?}: outer {outer:?} must contain inner {inner:?}"
            );
            assert!(
                inner.y < peer.y + peer.h && peer.y < inner.y + inner.h,
                "{profile:?}: inner {inner:?} shares no rank with its peer {peer:?}"
            );
            if profile == crate::Profile::Cell {
                let rect = |x, y, w, h| Rect { x, y, w, h };
                assert_eq!(outer, rect(1, 1, 41, 31));
                assert_eq!(inner, rect(10, 8, 31, 5));
                assert_eq!(nested_rect(&scene, "b1")?, rect(16, 9, 6, 3));
                assert_eq!(peer, rect(2, 9, 6, 3));
            }
        }
        Ok(())
    }

    #[test]
    fn sparse_sizes_follow_filtered_box_indices() -> Result<(), LayoutError> {
        let group = Group {
            id: "group".into(),
            parent: String::new(),
            direction: "LR".into(),
            direction_span: crate::source::Span { start: 0, end: 0 },
        };
        let input = Input {
            kind: "flowchart",
            profile: Profile::Cell,
            direction: Direction::Tb,
            options: DumpOptions::default(),
            boxes: ["outside", "fixed", "trailing"]
                .into_iter()
                .map(|id| Box {
                    id: id.into(),
                    role: BoxRole::Node,
                    shape: String::new(),
                    icon: false,
                    parent: String::new(),
                    exclusive: true,
                    text: String::new(),
                    direction: String::new(),
                })
                .collect(),
            routes: Vec::new(),
            labels: Vec::new(),
            groups: Vec::new(),
            sizes: vec![SizeRule::Measured, SizeRule::Exact(Size { w: 1, h: 1 })],
            attachments: Vec::new(),
            region_sets: Vec::new(),
            spacing: crate::layout::input::Spacing::default(),
        };
        let ids = vec!["fixed".into(), "trailing".into()];
        let (child, _) = child_input(&input, &[], &group, &ids)?;
        assert_eq!(child.boxes.len(), 2);
        assert_eq!(child.sizes.len(), 2);
        assert!(
            matches!(child.sizes[0], SizeRule::Exact(Size { w: 1, h: 1 })),
            "child must retain the fixed box's original Exact rule"
        );
        assert!(
            matches!(child.sizes[1], SizeRule::Measured),
            "child must fill the missing trailing size rule with Measured"
        );
        let selected = vec![(&group, vec!["outside".into()])];
        let (parent, _) = parent_input(&input, &[], &selected, &[])?;
        assert_eq!(parent.boxes.len(), 2);
        assert_eq!(parent.sizes.len(), 2);
        assert!(
            matches!(parent.sizes[0], SizeRule::Exact(Size { w: 1, h: 1 })),
            "parent must retain the fixed box's original Exact rule"
        );
        assert!(
            matches!(parent.sizes[1], SizeRule::Measured),
            "parent must fill the missing trailing size rule with Measured"
        );
        Ok(())
    }
}
