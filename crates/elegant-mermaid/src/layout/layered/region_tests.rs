use super::{
    LayoutError,
    pipeline::{EdgeOptions, layout_family},
};
use crate::{
    geom::Rect,
    layout::input::{Box as InputBox, Group as InputGroup, Input, Route as InputRoute, SizeRule},
    scene::{BoxRole, Direction, DumpOptions, Profile, Scene},
};

fn input(profile: Profile, direction: Direction) -> Input {
    Input {
        kind: "state",
        profile,
        direction,
        options: DumpOptions {
            profile,
            thoroughness: 1,
            ..DumpOptions::default()
        },
        boxes: Vec::new(),
        routes: Vec::new(),
        labels: Vec::new(),
        groups: Vec::new(),
        sizes: Vec::new(),
        attachments: Vec::new(),
        region_sets: Vec::new(),
        spacing: crate::layout::input::Spacing::default(),
    }
}

fn node(input: &mut Input, id: &str, parent: &str) {
    input.boxes.push(InputBox {
        icon: false,
        id: id.into(),
        role: BoxRole::Node,
        shape: String::new(),
        parent: parent.into(),
        exclusive: true,
        text: id.into(),
        direction: String::new(),
    });
    input.sizes.push(SizeRule::Measured);
}

fn group(input: &mut Input, id: &str, parent: &str) {
    node(input, id, parent);
    if let Some(item) = input.boxes.last_mut() {
        item.role = BoxRole::Group;
        item.exclusive = false;
    }
    input.groups.push(InputGroup {
        id: id.into(),
        parent: parent.into(),
        direction: String::new(),
        direction_span: crate::source::Span { start: 0, end: 0 },
    });
}

fn regions(input: &mut Input, parent: &str, children: &[&str]) -> Result<(), LayoutError> {
    let index = |id: &str| {
        input
            .groups
            .iter()
            .position(|group| group.id == id)
            .ok_or(LayoutError::Domain)
    };
    input.region_sets.push(crate::layout::input::RegionSet {
        parent: index(parent)?,
        regions: children
            .iter()
            .map(|id| index(id))
            .collect::<Result<Vec<_>, _>>()?,
    });
    Ok(())
}

fn edge(input: &mut Input, from: &str, to: &str) {
    input.routes.push(InputRoute {
        id: format!("e{}", input.routes.len()),
        from: from.into(),
        to: to.into(),
        orthogonal: true,
        marker_start: String::new(),
        marker_end: String::new(),
        line: "solid".into(),
        min_length: 1,
        from_side: None,
        to_side: None,
    });
}

fn fixture(profile: Profile, direction: Direction) -> Result<Input, LayoutError> {
    let mut input = input(profile, direction);
    fixture_groups(&mut input);
    fixture_nodes(&mut input);
    fixture_regions(&mut input)?;
    fixture_edges(&mut input);
    Ok(input)
}

fn fixture_groups(input: &mut Input) {
    for (id, parent) in [
        ("outer", ""),
        ("empty-first", "outer"),
        ("left", "outer"),
        ("right", "outer"),
        ("empty-last", "outer"),
        ("nested-empty", "right"),
        ("nested-live", "right"),
    ] {
        group(input, id, parent);
    }
}

fn fixture_nodes(input: &mut Input) {
    for (id, parent) in [
        ("a", "left"),
        ("b", "left"),
        ("c", "left"),
        ("d", "nested-live"),
        ("e", "nested-live"),
        ("f", "nested-live"),
        ("g", "nested-live"),
        ("outside", ""),
    ] {
        node(input, id, parent);
    }
}

fn fixture_regions(input: &mut Input) -> Result<(), LayoutError> {
    let wide = input
        .boxes
        .iter_mut()
        .find(|item| item.id == "b")
        .ok_or(LayoutError::Domain)?;
    wide.text = "unequal wide member\nsecond measured line".into();
    regions(
        input,
        "outer",
        &["empty-first", "left", "right", "empty-last"],
    )?;
    regions(input, "right", &["nested-empty", "nested-live"])?;
    Ok(())
}

fn fixture_edges(input: &mut Input) {
    for (from, to) in [
        ("a", "b"),
        ("b", "c"),
        ("c", "a"),
        ("b", "b"),
        ("d", "e"),
        ("e", "f"),
        ("f", "g"),
        ("g", "d"),
        ("e", "e"),
        ("c", "d"),
    ] {
        edge(input, from, to);
    }
}

fn external_fixture(profile: Profile, direction: Direction) -> Result<Input, LayoutError> {
    let mut input = fixture(profile, direction)?;
    edge(&mut input, "outside", "a");
    edge(&mut input, "g", "outside");
    Ok(input)
}

fn render(input: &Input) -> Result<Scene, LayoutError> {
    let edges: Vec<_> = input
        .routes
        .iter()
        .map(|_| EdgeOptions {
            marker_start: None,
            marker_end: None,
            stroke: "",
            min_length: 1,
        })
        .collect();
    layout_family(input, &edges).map(|(scene, _)| scene)
}

fn rect(scene: &Scene, id: &str) -> Result<Rect, LayoutError> {
    scene
        .dump_part()
        .boxes
        .iter()
        .find(|item| item.id == id)
        .map(|item| item.rect)
        .ok_or(LayoutError::Domain)
}

fn contains(outer: Rect, inner: Rect) -> bool {
    outer.x <= inner.x
        && outer.y <= inner.y
        && i64::from(inner.x) + i64::from(inner.w) <= i64::from(outer.x) + i64::from(outer.w)
        && i64::from(inner.y) + i64::from(inner.h) <= i64::from(outer.y) + i64::from(outer.h)
}

fn axes(rect: Rect, direction: Direction) -> ((i64, i64), (i64, i64)) {
    let x = (i64::from(rect.x), i64::from(rect.x) + i64::from(rect.w));
    let y = (i64::from(rect.y), i64::from(rect.y) + i64::from(rect.h));
    match direction {
        Direction::Tb | Direction::Bt => (y, x),
        Direction::Lr | Direction::Rl => (x, y),
    }
}

fn assert_bands(input: &Input, scene: &Scene) -> Result<(), LayoutError> {
    for set in &input.region_sets {
        let parent = rect(scene, &input.groups[set.parent].id)?;
        let mut previous = None;
        for &index in &set.regions {
            let id = &input.groups[index].id;
            let frame = rect(scene, id)?;
            assert!(
                frame.w > 0 && frame.h > 0,
                "empty/live region {id} needs positive extent: {frame:?}"
            );
            assert!(
                contains(parent, frame),
                "region {id} escapes parent: {frame:?}, {parent:?}"
            );
            let (rank, cross) = axes(frame, input.direction);
            if let Some((previous_rank, previous_cross)) = previous {
                assert_eq!(
                    rank, previous_rank,
                    "whole-band rank span differs at {id}: {frame:?}"
                );
                assert!(
                    previous_cross <= cross.0,
                    "declared sibling order/disjointness violated at {id}: {frame:?}"
                );
            }
            previous = Some((rank, cross.1));
        }
    }
    Ok(())
}

fn inside(input: &Input, id: &str, region: &str) -> bool {
    let mut current = id;
    while let Some(item) = input.boxes.iter().find(|item| item.id == current) {
        if item.parent == region {
            return true;
        }
        current = &item.parent;
    }
    false
}

fn assert_route_in_frame(route: &crate::scene::SceneRoute, frame: Rect, owner: &str) {
    for point in &route.points {
        let singleton = Rect {
            x: point.x,
            y: point.y,
            w: 0,
            h: 0,
        };
        assert!(
            contains(frame, singleton),
            "route {} leaves {owner} at {point:?}: {frame:?}",
            route.id
        );
    }
}

fn assert_shared_regions(
    input: &Input,
    scene: &Scene,
    semantic: &InputRoute,
) -> Result<(), LayoutError> {
    let route = scene
        .dump_part()
        .routes
        .iter()
        .find(|route| route.id == semantic.id)
        .ok_or(LayoutError::Domain)?;
    for group in &input.groups {
        if inside(input, &semantic.from, &group.id) && inside(input, &semantic.to, &group.id) {
            assert_route_in_frame(route, rect(scene, &group.id)?, &group.id);
        }
    }
    Ok(())
}

fn assert_routes(input: &Input, scene: &Scene) -> Result<(), LayoutError> {
    for semantic in &input.routes {
        let route = scene
            .dump_part()
            .routes
            .iter()
            .find(|route| route.id == semantic.id)
            .ok_or(LayoutError::Domain)?;
        assert!(
            !route.points.is_empty(),
            "route {} has no boundary endpoints",
            route.id
        );
        assert!(
            crate::geom::is_orthogonal(&route.points),
            "route {} is diagonal: {:?}",
            route.id,
            route.points
        );
        assert_shared_regions(input, scene, semantic)?;
    }
    Ok(())
}

fn assert_members(scene: &Scene) -> Result<(), LayoutError> {
    for item in &scene.dump_part().boxes {
        if !item.parent.is_empty() {
            let parent = rect(scene, &item.parent)?;
            assert!(
                contains(parent, item.rect),
                "member {} escapes {}: {:?}, {parent:?}",
                item.id,
                item.parent,
                item.rect
            );
        }
    }
    Ok(())
}

fn assert_multirank(scene: &Scene, direction: Direction) -> Result<(), LayoutError> {
    for (first, middle, last) in [("a", "b", "c"), ("d", "f", "g")] {
        let (a, _) = axes(rect(scene, first)?, direction);
        let (b, _) = axes(rect(scene, middle)?, direction);
        let (c, _) = axes(rect(scene, last)?, direction);
        let separated = match direction {
            Direction::Tb | Direction::Lr => a.1 <= b.0 && b.1 <= c.0,
            Direction::Bt | Direction::Rl => c.1 <= b.0 && b.1 <= a.0,
        };
        assert!(
            separated,
            "multi-rank witness collapsed or reversed: {direction:?} {first}={a:?} {middle}={b:?} {last}={c:?}"
        );
    }
    Ok(())
}

#[test]
fn ordered_regions_cover_unequal_multirank_nested_and_empty_contents() -> Result<(), LayoutError> {
    for profile in [Profile::Vector, Profile::Cell] {
        for direction in [Direction::Tb, Direction::Bt, Direction::Lr, Direction::Rl] {
            let input = external_fixture(profile, direction)?;
            let scene = render(&input)?;
            assert_bands(&input, &scene)?;
            let violation = scene.validate()?;
            assert_eq!(
                violation, None,
                "mixed internal/external routes violate scene geometry: {profile:?} {direction:?}"
            );
            assert_multirank(&scene, direction)?;
            assert_members(&scene)?;
            assert_routes(&input, &scene)?;
        }
    }
    Ok(())
}

fn return_offset(
    scene: &Scene,
    direction: Direction,
    id: &str,
    owner: &str,
) -> Result<i64, LayoutError> {
    let route = scene
        .dump_part()
        .routes
        .iter()
        .find(|route| route.id == id)
        .ok_or(LayoutError::Domain)?;
    let (_, frame_cross) = axes(rect(scene, owner)?, direction);
    let furthest = route
        .points
        .iter()
        .map(|point| match direction {
            Direction::Tb | Direction::Bt => i64::from(point.x),
            Direction::Lr | Direction::Rl => i64::from(point.y),
        })
        .max()
        .ok_or(LayoutError::Domain)?;
    Ok(frame_cross.1 - furthest)
}

#[test]
fn global_returns_do_not_displace_reserved_internal_return_lanes() -> Result<(), LayoutError> {
    for profile in [Profile::Vector, Profile::Cell] {
        for direction in [Direction::Tb, Direction::Bt, Direction::Lr, Direction::Rl] {
            let local = render(&fixture(profile, direction)?)?;
            let mixed = render(&external_fixture(profile, direction)?)?;
            for (route, region) in [("e2", "left"), ("e7", "nested-live")] {
                assert_eq!(
                    return_offset(&mixed, direction, route, region)?,
                    return_offset(&local, direction, route, region)?,
                    "global return lanes displaced internal reservation: {profile:?} {direction:?} {route} in {region}"
                );
            }
        }
    }
    Ok(())
}
