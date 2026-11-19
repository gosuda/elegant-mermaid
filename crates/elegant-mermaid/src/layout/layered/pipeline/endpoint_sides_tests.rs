use super::*;
use crate::layout::input::{Box as InputBox, Route as InputRoute, RouteSide, Spacing};

fn input(profile: Profile, direction: Direction, sides: (RouteSide, RouteSide)) -> Input {
    let boxes = ["A", "B", "obstacle"]
        .into_iter()
        .map(|id| InputBox {
            icon: false,
            id: id.into(),
            role: BoxRole::Node,
            shape: "rect".into(),
            parent: String::new(),
            exclusive: true,
            text: id.into(),
            direction: String::new(),
        })
        .collect();
    let routes = [
        ("A", "B"),
        ("A", "B"),
        ("B", "A"),
        ("A", "obstacle"),
        ("obstacle", "B"),
    ]
    .into_iter()
    .enumerate()
    .map(|(index, (from, to))| InputRoute {
        id: format!("e{index}"),
        from: from.into(),
        to: to.into(),
        orthogonal: true,
        marker_start: "none".into(),
        marker_end: "point".into(),
        line: "normal".into(),
        min_length: 1,
        from_side: Some(sides.0),
        to_side: Some(sides.1),
    })
    .collect();
    let labels = vec![crate::layout::input::Label {
        id: "e0.label".into(),
        owner: "e0".into(),
        role: TextRole::Label,
        text: "relation".into(),
    }];
    Input {
        kind: "c4",
        profile,
        direction,
        options: DumpOptions {
            profile,
            direction,
            thoroughness: 1,
            ..DumpOptions::default()
        },
        boxes,
        routes,
        labels,
        groups: Vec::new(),
        sizes: [SizeRule::Measured, SizeRule::Measured, SizeRule::Measured].into(),
        attachments: Vec::new(),
        region_sets: Vec::new(),
        spacing: Spacing::default(),
    }
}

fn vector(side: RouteSide) -> (i64, i64) {
    match side {
        RouteSide::Up => (0, -1),
        RouteSide::Down => (0, 1),
        RouteSide::Left => (-1, 0),
        RouteSide::Right => (1, 0),
    }
}

fn endpoint(rect: Rect, side: RouteSide) -> Result<Point, std::num::TryFromIntError> {
    let x = i64::from(rect.x);
    let y = i64::from(rect.y);
    let w = i64::from(rect.w);
    let h = i64::from(rect.h);
    let (x, y) = match side {
        RouteSide::Up => (x + w / 2, y),
        RouteSide::Down => (x + w / 2, y + h),
        RouteSide::Left => (x, y + h / 2),
        RouteSide::Right => (x + w, y + h / 2),
    };
    Ok(Point {
        x: i32::try_from(x)?,
        y: i32::try_from(y)?,
    })
}

fn assert_route_geometry(
    scene: &Scene,
    route: &crate::scene::SceneRoute,
    sides: (RouteSide, RouteSide),
) -> Result<(), Box<dyn std::error::Error>> {
    let from = scene
        .boxes()
        .iter()
        .find(|b| b.id == route.from)
        .ok_or("route source box must exist")?;
    let to = scene
        .boxes()
        .iter()
        .find(|b| b.id == route.to)
        .ok_or("route target box must exist")?;
    let points = &route.points;
    let last = *points.last().ok_or("forced-face route must have points")?;
    assert_eq!(points[0], endpoint(from.rect, sides.0)?);
    assert_eq!(last, endpoint(to.rect, sides.1)?);
    let delta = |a: Point, b: Point| {
        (
            (i64::from(b.x) - i64::from(a.x)).signum(),
            (i64::from(b.y) - i64::from(a.y)).signum(),
        )
    };
    assert_eq!(delta(points[0], points[1]), vector(sides.0));
    assert_eq!(delta(last, points[points.len() - 2]), vector(sides.1));
    assert!(
        crate::geom::is_orthogonal(points),
        "route {} must be orthogonal: points={points:?}",
        route.id
    );
    for (index, point) in points.iter().enumerate() {
        assert!(
            point.x >= 0 && point.y >= 0,
            "route {} point {index} must be nonnegative: point={point:?}",
            route.id
        );
        assert!(
            point.x <= scene.canvas().w && point.y <= scene.canvas().h,
            "route {} point {index} must stay inside canvas: point={point:?}, canvas={:?}",
            route.id,
            scene.canvas()
        );
    }
    for obstacle in scene
        .boxes()
        .iter()
        .filter(|b| b.exclusive && b.id != route.from && b.id != route.to)
    {
        assert!(
            !crate::geom::polyline_hits_rect(points, obstacle.rect)?,
            "route {} must clear obstacle {}: points={points:?}, obstacle={:?}",
            route.id,
            obstacle.id,
            obstacle.rect
        );
    }
    for label in &scene.dump_part().labels {
        assert!(
            !crate::geom::polyline_hits_rect(points, label.rect)?,
            "route {} must clear label {}: points={points:?}, label={:?}",
            route.id,
            label.id,
            label.rect
        );
    }
    Ok(())
}

fn assert_scene_geometry(
    scene: &Scene,
    sides: (RouteSide, RouteSide),
) -> Result<(), Box<dyn std::error::Error>> {
    for route in scene.routes() {
        assert_route_geometry(scene, route, sides)?;
    }
    assert_eq!(scene.routes()[0].points, scene.routes()[1].points);
    assert_eq!(scene.routes()[2].from, "B");
    assert_eq!(scene.routes()[2].to, "A");
    Ok(())
}

#[test]
fn forced_faces_preserve_screen_sides_and_clearance() -> Result<(), Box<dyn std::error::Error>> {
    use RouteSide::{Down, Left, Right, Up};
    for profile in [Profile::Cell, Profile::Vector] {
        for direction in [Direction::Tb, Direction::Bt, Direction::Lr, Direction::Rl] {
            for sides in [(Up, Down), (Down, Up), (Left, Right), (Right, Left)] {
                let input = input(profile, direction, sides);
                let (scene, _) = crate::layout::c4::layout(&input)?;
                assert_scene_geometry(&scene, sides)?;
            }
        }
    }
    Ok(())
}
