use super::*;

fn input(source: &str, profile: Profile) -> Result<Input, &'static str> {
    let parsed = crate::syntax::c4::parse(source, &[]);
    assert_eq!(parsed.diagnostics.len(), 0);
    let (model, diagnostics) = crate::model::c4::resolve(source, &parsed.document);
    assert_eq!(diagnostics.len(), 0);
    from_c4(&model, profile, DumpOptions::default()).map_err(|_| "C4 input failed")
}

#[test]
fn elements_keep_measured_sizes_and_registered_shapes() -> Result<(), &'static str> {
    let source = "C4Context\nPerson(p, \"User\")\nSystemDb(db, \"Data\", \"Stores records\")\nContainer(c, \"API\", \"Rust\", \"Serves requests\")\n";
    for profile in [Profile::Vector, Profile::Cell] {
        let input = input(source, profile)?;
        assert_eq!(
            input
                .boxes
                .iter()
                .map(|node| node.id.as_str())
                .collect::<Vec<_>>(),
            ["p", "db", "c"]
        );
        assert_eq!(
            input
                .boxes
                .iter()
                .map(|node| node.shape.as_str())
                .collect::<Vec<_>>(),
            ["person", "cyl", "rect"]
        );
        assert_eq!(
            input.boxes.get(2).ok_or("missing API")?.text,
            "API<br/>Rust<br/>Serves requests"
        );
        assert!(
            input
                .sizes
                .iter()
                .all(|size| matches!(size, SizeRule::Measured)),
            "C4 boxes must use measured sizes under {profile:?}; observed {:?}",
            input.sizes
        );
    }
    Ok(())
}

#[test]
fn element_text_uses_markup_breaks_without_control_characters() -> Result<(), &'static str> {
    let source = "C4Context\nPerson(p, \"Customer\", \"Uses the system\")\n";
    for profile in [Profile::Vector, Profile::Cell] {
        let input = input(source, profile)?;
        let node = input.boxes.first().ok_or("missing customer")?;
        assert_eq!(node.text, "Customer<br/>Uses the system");
        assert!(
            node.text.contains("<br/>") && !node.text.chars().any(char::is_control),
            "C4 box text must separate fields with markup and contain no controls under {profile:?}; observed {:?}",
            node.text
        );
    }
    Ok(())
}

#[test]
fn boundaries_form_nested_nonexclusive_clusters() -> Result<(), &'static str> {
    let input = input(
        "C4Deployment\nNode(a, \"Host\") {\nSystem_Boundary(b, \"System\") {\nComponent(c, \"Worker\")\n}\n}\n",
        Profile::Cell,
    )?;
    assert_eq!(
        input
            .boxes
            .iter()
            .map(|node| (node.id.as_str(), node.parent.as_str()))
            .collect::<Vec<_>>(),
        [("a", ""), ("b", "a"), ("c", "b")]
    );
    assert_eq!(input.groups.len(), 2);
    let host = input.boxes.first().ok_or("missing host")?;
    assert!(
        !host.exclusive,
        "C4 deployment boundaries must be nonexclusive; observed {host:?}"
    );
    assert!(
        matches!(host.role, BoxRole::Group),
        "C4 deployment boundaries must have group role; observed {:?}",
        host.role
    );
    Ok(())
}

#[test]
fn relation_labels_markers_and_route_ids_are_stable() -> Result<(), &'static str> {
    let input = input(
        "C4Context\nSystem(e0, \"A\")\nSystem(b, \"B\")\nBiRel(e0, b, \"Calls\", \"HTTPS\")\nRel_Back(b, e0, \"Returns\")\n",
        Profile::Cell,
    )?;
    assert_eq!(
        input
            .routes
            .iter()
            .map(|route| route.id.as_str())
            .collect::<Vec<_>>(),
        ["e1", "e2"]
    );
    let first = input.routes.first().ok_or("missing relation")?;
    assert_eq!(
        (
            &*first.marker_start,
            &*first.marker_end,
            &*first.line,
            first.min_length
        ),
        ("point", "point", "normal", 1)
    );
    let label = input
        .labels
        .iter()
        .find(|label| label.owner == "e1")
        .ok_or("missing label")?;
    assert_eq!(label.text, "Calls<br/>HTTPS");
    assert_eq!(label.id, "e1.label");
    let back = input.routes.get(1).ok_or("missing back relation")?;
    assert_eq!(
        (
            &*back.from,
            &*back.to,
            &*back.marker_start,
            &*back.marker_end
        ),
        ("b", "e0", "point", "none")
    );
    Ok(())
}

#[test]
fn directional_relation_macros_attach_to_screen_face_midpoints() -> Result<(), &'static str> {
    for profile in [Profile::Vector, Profile::Cell] {
        for (macro_name, source_face, target_face) in [
            ("Rel_Up", (1, 0), (1, 2)),
            ("Rel_U", (1, 0), (1, 2)),
            ("Rel_Down", (1, 2), (1, 0)),
            ("Rel_D", (1, 2), (1, 0)),
            ("Rel_Left", (0, 1), (2, 1)),
            ("Rel_L", (0, 1), (2, 1)),
            ("Rel_Right", (2, 1), (0, 1)),
            ("Rel_R", (2, 1), (0, 1)),
        ] {
            let source = format!(
                "C4Context\nSystem(a, \"Source system\")\nSystem(b, \"Target\")\n{macro_name}(a, b, \"Calls\")\n"
            );
            let input = input(&source, profile)?;
            let (scene, _) = layout(&input).map_err(|_| "directional C4 layout failed")?;
            assert_eq!(
                scene.routes().len(),
                1,
                "{macro_name} under {profile:?} must emit one relation"
            );
            let route = scene.routes().first().ok_or("missing directional route")?;
            for (id, face, endpoint) in [
                ("a", source_face, route.points.first()),
                ("b", target_face, route.points.last()),
            ] {
                let bounds = scene
                    .boxes()
                    .iter()
                    .find(|bounds| bounds.id == id)
                    .ok_or("missing directional endpoint box")?;
                let expected = crate::geom::Point {
                    x: bounds.rect.x + bounds.rect.w * face.0 / 2,
                    y: bounds.rect.y + bounds.rect.h * face.1 / 2,
                };
                assert_eq!(
                    endpoint,
                    Some(&expected),
                    "{macro_name} under {profile:?}: endpoint on {id} must be the screen-face midpoint {face:?} of {:?}",
                    bounds.rect
                );
            }
        }
    }
    Ok(())
}

#[test]
fn unresolved_endpoints_do_not_create_phantom_boxes() -> Result<(), &'static str> {
    let input = input(
        "C4Context\nSystem(a, \"A\")\nRel(a, absent, \"Uses\")\n",
        Profile::Cell,
    )?;
    assert_eq!(input.boxes.len(), 1);
    assert_eq!(input.routes.len(), 0);
    Ok(())
}

#[test]
fn colliding_boundary_aliases_get_unique_box_ids() -> Result<(), &'static str> {
    let input = input(
        "C4Context\nSystem(a, \"Element\")\nBoundary(a, \"Group\") {\nPerson(p, \"Person\")\n}\n",
        Profile::Cell,
    )?;
    assert_eq!(
        input
            .boxes
            .iter()
            .map(|node| node.id.as_str())
            .collect::<Vec<_>>(),
        ["a", "c4group0", "p"]
    );
    assert_eq!(
        input.boxes.get(2).ok_or("missing child")?.parent,
        "c4group0"
    );
    Ok(())
}

fn shape_fixture(profile: Profile) -> Result<(Input, crate::scene::Scene), &'static str> {
    let source = "C4Context\nPerson(p, \"User\")\nSystemDb(db, \"Data\")\nSystem(s, \"System\")\n";
    let input = input(source, profile)?;
    let (scene, _) = layout(&input).map_err(|_| "C4 shape layout failed")?;
    Ok((input, scene))
}

#[test]
fn actual_person_scene_has_a_rounded_body_and_circular_head() -> Result<(), &'static str> {
    use crate::scene::Item;
    for profile in [Profile::Vector, Profile::Cell] {
        let (_, scene) = shape_fixture(profile)?;
        let person = scene
            .items()
            .iter()
            .find(|group| group.owner == "p")
            .ok_or("missing person group")?;
        assert!(
            matches!(person.items.first(), Some(Item::RoundRect(_))),
            "C4 person must have a rounded body under {profile:?}; observed {:?}",
            person.items
        );
        let head = person
            .items
            .iter()
            .find_map(|item| match item {
                Item::Ellipse(ellipse) => Some(ellipse),
                _ => None,
            })
            .ok_or("missing person head")?;
        assert_eq!(head.rx, head.ry);
    }
    Ok(())
}

#[test]
fn actual_database_scene_has_a_fitted_outer_shape_and_elliptical_cap() -> Result<(), &'static str> {
    use crate::scene::Item;
    for profile in [Profile::Vector, Profile::Cell] {
        let (_, scene) = shape_fixture(profile)?;
        let database = scene
            .items()
            .iter()
            .find(|group| group.owner == "db")
            .ok_or("missing database group")?;
        let cap = database
            .items
            .iter()
            .find_map(|item| match item {
                Item::Ellipse(ellipse) => Some(ellipse),
                _ => None,
            })
            .ok_or("missing database cap")?;
        assert!(
            cap.rx > cap.ry,
            "C4 database must have a wide elliptical cap under {profile:?}; observed {cap:?}"
        );
        let expected_outer = match profile {
            Profile::Vector => matches!(database.items.first(), Some(Item::Path(_))),
            Profile::Cell => matches!(database.items.first(), Some(Item::RoundRect(_))),
        };
        assert!(
            expected_outer,
            "C4 database outer primitive must fit its profile {profile:?}; observed {:?}",
            database.items
        );
    }
    Ok(())
}

#[test]
fn actual_ordinary_system_retains_its_single_rectangle() -> Result<(), &'static str> {
    use crate::scene::{Item, ItemClass};
    for profile in [Profile::Vector, Profile::Cell] {
        let (_, scene) = shape_fixture(profile)?;
        let system = scene
            .items()
            .iter()
            .find(|group| group.owner == "s")
            .ok_or("missing ordinary system")?;
        assert!(
            matches!(system.items.first(), Some(Item::Rect(_))),
            "ordinary C4 systems must retain rectangular outlines; observed {:?}",
            system.items
        );
        assert_eq!(
            system
                .items
                .iter()
                .filter(|item| item.class() == ItemClass::Shape)
                .count(),
            1
        );
    }
    Ok(())
}

#[test]
fn shape_postprocessing_preserves_dump_and_text_primitives() -> Result<(), &'static str> {
    use crate::scene::ItemClass;
    for profile in [Profile::Vector, Profile::Cell] {
        let (input, scene) = shape_fixture(profile)?;
        let (baseline, _) = super::super::layered::pipeline::layout_family(&input, &[])
            .map_err(|_| "baseline layout failed")?;
        assert_eq!(scene.dump(), baseline.dump());
        let texts = scene
            .items()
            .iter()
            .flat_map(|group| group.items.iter())
            .filter(|item| item.class() == ItemClass::Text)
            .collect::<Vec<_>>();
        let original = baseline
            .items()
            .iter()
            .flat_map(|group| group.items.iter())
            .filter(|item| item.class() == ItemClass::Text)
            .collect::<Vec<_>>();
        assert_eq!(texts, original);
    }
    Ok(())
}

fn outline_points(item: crate::scene::Item) -> Result<Vec<crate::geom::Point>, &'static str> {
    use crate::geom::Point;
    use crate::scene::{Item, PathCommand};
    match item {
        Item::RoundRect(body) => Ok(vec![
            Point {
                x: body.rect.x,
                y: body.rect.y,
            },
            Point {
                x: body.rect.x + body.rect.w,
                y: body.rect.y + body.rect.h,
            },
        ]),
        Item::Ellipse(ellipse) => Ok(vec![
            Point {
                x: ellipse.cx - ellipse.rx,
                y: ellipse.cy - ellipse.ry,
            },
            Point {
                x: ellipse.cx + ellipse.rx,
                y: ellipse.cy + ellipse.ry,
            },
        ]),
        Item::Path(path) => Ok(path
            .commands
            .into_iter()
            .flat_map(|command| match command {
                PathCommand::Move(point) | PathCommand::Line(point) => vec![point],
                PathCommand::Curve { c1, c2, to } => vec![c1, c2, to],
                _ => Vec::new(),
            })
            .collect()),
        _ => Err("unexpected outline primitive"),
    }
}

#[test]
fn fitted_outlines_remain_inside_unchanged_box() -> Result<(), &'static str> {
    use crate::geom::{Point, Rect};
    let rect = Rect {
        x: 11,
        y: 17,
        w: 1000,
        h: 1000,
    };
    let contains =
        |point: Point| point.x >= 11 && point.x <= 1011 && point.y >= 17 && point.y <= 1017;
    let mut items =
        person_outline(rect, Profile::Vector, 512).map_err(|_| "person outline failed")?;
    items.extend(
        cylinder_outline(rect, Profile::Vector, 512).map_err(|_| "cylinder outline failed")?,
    );
    for item in items {
        let points = outline_points(item)?;
        assert!(
            points.iter().copied().all(contains),
            "C4 fitted outline points must stay inside the original box {rect:?}; observed {points:?}"
        );
    }
    Ok(())
}

#[test]
fn cell_database_cap_has_a_database_symbol_instead_of_an_invisible_flat_rim()
-> Result<(), &'static str> {
    let (_, scene) = shape_fixture(Profile::Cell)?;
    let database = scene
        .items()
        .iter()
        .find(|group| group.owner == "db")
        .ok_or("missing database group")?;
    let symbol = database
        .items
        .iter()
        .find_map(|item| match item {
            crate::scene::Item::SymbolRef(symbol) => Some(symbol),
            _ => None,
        })
        .ok_or("missing database cap symbol")?;
    assert_eq!(symbol.symbol.as_str(), "database");
    let bounds = scene
        .boxes()
        .iter()
        .find(|bounds| bounds.id == "db")
        .ok_or("missing database bounds")?;
    assert_eq!(symbol.at.y, bounds.rect.y);
    Ok(())
}

#[test]
fn directional_cell_routes_stay_on_drawable_cells() -> Result<(), &'static str> {
    let source = "C4Context\nSystem(a, \"A\")\nSystem(b, \"B\")\nSystem(c, \"C\")\nSystem(d, \"D\")\nSystem(e, \"E\")\nRel(a, b, \"Rel (default)\")\nRel_U(a, c, \"Rel_U\")\nRel_D(a, d, \"Rel_D\")\nRel_L(a, e, \"Rel_L\")\nRel_R(b, c, \"Rel_R\")\n";
    let input = input(source, Profile::Cell)?;
    let (scene, _) = layout(&input).map_err(|_| "C4 directional layout failed")?;
    let canvas = scene.canvas();
    for route in scene.routes() {
        for point in &route.points {
            assert!(
                point.x >= 0 && point.y >= 0 && point.x < canvas.w && point.y < canvas.h,
                "route {} point {point:?} must be a cell of canvas {canvas:?}",
                route.id
            );
        }
    }
    Ok(())
}
