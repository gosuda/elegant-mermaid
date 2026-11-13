use super::*;

#[test]
fn malformed_rejects_a_duplicate_box_id() {
    let mut dump = valid_dump();
    dump.boxes.push(bbox("A", rect(40, 40, 10, 10)));
    assert_eq!(
        malformed(&dump),
        Some(Malformed::DuplicateBox(String::from("A")))
    );
}

#[test]
fn malformed_rejects_a_duplicate_route_and_label_id() {
    let mut routes = valid_dump();
    routes
        .routes
        .push(route("e0", "A", "B", vec![point(10, 20), point(10, 60)]));
    assert_eq!(
        malformed(&routes),
        Some(Malformed::DuplicateRoute(String::from("e0")))
    );
    let mut labels = valid_dump();
    labels
        .labels
        .push(label("e0.label", "e0", rect(0, 40, 4, 4)));
    assert_eq!(
        malformed(&labels),
        Some(Malformed::DuplicateLabel(String::from("e0.label")))
    );
}

#[test]
fn malformed_rejects_an_unknown_parent() {
    let mut dump = valid_dump();
    if let Some(b) = dump.boxes.first_mut() {
        b.parent = String::from("Z");
    }
    assert_eq!(
        malformed(&dump),
        Some(Malformed::UnknownParent {
            bbox: String::from("A"),
            parent: String::from("Z"),
        })
    );
}

#[test]
fn malformed_rejects_a_parent_cycle() {
    let mut dump = valid_dump();
    if let Some(a) = dump.boxes.first_mut() {
        a.parent = String::from("B");
    }
    if let Some(b) = dump.boxes.get_mut(1) {
        b.parent = String::from("A");
    }
    assert_eq!(
        malformed(&dump),
        Some(Malformed::ParentCycle(String::from("A")))
    );
}

#[test]
fn malformed_rejects_a_box_that_is_its_own_parent() {
    let mut dump = valid_dump();
    if let Some(a) = dump.boxes.first_mut() {
        a.parent = String::from("A");
    }
    assert_eq!(
        malformed(&dump),
        Some(Malformed::ParentCycle(String::from("A")))
    );
}

#[test]
fn malformed_rejects_an_unknown_route_end() {
    let mut dump = valid_dump();
    if let Some(r) = dump.routes.first_mut() {
        r.to = String::from("Z");
    }
    assert_eq!(
        malformed(&dump),
        Some(Malformed::UnknownRouteEnd {
            route: String::from("e0"),
            id: String::from("Z"),
        })
    );
}

#[test]
fn malformed_rejects_an_unknown_owner() {
    let mut dump = valid_dump();
    if let Some(l) = dump.labels.first_mut() {
        l.owner = String::from("Z");
    }
    assert_eq!(
        malformed(&dump),
        Some(Malformed::UnknownOwner {
            label: String::from("e0.label"),
            owner: String::from("Z"),
        })
    );
}

#[test]
fn malformed_rejects_a_coordinate_beyond_the_limit() {
    let limit = i32::try_from(COORD_LIMIT).unwrap_or(i32::MAX);
    let mut dump = valid_dump();
    if let Some(b) = dump.boxes.first_mut() {
        b.rect = rect(0, 0, limit + 1, 10);
    }
    assert_eq!(
        malformed(&dump),
        Some(Malformed::Coordinate(String::from("box A")))
    );
}

#[test]
fn malformed_rejects_a_route_point_beyond_the_limit() {
    let limit = i32::try_from(COORD_LIMIT).unwrap_or(i32::MAX);
    let mut dump = valid_dump();
    if let Some(r) = dump.routes.first_mut() {
        r.points.push(point(limit + 1, 0));
    }
    assert_eq!(
        malformed(&dump),
        Some(Malformed::Coordinate(String::from("route e0")))
    );
}

#[test]
fn malformed_rejects_a_negative_width() {
    let mut dump = valid_dump();
    if let Some(b) = dump.boxes.first_mut() {
        b.rect = rect(0, 0, -1, 10);
    }
    assert_eq!(
        malformed(&dump),
        Some(Malformed::InvalidRect(String::from("box A")))
    );
}

#[test]
fn malformed_rejects_a_label_beyond_the_limit() {
    let limit = i32::try_from(COORD_LIMIT).unwrap_or(i32::MAX);
    let mut dump = valid_dump();
    if let Some(l) = dump.labels.first_mut() {
        l.rect = rect(limit, 0, 4, 4);
    }
    assert_eq!(
        malformed(&dump),
        Some(Malformed::Coordinate(String::from("label e0.label")))
    );
}

#[test]
fn malformed_reasons_carry_the_printed_prefix() {
    let mut bad = valid_dump();
    bad.boxes.push(bbox("A", rect(40, 40, 10, 10)));
    let reason = malformed(&bad).map(|m| format!("malformed dump: {m}"));
    assert_eq!(
        reason,
        Some(String::from("malformed dump: box id A appears twice"))
    );
}

#[test]
fn ancestors_stop_on_a_parent_chain_that_returns() {
    let mut dump = valid_dump();
    if let Some(a) = dump.boxes.first_mut() {
        a.parent = String::from("B");
    }
    if let Some(b) = dump.boxes.get_mut(1) {
        b.parent = String::from("A");
    }
    let index = Index::new(&dump);
    let chain = index.ancestors("A");
    assert_eq!(chain.len(), dump.boxes.len());
}

#[test]
fn scope_and_owner_ancestors_follow_the_relations() {
    let mut dump = Dump::new("flowchart", DumpOptions::default());
    let mut outer = bbox("O", rect(0, 0, 100, 100));
    outer.role = BoxRole::Group;
    outer.exclusive = false;
    dump.boxes.push(outer);
    let mut inner = bbox("I", rect(0, 0, 50, 50));
    inner.role = BoxRole::Group;
    inner.parent = String::from("O");
    inner.exclusive = false;
    dump.boxes.push(inner);
    let mut a = bbox("A", rect(0, 0, 20, 20));
    a.parent = String::from("I");
    dump.boxes.push(a);
    let mut b = bbox("B", rect(60, 60, 20, 20));
    b.parent = String::from("O");
    dump.boxes.push(b);
    dump.routes
        .push(route("e0", "A", "B", vec![point(10, 20), point(70, 60)]));
    let index = Index::new(&dump);
    let scope: Vec<&str> = index.scope(&dump.routes[0]).into_iter().collect();
    assert_eq!(scope, ["A", "B", "I", "O"]);
    let owner: Vec<&str> = index.owner_ancestors("e0").into_iter().collect();
    assert_eq!(owner, ["I", "O"]);
    let boxed: Vec<&str> = index.owner_ancestors("B").into_iter().collect();
    assert_eq!(boxed, ["O"]);
}

#[test]
fn on_boundary_accepts_the_four_sides_and_rejects_the_interior() {
    let r = rect(0, 0, 10, 10);
    for p in [
        point(0, 0),
        point(10, 10),
        point(0, 5),
        point(10, 5),
        point(5, 0),
        point(5, 10),
    ] {
        assert!(on_boundary(p, r), "{p:?}");
    }
    for p in [point(5, 5), point(11, 0), point(-1, 0)] {
        assert!(!on_boundary(p, r), "{p:?}");
    }
}

#[test]
fn a_canvas_beyond_the_limit_is_malformed() {
    let dump = valid_dump();
    let limit = i32::try_from(COORD_LIMIT).unwrap_or(i32::MAX);
    let oversized = Size {
        w: limit + 1,
        h: 10,
    };
    assert_eq!(
        well_formed(oversized, &dump),
        Err(Malformed::Coordinate(String::from("canvas ")))
    );
}
