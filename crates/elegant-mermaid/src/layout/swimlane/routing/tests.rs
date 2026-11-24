use super::{Axis, Ends, Router, text_obstacles};
use crate::geom::{GeomError, Point, Rect};
use crate::scene::{Align, Group, GroupRole, Item, Run, TextItem, TextRole, TextStyle};

fn text_group(owner: &str, rect: Rect, align: Align, text: &str) -> Group {
    Group::new(GroupRole::Node, owner).with_items(vec![Item::Text(TextItem {
        rect,
        role: TextRole::Label,
        size: 14,
        align,
        style: TextStyle::Text,
        series: 0,
        lines: vec![vec![Run::plain(text)]],
    })])
}

#[test]
fn text_obstacles_reserve_centered_glyphs_without_blocking_a_clear_port_stub()
-> Result<(), GeomError> {
    let groups = [text_group(
        "source",
        Rect { x: 10, y: 5, w: 20, h: 1 },
        Align::Middle,
        "A",
    )];
    let obstacles = text_obstacles(Axis::Y, &groups)?;
    assert_eq!(obstacles.len(), 1);
    let obstacle = &obstacles[0];
    assert_eq!((obstacle.cross0, obstacle.cross1), (4, 7));
    assert_eq!((obstacle.rank0, obstacle.rank1), (18, 21));
    assert!(!obstacle.hits(
        Axis::Y.grid(Point { x: 30, y: 5 }),
        Axis::Y.grid(Point { x: 31, y: 5 })
    ));
    Ok(())
}

#[test]
fn assembled_routes_reject_text_in_either_port_stub() -> Result<(), GeomError> {
    let router = Router { axis: Axis::Y, slot: 2, bend: 4 };
    let ends = Ends {
        source: Point { x: 29, y: 5 },
        target: Point { x: 40, y: 5 },
        entry: router.axis.grid(Point { x: 31, y: 5 }),
        exit: router.axis.grid(Point { x: 38, y: 5 }),
        start_move: 2,
        end_move: 2,
    };
    for (owner, x) in [("source", 29), ("target", 39), ("unrelated", 29)] {
        let groups = [text_group(
            owner,
            Rect { x, y: 5, w: 1, h: 1 },
            Align::Start,
            "A",
        )];
        let text = text_obstacles(router.axis, &groups)?;
        assert_eq!(router.points(&[], &text, &ends), Err(GeomError::Domain));
    }
    assert_eq!(
        router.points(&[], &[], &ends)?,
        [ends.source, ends.target]
    );
    Ok(())
}
