use crate::geom::{Point, Rect, Size, is_orthogonal, polyline_hits_rect};
use crate::layout::layered::LayoutError;
use crate::scene::{GroupRole, Item, Profile, Run, TextRole};

use super::{
    EventFrame, EventLane, EventModelingInput, EventModelingResult, EventRelation, Text,
    event_modeling,
};

fn sized(w: i32, h: i32) -> Text {
    Text {
        runs: vec![vec![Run::plain("t")]],
        lines: vec!["t".to_owned()],
        w,
        h,
        role: TextRole::Label,
    }
}

fn lanes(indices: &[i64]) -> Vec<EventLane> {
    indices
        .iter()
        .map(|&index| EventLane {
            id: "lane".to_owned(),
            index,
            label: None,
        })
        .collect()
}

fn frames(lane_of: &[usize]) -> Vec<EventFrame> {
    lane_of
        .iter()
        .map(|&lane| EventFrame {
            id: String::new(),
            lane,
            category: String::new(),
            name: sized(0, 0),
            data: None,
        })
        .collect()
}

fn relation(from: usize, to: usize) -> EventRelation {
    EventRelation {
        id: String::new(),
        from,
        to,
    }
}

fn plan(input: &EventModelingInput, profile: Profile) -> EventModelingResult {
    event_modeling(input, profile).unwrap()
}

fn point(x: i32, y: i32) -> Point {
    Point { x, y }
}

#[test]
fn columns_keep_same_lane_boxes_disjoint() {
    let input = EventModelingInput {
        lanes: lanes(&[0, 100, 200]),
        frames: frames(&[0, 1, 2, 0, 1]),
        relations: Vec::new(),
    };
    let res = plan(&input, Profile::Vector);
    let x: Vec<i32> = res.frames.iter().map(|r| r.x).collect();
    let y: Vec<i32> = res.frames.iter().map(|r| r.y).collect();
    assert_eq!(x, [17024, 18944, 20864, 24064, 25984]);
    assert_eq!(y, [1984, 10944, 19904, 1984, 10944]);
    assert!(x[0] + res.frames[0].w <= x[3]);
    assert!(x[1] + res.frames[1].w <= x[4]);
}

#[test]
fn lanes_stack_with_gaps_and_grow_to_their_tallest_box() {
    let mut tall = frames(&[0, 1]);
    tall[1].name = sized(100, 100_000);
    let input = EventModelingInput {
        lanes: lanes(&[0, 100]),
        frames: tall,
        relations: Vec::new(),
    };
    let res = plan(&input, Profile::Vector);
    assert_eq!(res.lanes[0].h, 8320);
    assert_eq!(res.lanes[1].h, 48000 + 1280 + 1920);
    assert_eq!(res.lanes[0].y + res.lanes[0].h + 640, res.lanes[1].y);
    assert_eq!(res.frames[1].h, 48000 + 1280);
    assert_eq!(res.lanes[1].y + 960, res.frames[1].y);
    assert_eq!(res.lanes[0].w, res.lanes[1].w);
}

#[test]
fn lane_order_follows_index_then_position() {
    let input = EventModelingInput {
        lanes: lanes(&[200, 0, 0]),
        frames: frames(&[0, 1, 2]),
        relations: Vec::new(),
    };
    let res = plan(&input, Profile::Cell);
    assert!(res.lanes[1].y < res.lanes[2].y);
    assert!(res.lanes[2].y < res.lanes[0].y);
}

#[test]
fn frame_size_clamps_and_adds_the_data_block() {
    let mut list = frames(&[0, 0]);
    list[0].name = sized(100, 1280);
    list[1].name = sized(6000, 1280);
    list[1].data = Some(sized(50000, 2 * 1280));
    let input = EventModelingInput {
        lanes: lanes(&[0]),
        frames: list,
        relations: Vec::new(),
    };
    let res = plan(&input, Profile::Vector);
    assert_eq!(res.frames[0].w, 5120 + 1280);
    assert_eq!(res.frames[0].h, 5120 + 1280);
    assert_eq!(res.frames[1].w, 28800 + 1280);
    assert_eq!(res.frames[1].h, 5120 + 1280);
}

#[test]
fn gutter_widens_for_long_lane_labels() {
    let mut list = lanes(&[0]);
    list[0].label = Some(sized(20000, 1280));
    let input = EventModelingInput {
        lanes: list,
        frames: frames(&[0]),
        relations: Vec::new(),
    };
    let res = plan(&input, Profile::Vector);
    assert_eq!(res.frames[0].x, 23840 + 1024);
    assert_eq!(res.lane_labels[0].x, 1920 + 1024);
    assert!(res.lane_labels[0].x + res.lane_labels[0].w <= res.frames[0].x - 1920);
}

#[test]
fn adjacent_lanes_draw_one_straight_segment_in_vector_and_a_corridor_in_cells() {
    let input = EventModelingInput {
        lanes: lanes(&[0, 100]),
        frames: frames(&[0, 1]),
        relations: vec![relation(0, 1)],
    };
    let vector = plan(&input, Profile::Vector);
    assert_eq!(vector.routes[0], [point(21290, 8384), point(21077, 10944)]);
    let cell = plan(&input, Profile::Cell);
    assert_eq!(
        cell.routes[0],
        [point(34, 9), point(34, 10), point(35, 10), point(35, 12)]
    );
}

#[test]
fn upward_relation_starts_at_the_source_top_and_ends_at_the_target_bottom() {
    let input = EventModelingInput {
        lanes: lanes(&[0, 100]),
        frames: frames(&[1, 0]),
        relations: vec![relation(0, 1)],
    };
    let res = plan(&input, Profile::Vector);
    let route = &res.routes[0];
    assert_eq!(route[0].y, res.frames[0].y);
    assert_eq!(route.last().unwrap().y, res.frames[1].y + res.frames[1].h);
}

#[test]
fn relation_around_a_box_in_the_way_stays_orthogonal_and_clear() {
    let input = EventModelingInput {
        lanes: lanes(&[0, 100, 200]),
        frames: frames(&[0, 1, 2]),
        relations: vec![relation(0, 2)],
    };
    let res = plan(&input, Profile::Vector);
    let want = [
        point(21290, 8384),
        point(21290, 9664),
        point(27904, 9664),
        point(27904, 18624),
        point(22997, 18624),
        point(22997, 19904),
    ];
    assert_eq!(res.routes[0], want);
    assert!(is_orthogonal(&res.routes[0]));
    assert!(!polyline_hits_rect(&res.routes[0], res.frames[1]).unwrap());
}

#[test]
fn same_lane_relation_loops_above_the_lane() {
    let input = EventModelingInput {
        lanes: lanes(&[0]),
        frames: frames(&[0, 0]),
        relations: vec![relation(0, 1)],
    };
    let res = plan(&input, Profile::Vector);
    let want = [
        point(21290, 1984),
        point(21290, 1504),
        point(26197, 1504),
        point(26197, 1984),
    ];
    assert_eq!(res.routes[0], want);
}

#[test]
fn self_relation_is_a_closed_loop_on_the_top_edge() {
    let input = EventModelingInput {
        lanes: lanes(&[0]),
        frames: frames(&[0]),
        relations: vec![relation(0, 0)],
    };
    let res = plan(&input, Profile::Cell);
    let route = &res.routes[0];
    assert_eq!(route.len(), 4);
    assert_eq!(route[0].y, res.frames[0].y);
    assert_eq!(route[3].y, res.frames[0].y);
    assert!(route[1].y < route[0].y);
}

fn on_boundary(p: Point, r: Rect) -> bool {
    let inside = p.x >= r.x && p.x <= r.x + r.w && p.y >= r.y && p.y <= r.y + r.h;
    inside && (p.x == r.x || p.x == r.x + r.w || p.y == r.y || p.y == r.y + r.h)
}

#[test]
fn endpoints_lie_on_their_box_boundaries() {
    let input = EventModelingInput {
        lanes: lanes(&[0, 100, 200]),
        frames: frames(&[0, 1, 2, 1, 0]),
        relations: vec![
            relation(0, 1),
            relation(2, 0),
            relation(4, 3),
            relation(3, 3),
        ],
    };
    for profile in [Profile::Vector, Profile::Cell] {
        let res = plan(&input, profile);
        for (i, link) in input.relations.iter().enumerate() {
            let route = &res.routes[i];
            assert!(on_boundary(route[0], res.frames[link.from]), "{i} start");
            assert!(
                on_boundary(*route.last().unwrap(), res.frames[link.to]),
                "{i} end"
            );
        }
    }
}

#[test]
fn canvas_contains_every_rect() {
    let mut list = lanes(&[0, 100]);
    list[1].label = Some(sized(3000, 2560));
    let input = EventModelingInput {
        lanes: list,
        frames: frames(&[0, 1, 0]),
        relations: vec![relation(0, 1)],
    };
    let res = plan(&input, Profile::Vector);
    for rect in res.lanes.iter().chain(&res.frames).chain(&res.lane_labels) {
        assert!(rect.x >= 0 && rect.y >= 0);
        assert!(rect.x + rect.w <= res.canvas.w);
        assert!(rect.y + rect.h <= res.canvas.h);
    }
}

#[test]
fn input_indices_are_checked() {
    let bad_frame = EventModelingInput {
        lanes: lanes(&[0]),
        frames: frames(&[1]),
        relations: Vec::new(),
    };
    assert_eq!(
        event_modeling(&bad_frame, Profile::Cell).unwrap_err(),
        LayoutError::Domain
    );
    let bad_relation = EventModelingInput {
        lanes: lanes(&[0]),
        frames: frames(&[0]),
        relations: vec![relation(0, 1)],
    };
    assert_eq!(
        event_modeling(&bad_relation, Profile::Cell).unwrap_err(),
        LayoutError::Domain
    );
}

#[test]
fn empty_input_has_a_margin_only_canvas() {
    let res = plan(&EventModelingInput::default(), Profile::Cell);
    assert_eq!(res.canvas, Size { w: 2, h: 2 });
}

#[test]
fn paint_order_and_styles() {
    let mut list = lanes(&[0, 100]);
    list[1].id = String::new();
    let mut members = frames(&[0, 1]);
    members[0].id = "a".to_owned();
    members[0].category = "ui".to_owned();
    members[1].id = "b".to_owned();
    members[1].category = "command".to_owned();
    let input = EventModelingInput {
        lanes: list,
        frames: members,
        relations: vec![EventRelation {
            id: "e0".to_owned(),
            from: 0,
            to: 1,
        }],
    };
    let res = plan(&input, Profile::Vector);
    let roles: Vec<GroupRole> = res.groups.iter().map(|g| g.role).collect();
    assert_eq!(
        roles,
        [
            GroupRole::Group,
            GroupRole::Edge,
            GroupRole::Node,
            GroupRole::Node
        ]
    );
    assert_eq!(res.groups[0].owner, "lane");
    assert_eq!(res.groups[1].owner, "e0");
    let style = |group: usize| match &res.groups[group].items[0] {
        Item::RoundRect(item) => item.shape.style.name(),
        _ => "other",
    };
    assert_eq!(style(2), "node");
    assert_eq!(style(3), "note");
    let marker = match &res.groups[1].items[1] {
        Item::MarkerRef(marker) => Some(marker),
        _ => None,
    }
    .unwrap();
    assert_eq!(marker.marker.as_str(), "point");
    assert_eq!(Some(&marker.at), res.routes[0].last());
}
