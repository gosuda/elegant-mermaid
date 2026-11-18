use super::*;
use crate::geom::{Point, Rect};
use crate::layout::layered::LayoutError;
use crate::scene::{Direction, GroupRole, Profile, TextRole};

fn text(w: i32, h: i32) -> Text {
    Text {
        runs: Vec::new(),
        lines: vec!["t".to_owned()],
        w,
        h,
        role: TextRole::Label,
    }
}

fn branch(id: &str, order: i64) -> Branch {
    Branch {
        id: id.to_owned(),
        order,
        label: None,
    }
}

fn commit(id: &str, branch: usize) -> Commit {
    Commit {
        id: id.to_owned(),
        branch,
        kind: "commit".to_owned(),
        label: None,
        tags: Vec::new(),
    }
}

fn link(id: &str, from: usize, to: usize, pick: bool) -> Link {
    Link {
        id: id.to_owned(),
        from,
        to,
        pick,
    }
}

fn plan(
    branches: Vec<Branch>,
    commits: Vec<Commit>,
    links: Vec<Link>,
    direction: Direction,
    profile: Profile,
) -> Result<GitGraphResult, LayoutError> {
    git_graph(
        &GitGraphInput {
            direction,
            show_branches: true,
            rotate_labels: true,
            branches,
            commits,
            links,
        },
        profile,
    )
}

fn straight(
    branches: Vec<Branch>,
    commits: Vec<Commit>,
    links: Vec<Link>,
    direction: Direction,
    profile: Profile,
) -> GitGraphResult {
    plan(branches, commits, links, direction, profile).expect("plan")
}

#[test]
fn lane_order_key_is_order_then_declaration() {
    let branches = vec![
        branch("main", 0),
        branch("test1", 1),
        branch("test2", 0),
        branch("test3", 0),
    ];
    let commits = vec![
        commit("a", 0),
        commit("b", 1),
        commit("c", 2),
        commit("d", 3),
    ];
    let res = straight(
        branches,
        commits,
        Vec::new(),
        Direction::Lr,
        Profile::Vector,
    );
    let y = |i: usize| res.points[i].y;
    let pitch = y(2) - y(0);
    assert_eq!(pitch, 5760);
    assert_eq!(y(3) - y(0), 2 * pitch);
    assert_eq!(y(1) - y(0), 3 * pitch);
}

#[test]
fn order_ties_fall_back_to_declaration_index() {
    let branches = vec![branch("m", 0), branch("a", 0), branch("b", 0)];
    let commits = vec![commit("x", 2), commit("y", 1), commit("z", 0)];
    let res = straight(
        branches,
        commits,
        Vec::new(),
        Direction::Lr,
        Profile::Vector,
    );
    assert!(res.points[2].y < res.points[1].y);
    assert!(res.points[1].y < res.points[0].y);
}

#[test]
fn commit_steps_follow_the_longest_parent_chain() {
    let branches = vec![branch("m", 0), branch("d", 0), branch("p", 0)];
    let commits = vec![
        commit("a", 0),
        commit("b", 0),
        commit("c", 1),
        commit("d", 1),
        commit("e", 0),
        commit("pick", 2),
    ];
    let links = vec![
        link("", 0, 1, false),
        link("", 1, 2, false),
        link("", 2, 3, false),
        link("", 1, 4, false),
        link("", 3, 4, false),
        link("", 3, 5, true),
    ];
    let res = straight(branches, commits, links, Direction::Lr, Profile::Cell);
    let x = |i: usize| res.points[i].x - res.points[0].x;
    let steps: Vec<i32> = (0..6).map(x).collect();
    assert_eq!(steps, [0, 4, 8, 12, 16, 0]);
}

#[test]
fn backward_links_do_not_move_commits() {
    let commits = vec![commit("a", 0), commit("b", 1)];
    let links = vec![link("", 1, 0, false), link("", 0, 0, false)];
    let res = straight(
        vec![branch("m", 0), branch("d", 0)],
        commits,
        links,
        Direction::Lr,
        Profile::Cell,
    );
    assert_eq!(res.points[0].x, res.points[1].x);
}

fn commits_with_only_a_backward_parent_on_the_last() -> (Vec<Commit>, Vec<Link>) {
    let commits = vec![
        labelled("a", 0, 6, &[]),
        labelled("b", 0, 6, &[]),
        labelled("c", 0, 6, &[]),
    ];
    (commits, vec![link("", 0, 1, false), link("", 2, 0, false)])
}

#[test]
fn commit_with_only_a_backward_parent_still_advances_past_its_lane_predecessor() {
    let (commits, links) = commits_with_only_a_backward_parent_on_the_last();
    let res = straight(
        vec![branch("m", 0)],
        commits,
        links,
        Direction::Lr,
        Profile::Cell,
    );
    for i in 1..3 {
        let (prev, next) = (res.commit_labels[i - 1], res.commit_labels[i]);
        assert!(res.points[i].x > res.points[i - 1].x, "{i}");
        assert!(next.x - right(prev) >= 2, "{i}");
    }
}

#[test]
fn commit_with_only_a_backward_parent_still_advances_vertically() {
    for direction in [Direction::Tb, Direction::Bt] {
        let (commits, links) = commits_with_only_a_backward_parent_on_the_last();
        let res = straight(
            vec![branch("m", 0)],
            commits,
            links,
            direction,
            Profile::Cell,
        );
        for i in 1..3 {
            assert_eq!(
                (res.points[i].y - res.points[i - 1].y).abs(),
                4,
                "{direction:?}"
            );
        }
        assert_eq!(
            (res.points[2].y - res.points[0].y).abs(),
            8,
            "{direction:?}"
        );
    }
}

#[test]
fn cross_lane_connector_is_orthogonal_with_a_half_step_turn() {
    let branches = vec![branch("m", 0), branch("d", 0)];
    let commits = vec![commit("a", 0), commit("b", 1), commit("c", 0)];
    let links = vec![link("", 0, 1, false), link("", 0, 2, false)];
    let res = straight(branches, commits, links, Direction::Lr, Profile::Vector);
    let (a, b, c) = (res.points[0], res.points[1], res.points[2]);
    let turn = b.x - 1280;
    assert_eq!(
        res.routes[0],
        vec![a, Point { x: turn, y: a.y }, Point { x: turn, y: b.y }, b]
    );
    assert_eq!(res.routes[1], vec![a, c]);
    assert_eq!(a.y, c.y);
}

#[test]
fn vertical_directions_transpose_the_commit_axis() {
    let branches = vec![branch("m", 0), branch("d", 0)];
    let commits = vec![commit("a", 0), commit("b", 1), commit("c", 1)];
    let links = vec![link("", 0, 1, false), link("", 1, 2, false)];
    let tb = straight(
        branches.clone(),
        commits.clone(),
        links.clone(),
        Direction::Tb,
        Profile::Cell,
    );
    let bt = straight(branches, commits, links, Direction::Bt, Profile::Cell);
    for res in [&tb, &bt] {
        assert_eq!(res.points[1].x - res.points[0].x, 2);
        assert_eq!(res.points[1].x, res.points[2].x);
    }
    assert_eq!(tb.points[1].y - tb.points[0].y, 4);
    assert_eq!(tb.points[2].y - tb.points[1].y, 4);
    assert_eq!(bt.points[1].y - bt.points[0].y, -4);
    assert_eq!(bt.points[2].y - bt.points[1].y, -4);
    assert_eq!(tb.points[1].x, bt.points[1].x);
}

#[test]
fn vertical_lanes_widen_for_side_text() {
    let branches = vec![branch("m", 0), branch("d", 0)];
    let narrow = straight(
        branches.clone(),
        vec![commit("a", 0), commit("b", 1)],
        Vec::new(),
        Direction::Tb,
        Profile::Cell,
    );
    let mut first = commit("a", 0);
    first.label = Some(text(6, 1));
    first.tags = vec![text(3, 1)];
    let wide = straight(
        branches,
        vec![first, commit("b", 1)],
        Vec::new(),
        Direction::Tb,
        Profile::Cell,
    );
    let gap = |r: &GitGraphResult| r.points[1].x - r.points[0].x;
    assert_eq!(gap(&narrow), 2);
    assert_eq!(gap(&wide), 2 + 1 + 6 + 1 + 3);
    assert_eq!(wide.commit_labels[0].x, wide.points[0].x + 1);
    assert_eq!(wide.tag_labels[0][0].x, wide.commit_labels[0].x + 6 + 1);
}

#[test]
fn lane_frames_are_segments_through_their_commits() {
    let mut main = branch("m", 0);
    main.label = Some(text(40, 1280));
    let branches = vec![main, branch("d", 0)];
    let commits = vec![commit("a", 0), commit("b", 1)];
    for direction in [Direction::Lr, Direction::Tb, Direction::Bt] {
        let res = straight(
            branches.clone(),
            commits.clone(),
            vec![link("", 0, 1, false)],
            direction,
            Profile::Vector,
        );
        for (i, lane) in res.lanes.iter().enumerate() {
            assert!(lane.w == 0 || lane.h == 0, "{direction:?}");
            let p = res.points[i];
            assert!(
                lane.x <= p.x && p.x <= lane.x + lane.w && lane.y <= p.y && p.y <= lane.y + lane.h,
                "{direction:?}"
            );
        }
    }
}

#[test]
fn label_placement_lr() {
    let mut first = commit("a", 0);
    first.label = Some(text(2560, 1280));
    first.tags = vec![text(1280, 1280), text(1280, 1280)];
    let res = straight(
        vec![branch("m", 0)],
        vec![first],
        Vec::new(),
        Direction::Lr,
        Profile::Vector,
    );
    let p = res.points[0];
    assert_eq!(
        res.commit_labels[0],
        Rect {
            x: p.x - 1280,
            y: p.y + 640,
            w: 2560,
            h: 1280
        }
    );
    assert_eq!(
        res.tag_labels[0][0],
        Rect {
            x: p.x - 640,
            y: p.y - 1024 - 1280,
            w: 1280,
            h: 1280
        }
    );
    assert_eq!(
        res.tag_labels[0][1].y,
        res.tag_labels[0][0].y - (1280 + 512)
    );
}

#[test]
fn canvas_keeps_everything_inside_the_margin() {
    let mut main = branch("m", 0);
    main.label = Some(text(500, 1280));
    let mut first = commit("a", 0);
    first.label = Some(text(3000, 1280));
    first.tags = vec![text(900, 1280)];
    for profile in [Profile::Vector, Profile::Cell] {
        let res = straight(
            vec![main.clone()],
            vec![first.clone()],
            Vec::new(),
            Direction::Lr,
            profile,
        );
        let mut rects = vec![res.commit_labels[0], res.branch_labels[0]];
        rects.extend(res.tag_labels[0].iter().copied());
        rects.extend(res.lanes.iter().copied());
        for r in rects {
            assert!(r.x >= 0 && r.y >= 0);
            assert!(r.x + r.w <= res.canvas.w);
            assert!(r.y + r.h <= res.canvas.h);
        }
    }
}

#[test]
fn scene_group_order_and_owners() {
    let mut lane = branch("lane0", 0);
    lane.label = Some(text(40, 1280));
    let res = straight(
        vec![lane],
        vec![commit("a", 0), commit("b", 0)],
        vec![link("e0", 0, 1, false)],
        Direction::Lr,
        Profile::Cell,
    );
    let roles: Vec<GroupRole> = res.groups.iter().map(|g| g.role).collect();
    let owners: Vec<&str> = res.groups.iter().map(|g| g.owner.as_str()).collect();
    assert_eq!(
        roles,
        [
            GroupRole::Group,
            GroupRole::Edge,
            GroupRole::Node,
            GroupRole::Node
        ]
    );
    assert_eq!(owners, ["lane0", "e0", "a", "b"]);
}

#[test]
fn rotate_commit_labels_adds_lane_room() {
    let branches = vec![branch("m", 0), branch("d", 0)];
    let commits = vec![commit("a", 0), commit("b", 1)];
    let gap = |rotate: bool| {
        let res = git_graph(
            &GitGraphInput {
                direction: Direction::Lr,
                show_branches: false,
                rotate_labels: rotate,
                branches: branches.clone(),
                commits: commits.clone(),
                links: Vec::new(),
            },
            Profile::Vector,
        )
        .expect("plan");
        res.points[1].y - res.points[0].y
    };
    assert_eq!(gap(false), 3200);
    assert_eq!(gap(true), 3200 + 2560);
}

#[test]
fn overflow_is_typed() {
    let n = 300_000;
    let commits: Vec<Commit> = (0..n).map(|_| commit("", 0)).collect();
    let links: Vec<Link> = (1..n).map(|i| link("", i - 1, i, false)).collect();
    let result = plan(
        vec![branch("m", 0)],
        commits,
        links,
        Direction::Lr,
        Profile::Vector,
    );
    assert!(matches!(result, Err(LayoutError::Overflow)));
}

fn labelled(id: &str, branch: usize, w: i32, tags: &[i32]) -> Commit {
    let mut commit = commit(id, branch);
    commit.label = Some(text(w, 1));
    commit.tags = tags.iter().map(|&tag| text(tag, 1)).collect();
    commit
}

fn chain(n: usize) -> Vec<Link> {
    (1..n).map(|i| link("", i - 1, i, false)).collect()
}

fn right(rect: Rect) -> i32 {
    rect.x + rect.w
}

#[test]
fn commit_gap_widens_to_keep_adjacent_labels_apart() {
    for [a, b] in [[6, 6], [5, 6], [6, 5], [1, 1], [20, 3]] {
        let commits = vec![labelled("a", 0, a, &[]), labelled("b", 0, b, &[])];
        let res = straight(
            vec![branch("m", 0)],
            commits,
            chain(2),
            Direction::Lr,
            Profile::Cell,
        );
        let (first, second) = (res.commit_labels[0], res.commit_labels[1]);
        assert!(second.x - right(first) >= 2, "{a} {b}");
        assert_eq!(
            res.points[1].x - res.points[0].x,
            4.max((a + b + 1) / 2 + 2),
            "{a} {b}"
        );
    }
}

#[test]
fn commit_gap_uses_vector_units() {
    let commits = vec![labelled("a", 0, 6400, &[]), labelled("b", 0, 3200, &[])];
    let res = straight(
        vec![branch("m", 0)],
        commits,
        chain(2),
        Direction::Lr,
        Profile::Vector,
    );
    let (first, second) = (res.commit_labels[0], res.commit_labels[1]);
    assert_eq!(res.points[1].x - res.points[0].x, 4800 + 1536);
    assert!(second.x - right(first) >= 1536);
}

#[test]
fn tags_widen_the_commit_gap() {
    let commits = vec![labelled("a", 0, 1, &[21]), labelled("b", 0, 1, &[])];
    let res = straight(
        vec![branch("m", 0)],
        commits,
        chain(2),
        Direction::Lr,
        Profile::Cell,
    );
    assert_eq!(res.points[1].x - res.points[0].x, 11 + 2);
    let (tag, label) = (res.tag_labels[0][0], res.commit_labels[1]);
    assert!(label.x - right(tag) >= 2);
}

#[test]
fn commit_gap_uses_the_widest_commit_of_each_level() {
    let branches = vec![branch("m", 0), branch("d", 0)];
    let commits = vec![
        labelled("a", 0, 2, &[]),
        labelled("x", 1, 10, &[]),
        labelled("b", 0, 2, &[]),
    ];
    let links = vec![link("", 0, 2, false), link("", 1, 2, false)];
    let res = straight(branches, commits, links, Direction::Lr, Profile::Cell);
    assert_eq!(res.points[0].x, res.points[1].x);
    assert_eq!(res.points[2].x - res.points[0].x, 6 + 2);
}

#[test]
fn unlabelled_commits_keep_the_commit_step() {
    let commits = vec![commit("a", 0), commit("b", 0), commit("c", 0)];
    let cell = straight(
        vec![branch("m", 0)],
        commits.clone(),
        chain(3),
        Direction::Lr,
        Profile::Cell,
    );
    assert_eq!(cell.points[2].x - cell.points[0].x, 8);
    let vector = straight(
        vec![branch("m", 0)],
        commits,
        chain(3),
        Direction::Lr,
        Profile::Vector,
    );
    assert_eq!(vector.points[2].x - vector.points[0].x, 5120);
}

#[test]
fn vertical_directions_ignore_label_width() {
    let commits = vec![labelled("a", 0, 30, &[]), labelled("b", 0, 30, &[])];
    for direction in [Direction::Tb, Direction::Bt] {
        let res = straight(
            vec![branch("m", 0)],
            commits.clone(),
            chain(2),
            direction,
            Profile::Cell,
        );
        assert_eq!((res.points[1].y - res.points[0].y).abs(), 4);
    }
}

#[test]
fn lane_gap_clears_the_label_band_above_the_tag_band() {
    let branches = vec![branch("m", 0), branch("d", 1)];
    for (profile, height, tag_pad) in [(Profile::Cell, 1, 0), (Profile::Vector, 1280, 256)] {
        let upper = Commit {
            label: Some(text(3, height)),
            ..commit("a", 0)
        };
        let lower = Commit {
            label: Some(text(3, height)),
            tags: vec![text(3, height), text(3, height)],
            ..commit("b", 1)
        };
        let res = straight(
            branches.clone(),
            vec![upper, lower],
            Vec::new(),
            Direction::Lr,
            profile,
        );
        let (label, top_tag) = (res.commit_labels[0], res.tag_labels[1][1]);
        assert!(label.y + label.h <= top_tag.y - tag_pad, "{profile:?}");
        if profile == Profile::Cell {
            assert_eq!(res.points[1].y - res.points[0].y, 2 + 2);
        }
    }
}

#[test]
fn lane_gap_keeps_the_base_pitch_without_tags() {
    let branches = vec![branch("m", 0), branch("d", 1)];
    let commits = vec![labelled("a", 0, 3, &[]), labelled("b", 1, 3, &[])];
    let res = straight(branches, commits, Vec::new(), Direction::Lr, Profile::Cell);
    assert_eq!(res.points[1].y - res.points[0].y, 2);
}

#[test]
fn bottom_to_top_branch_label_clears_the_lane_end() {
    for (profile, clearance) in [(Profile::Cell, 1), (Profile::Vector, 512)] {
        let mut main = branch("m", 0);
        main.label = Some(text(40, 1280));
        let res = straight(
            vec![main],
            vec![commit("a", 0)],
            Vec::new(),
            Direction::Bt,
            profile,
        );
        let (lane, label) = (res.lanes[0], res.branch_labels[0]);
        assert_eq!(lane.y + lane.h + clearance, label.y, "{profile:?}");
    }
}

#[test]
fn vertical_pitch_clears_branch_label_plates() {
    let mut main = branch("m", 0);
    main.label = Some(text(10, 1));
    let mut dev = branch("d", 1);
    dev.label = Some(text(10, 1));
    let res = straight(
        vec![main, dev],
        vec![commit("a", 0), commit("b", 1)],
        Vec::new(),
        Direction::Tb,
        Profile::Cell,
    );
    assert_eq!(res.points[1].x - res.points[0].x, 10 + 2);
    assert!(right(res.branch_labels[0]) <= res.branch_labels[1].x);
}

#[test]
fn right_to_left_is_not_a_gitgraph_direction() {
    for profile in [Profile::Vector, Profile::Cell] {
        let result = plan(
            vec![branch("m", 0)],
            vec![commit("a", 0)],
            Vec::new(),
            Direction::Rl,
            profile,
        );
        assert!(matches!(result, Err(LayoutError::Domain)), "{profile:?}");
    }
}

#[test]
fn every_supported_gitgraph_direction_lays_out() {
    for direction in [Direction::Lr, Direction::Tb, Direction::Bt] {
        for profile in [Profile::Vector, Profile::Cell] {
            straight(
                vec![branch("m", 0)],
                vec![commit("a", 0)],
                Vec::new(),
                direction,
                profile,
            );
        }
    }
}
