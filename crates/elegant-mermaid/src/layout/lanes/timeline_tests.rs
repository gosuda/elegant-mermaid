use super::*;
use crate::geom::Point;
use crate::layout::layered::LayoutError;
use crate::scene::{Direction, GroupRole, Profile, TextRole};

fn card(w: i32, h: i32) -> Text {
    Text {
        runs: Vec::new(),
        lines: vec!["t".to_owned()],
        w,
        h,
        role: TextRole::Label,
    }
}

fn period(section: Option<usize>, w: i32, events: &[i32]) -> TimelinePeriod {
    TimelinePeriod {
        id: "p".to_owned(),
        section,
        label: card(w, 1280),
        events: events
            .iter()
            .map(|&h| TimelineEvent {
                id: "e".to_owned(),
                link: "r".to_owned(),
                label: card(w, h),
            })
            .collect(),
    }
}

fn section(id: &str) -> TimelineSection {
    TimelineSection {
        id: id.to_owned(),
        label: card(100, 1280),
    }
}

fn input(
    direction: Direction,
    sections: Vec<TimelineSection>,
    periods: Vec<TimelinePeriod>,
) -> TimelineInput {
    TimelineInput {
        direction,
        title: None,
        sections,
        periods,
    }
}

fn plan(input: &TimelineInput, profile: Profile) -> TimelineResult {
    timeline(input, profile).unwrap()
}

#[test]
fn horizontal_columns_step_by_the_card_pitch() {
    let periods = vec![
        period(None, 100, &[]),
        period(None, 100, &[]),
        period(None, 100, &[]),
    ];
    let res = plan(&input(Direction::Lr, Vec::new(), periods), Profile::Vector);
    assert_eq!(res.periods[0].w, 9600);
    for i in 1..3 {
        assert_eq!(res.periods[i].x - res.periods[i - 1].x, 9600 + 3200);
        assert_eq!(res.periods[0].y, res.periods[i].y);
    }
}

#[test]
fn wide_label_widens_every_card() {
    let periods = vec![period(None, 100, &[]), period(None, 12000, &[])];
    let res = plan(&input(Direction::Lr, Vec::new(), periods), Profile::Vector);
    assert_eq!(res.periods[0].w, 12000 + 2 * 1280);
    assert_eq!(res.periods[0].w, res.periods[1].w);
}

#[test]
fn section_band_spans_its_periods_and_an_empty_section_keeps_one_slot() {
    let sections = vec![section("s0"), section("s1"), section("s2")];
    let periods = vec![
        period(Some(0), 100, &[]),
        period(Some(0), 100, &[]),
        period(Some(2), 100, &[]),
    ];
    let res = plan(&input(Direction::Lr, sections, periods), Profile::Vector);
    let pitch = 9600 + 3200;
    assert_eq!(res.sections[0].w, 2 * pitch - 3200);
    assert_eq!(res.sections[1].w, pitch - 3200);
    assert_eq!(res.sections[0].x + 2 * pitch, res.sections[1].x);
    assert_eq!(res.sections[1].x + pitch, res.sections[2].x);
    assert_eq!(res.sections[2].x, res.periods[2].x);
    assert_eq!(
        res.sections[0].y + res.sections[0].h + 3200,
        res.periods[0].y
    );
}

#[test]
fn periods_before_the_first_section_come_first() {
    let periods = vec![period(Some(0), 100, &[]), period(None, 100, &[])];
    let res = plan(
        &input(Direction::Lr, vec![section("s0")], periods),
        Profile::Cell,
    );
    assert!(res.periods[1].x < res.periods[0].x);
    assert_eq!(res.periods[0].x, res.sections[0].x);
}

#[test]
fn events_stack_under_their_period_separated_by_the_event_gap() {
    let periods = vec![period(None, 100, &[1280, 2560, 1280])];
    let res = plan(&input(Direction::Lr, Vec::new(), periods), Profile::Vector);
    let events = &res.events[0];
    assert_eq!(events.len(), 3);
    assert_eq!(res.periods[0].y + res.periods[0].h + 3200, events[0].y);
    for i in 1..3 {
        assert_eq!(events[i - 1].y + events[i - 1].h + 640, events[i].y);
        assert_eq!(res.periods[0].x, events[i].x);
    }
    assert_eq!(events[1].h, 2 * 1280 + 2560);
    let cx = res.periods[0].x + res.periods[0].w / 2;
    assert_eq!(
        res.routes[0][0],
        vec![
            Point {
                x: cx,
                y: res.periods[0].y + res.periods[0].h
            },
            Point {
                x: cx,
                y: events[0].y
            }
        ]
    );
    assert_eq!(
        res.routes[0][1],
        vec![
            Point {
                x: cx,
                y: events[0].y + events[0].h
            },
            Point {
                x: cx,
                y: events[1].y
            }
        ]
    );
}

#[test]
fn axis_runs_between_the_period_row_and_the_first_event() {
    let periods = vec![period(None, 100, &[1280])];
    let res = plan(&input(Direction::Lr, Vec::new(), periods), Profile::Vector);
    let bottom = res.periods[0].y + res.periods[0].h;
    let axis = &res.groups[0];
    assert_eq!(axis.role, GroupRole::Decor);
    assert!(!axis.items.is_empty());
    assert!(bottom < res.events[0][0].y);
}

#[test]
fn vertical_puts_events_in_a_second_column() {
    let periods = vec![
        period(Some(0), 100, &[1280, 1280]),
        period(Some(0), 100, &[1280]),
    ];
    let res = plan(
        &input(Direction::Tb, vec![section("s0")], periods),
        Profile::Vector,
    );
    assert_eq!(res.periods[0].x, res.periods[1].x);
    assert_eq!(
        res.periods[0].x + res.periods[0].w + 3200,
        res.events[0][0].x
    );
    assert_eq!(res.events[0][0].x, res.events[1][0].x);
    assert_eq!(res.periods[0].w, res.sections[0].w);
    assert!(res.periods[1].y > res.events[0][1].y);
    for route in &res.routes[0] {
        assert!(crate::geom::is_orthogonal(route));
        assert_eq!(route[0].x, res.periods[0].x + res.periods[0].w);
    }
}

#[test]
fn vertical_row_keeps_a_straight_route_when_the_centres_align() {
    let periods = vec![period(None, 100, &[1280])];
    let res = plan(&input(Direction::Tb, Vec::new(), periods), Profile::Vector);
    assert_eq!(res.routes[0][0].len(), 2);
}

#[test]
fn title_is_centred_over_the_content() {
    let mut graph = input(Direction::Lr, Vec::new(), vec![period(None, 100, &[])]);
    graph.title = Some(TimelineTitle {
        id: "title".to_owned(),
        label: card(2000, 1536),
    });
    let res = plan(&graph, Profile::Vector);
    assert_eq!(res.title.w, 2000);
    assert_eq!(
        res.periods[0].x + res.periods[0].w / 2,
        res.title.x + res.title.w / 2
    );
    assert_eq!(res.title.y + res.title.h + 640, res.periods[0].y);
}

#[test]
fn period_with_an_unknown_section_is_rejected() {
    let graph = input(
        Direction::Lr,
        vec![section("s0")],
        vec![period(Some(1), 100, &[])],
    );
    assert!(matches!(
        timeline(&graph, Profile::Vector),
        Err(LayoutError::Domain)
    ));
}

#[test]
fn empty_input_still_has_an_axis_and_a_canvas() {
    for profile in [Profile::Vector, Profile::Cell] {
        let res = plan(&input(Direction::Lr, Vec::new(), Vec::new()), profile);
        assert!(res.canvas.w > 0);
        assert!(res.canvas.h > 0);
    }
}

#[test]
fn result_coordinates_are_never_negative() {
    let mut graph = input(
        Direction::Tb,
        vec![section("s0")],
        vec![period(Some(0), 8, &[1, 2]), period(None, 8, &[])],
    );
    graph.title = Some(TimelineTitle {
        id: "title".to_owned(),
        label: card(30, 1),
    });
    for profile in [Profile::Vector, Profile::Cell] {
        let res = plan(&graph, profile);
        let mut rects = vec![res.title];
        rects.extend(res.sections.iter().copied());
        rects.extend(res.periods.iter().copied());
        for events in &res.events {
            rects.extend(events.iter().copied());
        }
        for r in rects {
            assert!(r.x >= 0 && r.y >= 0);
            assert!(r.x + r.w <= res.canvas.w);
            assert!(r.y + r.h <= res.canvas.h);
        }
    }
}
