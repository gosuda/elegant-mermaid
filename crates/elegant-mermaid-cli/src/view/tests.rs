use super::*;

#[test]
fn replay_revisions_continue_past_model_bound() {
    let mut viewer = Viewer {
        state: ViewState::new("diagram.mmd", 80, 24, Mode::Cells),
        options: Options::new("elegant-light"),
        colour: false,
        source: b"flowchart LR\nA --> B\n".to_vec(),
        image: None,
        scheduler: SchedulerState::initial(),
    };
    for _ in 0..12 {
        viewer.edited();
    }
    assert_eq!(viewer.scheduler.latest, 12);
    assert!(
        viewer.settle().is_ok(),
        "replay_revisions_continue_past_model_bound: expected {} to hold (observed false)",
        stringify!(viewer.settle().is_ok())
    );
    assert_eq!(viewer.state.displayed, 12);
    assert_eq!(viewer.state.frame_rev, 12);
    assert_eq!(viewer.scheduler.inflight, 0);
}

#[test]
fn stale_error_preserves_good_content() {
    let mut viewer = Viewer {
        state: ViewState::new("diagram.mmd", 80, 24, Mode::Cells),
        options: Options::new("elegant-light"),
        colour: false,
        source: b"flowchart LR\nA[alpha] --> B\n".to_vec(),
        image: None,
        scheduler: SchedulerState::initial(),
    };
    viewer.edited();
    assert!(
        viewer.settle().is_ok(),
        "stale_error_preserves_good_content: expected {} to hold (observed false)",
        stringify!(viewer.settle().is_ok())
    );
    let good = viewer.state.text.clone();
    viewer.source = b"unknown-kind\n".to_vec();
    viewer.edited();
    assert!(
        viewer.settle().is_ok(),
        "stale_error_preserves_good_content: expected {} to hold (observed false)",
        stringify!(viewer.settle().is_ok())
    );
    assert_eq!(viewer.state.text, good);
    assert_eq!(viewer.state.frame_rev, 1);
    assert_eq!(viewer.state.displayed, 2);
    assert_eq!(viewer.state.panel, Panel::Diagnostics);
}
