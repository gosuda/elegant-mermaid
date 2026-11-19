/// Revision cap used by the model and by the reachability test.
#[cfg(test)]
pub const MAX_REV: u64 = 4;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct SchedulerState {
    pub latest: u64,
    pub inflight: u64,
    pub cancelled: bool,
    pub displayed: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Event {
    Edited,
    RenderDone,
    RenderAborted,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Command {
    None,
    StartRender(u64),
    CancelRender(u64),
    Display(u64),
}

impl SchedulerState {
    pub fn initial() -> Self {
        Self::default()
    }

    pub fn enabled(self, event: Event) -> bool {
        match event {
            Event::Edited => true,
            Event::RenderDone => self.inflight != 0,
            Event::RenderAborted => self.inflight != 0 && self.cancelled,
        }
    }

    pub fn displayed_not_ahead(self) -> bool {
        self.displayed <= self.latest
    }

    pub fn idle_means_current(self) -> bool {
        self.inflight != 0 || self.displayed == self.latest
    }

    pub fn inflight_is_newer(self) -> bool {
        self.inflight == 0 || self.inflight > self.displayed
    }

    pub fn cancelled_means_stale(self) -> bool {
        self.cancelled == (self.inflight != 0 && self.inflight < self.latest)
    }

    #[cfg(test)]
    pub fn in_bounds(self) -> bool {
        let in_range = |value: u64| value <= MAX_REV;
        in_range(self.latest) && in_range(self.inflight) && in_range(self.displayed)
    }

    pub fn invariants_hold(self) -> bool {
        self.displayed_not_ahead()
            && self.idle_means_current()
            && self.inflight_is_newer()
            && self.cancelled_means_stale()
    }
}

pub fn step(state: SchedulerState, event: Event) -> (SchedulerState, Command) {
    if !state.enabled(event) {
        return (state, Command::None);
    }
    match event {
        Event::Edited => edited(state),
        Event::RenderDone => render_done(state),
        Event::RenderAborted => render_aborted(state),
    }
}

fn edited(state: SchedulerState) -> (SchedulerState, Command) {
    let mut next = state;
    let Some(latest) = state.latest.checked_add(1) else {
        return (state, Command::None);
    };
    next.latest = latest;
    if state.inflight == 0 {
        next.inflight = next.latest;
        next.cancelled = false;
        return (next, Command::StartRender(next.latest));
    }
    if state.cancelled {
        return (next, Command::None);
    }
    next.cancelled = true;
    (next, Command::CancelRender(state.inflight))
}

fn render_done(state: SchedulerState) -> (SchedulerState, Command) {
    let mut next = state;
    if state.cancelled {
        next.inflight = state.latest;
        next.cancelled = false;
        return (next, Command::StartRender(next.latest));
    }
    next.displayed = state.inflight;
    next.inflight = 0;
    (next, Command::Display(next.displayed))
}

fn render_aborted(state: SchedulerState) -> (SchedulerState, Command) {
    let mut next = state;
    next.inflight = state.latest;
    next.cancelled = false;
    (next, Command::StartRender(next.latest))
}

#[cfg(test)]
mod tests {
    use super::{Command, Event, MAX_REV, SchedulerState, step};
    use std::collections::{BTreeSet, VecDeque};

    fn events(state: SchedulerState) -> Vec<Event> {
        let mut candidates = vec![Event::RenderDone, Event::RenderAborted];
        if state.latest < MAX_REV {
            candidates.push(Event::Edited);
        }
        candidates
            .into_iter()
            .filter(|event| state.enabled(*event))
            .collect()
    }

    fn reachable() -> BTreeSet<SchedulerState> {
        let start = SchedulerState::initial();
        let mut seen = BTreeSet::new();
        let mut queue = VecDeque::new();
        seen.insert(start);
        queue.push_back(start);
        while let Some(state) = queue.pop_front() {
            for event in events(state) {
                let (next, _) = step(state, event);
                if seen.insert(next) {
                    queue.push_back(next);
                }
            }
        }
        seen
    }

    #[test]
    fn scheduler_reachable() {
        let states = reachable();
        assert_eq!(states.len(), 25);
        let mut saw_terminal = false;
        for state in &states {
            assert!(
                state.displayed_not_ahead(),
                "scheduler_reachable: expected {} to hold (observed false)",
                stringify!(state.displayed_not_ahead())
            );
            assert!(
                state.idle_means_current(),
                "scheduler_reachable: expected {} to hold (observed false)",
                stringify!(state.idle_means_current())
            );
            assert!(
                state.inflight_is_newer(),
                "scheduler_reachable: expected {} to hold (observed false)",
                stringify!(state.inflight_is_newer())
            );
            assert!(
                state.cancelled_means_stale(),
                "scheduler_reachable: expected {} to hold (observed false)",
                stringify!(state.cancelled_means_stale())
            );
            assert!(
                state.in_bounds(),
                "scheduler_reachable: expected {} to hold (observed false)",
                stringify!(state.in_bounds())
            );
            let terminal = state.latest == MAX_REV
                && state.inflight == 0
                && !state.cancelled
                && state.displayed == MAX_REV;
            saw_terminal |= terminal;
        }
        assert!(
            saw_terminal,
            "scheduler_reachable: expected {} to hold (observed false)",
            stringify!(saw_terminal)
        );
    }

    #[test]
    fn edited_starts_the_first_render() {
        let start = SchedulerState::initial();
        let (next, command) = step(start, Event::Edited);
        assert_eq!(next.latest, 1);
        assert_eq!(next.inflight, 1);
        assert!(
            !next.cancelled,
            "edited_starts_the_first_render: expected {} to hold (observed false)",
            stringify!(!next.cancelled)
        );
        assert_eq!(next.displayed, 0);
        assert_eq!(command, Command::StartRender(1));
    }

    #[test]
    fn edited_while_rendering_cancels_once() {
        let state = SchedulerState {
            latest: 1,
            inflight: 1,
            cancelled: false,
            displayed: 0,
        };
        let (second, second_command) = step(state, Event::Edited);
        assert_eq!(second.latest, 2);
        assert_eq!(second.inflight, 1);
        assert!(
            second.cancelled,
            "edited_while_rendering_cancels_once: expected {} to hold (observed false)",
            stringify!(second.cancelled)
        );
        assert_eq!(second_command, Command::CancelRender(1));
        let (third, third_command) = step(second, Event::Edited);
        assert_eq!(third.latest, 3);
        assert_eq!(third.inflight, 1);
        assert!(
            third.cancelled,
            "edited_while_rendering_cancels_once: expected {} to hold (observed false)",
            stringify!(third.cancelled)
        );
        assert_eq!(third_command, Command::None);
    }

    #[test]
    fn render_done_restarts_the_stale_revision() {
        let state = SchedulerState {
            latest: 3,
            inflight: 1,
            cancelled: true,
            displayed: 0,
        };
        let (next, command) = step(state, Event::RenderDone);
        assert_eq!(next.latest, 3);
        assert_eq!(next.inflight, 3);
        assert!(
            !next.cancelled,
            "render_done_restarts_the_stale_revision: expected {} to hold (observed false)",
            stringify!(!next.cancelled)
        );
        assert_eq!(next.displayed, 0);
        assert_eq!(command, Command::StartRender(3));
    }

    #[test]
    fn render_done_displays_the_inflight_revision() {
        let state = SchedulerState {
            latest: 2,
            inflight: 2,
            cancelled: false,
            displayed: 1,
        };
        let (next, command) = step(state, Event::RenderDone);
        assert_eq!(next.displayed, 2);
        assert_eq!(next.inflight, 0);
        assert_eq!(command, Command::Display(2));
    }

    #[test]
    fn render_aborted_restarts_the_latest_revision() {
        let state = SchedulerState {
            latest: 4,
            inflight: 2,
            cancelled: true,
            displayed: 1,
        };
        let (next, command) = step(state, Event::RenderAborted);
        assert_eq!(next.inflight, 4);
        assert!(
            !next.cancelled,
            "render_aborted_restarts_the_latest_revision: expected {} to hold (observed false)",
            stringify!(!next.cancelled)
        );
        assert_eq!(next.displayed, 1);
        assert_eq!(command, Command::StartRender(4));
    }

    #[test]
    fn disabled_events_leave_the_state_unchanged() {
        let idle = SchedulerState {
            latest: 2,
            inflight: 0,
            cancelled: false,
            displayed: 2,
        };
        for event in [Event::RenderDone, Event::RenderAborted] {
            let (next, command) = step(idle, event);
            assert_eq!(next, idle);
            assert_eq!(command, Command::None);
        }
        let running = SchedulerState {
            latest: 2,
            inflight: 1,
            cancelled: false,
            displayed: 0,
        };
        let (next, command) = step(running, Event::RenderAborted);
        assert_eq!(next, running);
        assert_eq!(command, Command::None);
    }
}
