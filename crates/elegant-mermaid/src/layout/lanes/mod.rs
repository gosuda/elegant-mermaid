//! The lanes layout family (`spec/layout/lanes.md`).
//!
//! Lane planners take a decoded input of measured texts and return integer geometry and
//! scene groups. The first kind of the family is gitgraph.

mod constants;
mod eventmodeling;
mod eventmodeling_constants;
mod eventmodeling_result;
mod gitgraph;
mod journey;
mod journey_constants;
mod journey_paint;
mod journey_result;
mod paint;
mod result;
mod timeline;
mod timeline_constants;
mod timeline_paint;
mod timeline_result;

pub(crate) use eventmodeling::{
    EventFrame, EventLane, EventModelingInput, EventModelingResult, EventRelation, event_modeling,
};
pub(crate) use eventmodeling_constants::event_modeling_wraps;
pub(crate) use gitgraph::{Branch, Commit, GitGraphInput, GitGraphResult, Link, Text, git_graph};
pub(crate) use journey::{
    JourneyInput, JourneyResult, JourneySection, JourneyTask, JourneyTitle, journey,
};
pub(crate) use timeline::{
    TimelineEvent, TimelineInput, TimelinePeriod, TimelineResult, TimelineSection, TimelineTitle,
    timeline,
};
#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod eventmodeling_tests;
#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod journey_tests;
#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod tests;
#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod timeline_tests;
