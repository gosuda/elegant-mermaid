//! The Wardley family entry: measure, arrange, place, and assemble the scene.

use crate::scene::{Direction, Dump, DumpOptions, Scene};

use super::LayoutError;
use super::wardley::Wardley;
use super::wardley_plan::Plan;

pub(crate) const KIND: &str = "wardley";

pub fn layout_wardley(w: &Wardley, options: &DumpOptions) -> Result<(Scene, bool), LayoutError> {
    let mut plan = Plan::new(w, options)?;
    plan.measure_all()?;
    plan.arrange();
    plan.place_labels()?;
    plan.grow();
    plan.place_boxes()?;
    plan.build_routes()?;
    let canvas = plan.canvas()?;
    let mut dump_options = options.clone();
    dump_options.direction = Direction::Tb;
    let mut dump = Dump::new(KIND, dump_options);
    dump.boxes = plan.dump_boxes();
    dump.routes = plan.routes.clone();
    dump.labels = plan.dump_labels();
    let groups = plan.groups()?;
    Ok((Scene::new(canvas, dump, groups), false))
}
