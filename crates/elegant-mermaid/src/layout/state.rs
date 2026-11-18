use std::collections::BTreeSet;

use super::input::{
    Attachment, AttachmentSide, Box, Group, Input, Label, RegionSet, Route, SizeRule,
};
use crate::{
    geom::{GeomError, Size},
    model::state::{EndpointRole, Model, Parent, State, StateKind},
    scene::{BoxRole, Direction, DumpOptions, Profile, TextRole},
    source::Span,
};

mod paint;

pub(crate) fn from_state(
    model: &Model,
    profile: Profile,
    options: DumpOptions,
) -> Result<Input, GeomError> {
    let direction = model
        .scopes
        .first()
        .map_or("TB", |scope| scope.direction.as_str());
    let mut input = Input {
        kind: "state",
        profile,
        direction: Direction::from_token(direction).unwrap_or_default(),
        options,
        boxes: Vec::new(),
        routes: Vec::new(),
        labels: Vec::new(),
        groups: Vec::new(),
        sizes: Vec::new(),
        attachments: Vec::new(),
        region_sets: Vec::new(),
        spacing: super::input::Spacing::default(),
    };
    let mut names = Names::new(model);
    let region_ids: Vec<_> = model
        .regions
        .iter()
        .map(|region| names.claim(&region.id))
        .collect();
    let mut state_groups = vec![None; model.states.len()];
    for (index, state) in model.states.iter().enumerate() {
        append_state(&mut input, model, state, &region_ids)?;
        if state.composite.is_some() {
            state_groups[index] = Some(input.groups.len() - 1);
        }
    }
    let region_groups = append_regions(&mut input, model, &region_ids);
    append_region_sets(&mut input, model, &state_groups, &region_groups)?;
    append_notes(&mut input, model, &mut names)?;
    append_transitions(&mut input, model, &mut names);
    Ok(input)
}

fn parent_id(model: &Model, parent: Option<Parent>, regions: &[String]) -> String {
    match parent {
        Some(Parent::State(state)) => model.states[state].id.clone(),
        Some(Parent::Region(region)) => regions[region].clone(),
        None => String::new(),
    }
}

fn append_state(
    input: &mut Input,
    model: &Model,
    state: &State,
    regions: &[String],
) -> Result<(), GeomError> {
    let composite = state.composite.map(|index| &model.composites[index]);
    let scope_index = composite.map_or(state.scope, |group| group.scope);
    let scope = &model.scopes[scope_index];
    let direction = if scope.direction_span.is_some() {
        scope.direction.clone()
    } else {
        String::new()
    };
    let (shape, size) = state_shape(state, input.profile, &scope.direction)?;
    let text = if composite.is_some() {
        state
            .descriptions
            .first()
            .map_or_else(|| state.id.clone(), |text| text.value.clone())
    } else if shape == "roundedRect" {
        state_text(state)
    } else {
        String::new()
    };
    let parent = parent_id(model, state.parent, regions);
    input.boxes.push(Box {
        id: state.id.clone(),
        role: if composite.is_some() {
            BoxRole::Group
        } else {
            BoxRole::Node
        },
        icon: false,
        shape: if composite.is_some() {
            String::new()
        } else {
            shape.into()
        },
        parent: parent.clone(),
        exclusive: composite.is_none(),
        text,
        direction: direction.clone(),
    });
    input.sizes.push(if composite.is_some() {
        SizeRule::Measured
    } else {
        size
    });
    if composite.is_some() {
        input.groups.push(Group {
            id: state.id.clone(),
            parent,
            direction,
            direction_span: scope.direction_span.unwrap_or(Span { start: 0, end: 0 }),
        });
    }
    Ok(())
}

fn state_text(state: &State) -> String {
    if state.descriptions.is_empty() {
        return state.id.clone();
    }
    state
        .descriptions
        .iter()
        .map(|row| row.value.as_str())
        .collect::<Vec<_>>()
        .join("\n")
}

fn state_shape(
    state: &State,
    profile: Profile,
    direction: &str,
) -> Result<(&'static str, SizeRule), GeomError> {
    match state.kind {
        StateKind::Fork | StateKind::Join => {
            let length = constant(profile, "fork_length")?;
            let thickness = constant(profile, "fork_thickness")?;
            let horizontal = !matches!(
                Direction::from_token(direction),
                Some(Direction::Lr | Direction::Rl)
            );
            let size = if horizontal {
                Size {
                    w: length,
                    h: thickness,
                }
            } else {
                Size {
                    w: thickness,
                    h: length,
                }
            };
            Ok(("fork", SizeRule::Exact(size)))
        }
        StateKind::Choice => exact_square(profile, "choice", "choice_size"),
        StateKind::Default => match state.occurrences.last().map(|item| item.role) {
            Some(EndpointRole::Start) => exact_square(profile, "sm-circ", "start_size"),
            Some(EndpointRole::End) => exact_square(profile, "fr-circ", "end_size"),
            _ => Ok(("roundedRect", SizeRule::Measured)),
        },
    }
}

fn exact_square(
    profile: Profile,
    shape: &'static str,
    name: &str,
) -> Result<(&'static str, SizeRule), GeomError> {
    let side = constant(profile, name)?;
    Ok((shape, SizeRule::Exact(Size { w: side, h: side })))
}

fn constant(profile: Profile, name: &str) -> Result<i32, GeomError> {
    let key = format!("{}.state.{name}", profile.as_str());
    crate::r#gen::layoutconst::LAYOUT_CONST
        .iter()
        .find(|row| row.name == key)
        .map(|row| row.value)
        .ok_or(GeomError::Domain)
}

fn append_regions(input: &mut Input, model: &Model, ids: &[String]) -> Vec<usize> {
    let mut groups = Vec::with_capacity(model.regions.len());
    for (index, region) in model.regions.iter().enumerate() {
        let parent = model.states[model.composites[region.parent].state]
            .id
            .clone();
        let id = ids[index].clone();
        input.boxes.push(Box {
            id: id.clone(),
            role: BoxRole::Group,
            shape: String::new(),
            icon: false,
            parent: parent.clone(),
            exclusive: false,
            text: String::new(),
            direction: String::new(),
        });
        input.sizes.push(SizeRule::Measured);
        groups.push(input.groups.len());
        input.groups.push(Group {
            id,
            parent,
            direction: String::new(),
            direction_span: Span { start: 0, end: 0 },
        });
    }
    groups
}

fn append_region_sets(
    input: &mut Input,
    model: &Model,
    states: &[Option<usize>],
    regions: &[usize],
) -> Result<(), GeomError> {
    for composite in &model.composites {
        if composite.regions.is_empty() {
            continue;
        }
        let parent = states[composite.state].ok_or(GeomError::Domain)?;
        input.region_sets.push(RegionSet {
            parent,
            regions: composite
                .regions
                .iter()
                .map(|&index| regions[index])
                .collect(),
        });
    }
    Ok(())
}

fn append_notes(input: &mut Input, model: &Model, names: &mut Names) -> Result<(), GeomError> {
    for (target, state) in model.states.iter().enumerate() {
        let Some(index) = state.note else {
            continue;
        };
        let note = model.notes.get(index).ok_or(GeomError::Domain)?;
        if note.target != target {
            return Err(GeomError::Domain);
        }
        let id = names.claim(&format!("{}.note", state.id));
        let note_index = input.boxes.len();
        let (side, direction) = match note.position.as_str() {
            "left of" => (AttachmentSide::Left, "left"),
            "right of" => (AttachmentSide::Right, "right"),
            _ => return Err(GeomError::Domain),
        };
        input.boxes.push(Box {
            id,
            role: BoxRole::Node,
            shape: "note".into(),
            icon: false,
            parent: input.boxes[target].parent.clone(),
            exclusive: true,
            text: note.text.value.clone(),
            direction: direction.into(),
        });
        input.sizes.push(SizeRule::Measured);
        input.attachments.push(Attachment {
            target,
            note: note_index,
            side,
        });
    }
    Ok(())
}

fn append_transitions(input: &mut Input, model: &Model, names: &mut Names) {
    for (index, transition) in model.transitions.iter().enumerate() {
        let id = names.claim(&format!("e{index}"));
        let label = transition
            .label
            .as_ref()
            .filter(|label| !label.value.is_empty());
        if let Some(label) = label {
            input.labels.push(Label {
                id: names.claim(&format!("{id}.label")),
                owner: id.clone(),
                role: TextRole::Label,
                text: label.value.clone(),
            });
        }
        input.routes.push(Route {
            id,
            from: model.states[transition.from.state].id.clone(),
            to: model.states[transition.to.state].id.clone(),
            orthogonal: true,
            marker_start: "none".into(),
            marker_end: "point".into(),
            line: "normal".into(),
            min_length: if label.is_some() { 2 } else { 1 },
            from_side: None,
            to_side: None,
        });
    }
}

struct Names {
    used: BTreeSet<String>,
}
impl Names {
    fn new(model: &Model) -> Self {
        Self {
            used: model.states.iter().map(|state| state.id.clone()).collect(),
        }
    }
    fn claim(&mut self, preferred: &str) -> String {
        if self.used.insert(preferred.into()) {
            return preferred.into();
        }
        let mut suffix = 1usize;
        loop {
            let candidate = format!("{preferred}.{suffix}");
            if self.used.insert(candidate.clone()) {
                return candidate;
            }
            suffix += 1;
        }
    }
}

pub(super) fn layout(
    input: &Input,
) -> Result<(crate::scene::Scene, bool), super::layered::LayoutError> {
    let edges = input
        .routes
        .iter()
        .map(|route| {
            let min_length = i32::try_from(route.min_length)
                .map_err(|_| super::layered::LayoutError::Overflow)?;
            Ok(super::layered::pipeline::EdgeOptions {
                marker_start: None,
                marker_end: crate::scene::MarkerName::new("point"),
                stroke: &route.line,
                min_length,
            })
        })
        .collect::<Result<Vec<_>, super::layered::LayoutError>>()?;
    let (scene, budget) = super::layered::pipeline::layout_family(input, &edges)?;
    Ok((paint::paint(input, scene)?, budget))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn adapt(source: &str, profile: Profile) -> Result<Input, GeomError> {
        let parsed = crate::syntax::state::parse(source, &[]);
        assert!(
            parsed.diagnostics.is_empty(),
            "state fixture syntax diagnostics: {:?}",
            parsed.diagnostics
        );
        let (model, diagnostics) = crate::model::state::resolve(source, &parsed.document);
        assert!(
            diagnostics.is_empty(),
            "state fixture semantic diagnostics: {diagnostics:?}"
        );
        from_state(&model, profile, DumpOptions::default())
    }

    #[test]
    fn fixed_symbols_use_exact_sizes() -> Result<(), GeomError> {
        for profile in [Profile::Vector, Profile::Cell] {
            let input = adapt(
                "stateDiagram-v2\n[*] --> A\nA --> [*]\nstate forked <<fork>>\nstate decision <<choice>>\n",
                profile,
            )?;
            for (index, node) in input.boxes.iter().enumerate() {
                if node.shape != "roundedRect" {
                    assert!(
                        matches!(input.sizes[index], SizeRule::Exact(_)),
                        "symbol {} must bypass measured sizing",
                        node.id
                    );
                }
            }
        }
        Ok(())
    }

    #[test]
    fn final_note_and_duplicate_transitions_survive() -> Result<(), GeomError> {
        let input = adapt(
            "stateDiagram-v2\nA --> B: first\nA --> B: second\nnote left of A: old\nnote right of A: final\n",
            Profile::Cell,
        )?;
        assert_eq!(
            input.attachments.len(),
            1,
            "only the final attached note may enter layout"
        );
        let attachment = &input.attachments[0];
        assert_eq!(
            input.boxes[attachment.note].text, "final",
            "replacement note text must survive"
        );
        assert_eq!(
            input.routes.len(),
            2,
            "parallel transitions must remain separate"
        );
        assert_ne!(
            input.routes[0].id, input.routes[1].id,
            "parallel transitions need distinct identities"
        );
        Ok(())
    }

    #[test]
    fn empty_concurrent_regions_keep_declaration_order() -> Result<(), GeomError> {
        let input = adapt("stateDiagram-v2\nstate C {\n--\nA\n--\n}\n", Profile::Cell)?;
        assert_eq!(
            input.region_sets.len(),
            1,
            "concurrent composite must retain its region set"
        );
        assert_eq!(
            input.region_sets[0].regions.len(),
            3,
            "leading and trailing empty regions must survive"
        );
        for &region in &input.region_sets[0].regions {
            assert_eq!(
                input.groups[region].parent, "C",
                "all concurrent regions must share their composite parent"
            );
        }
        Ok(())
    }

    #[test]
    fn composite_source_route_starts_on_frame_top() -> Result<(), GeomError> {
        for profile in [Profile::Vector, Profile::Cell] {
            let input = adapt(
                "stateDiagram-v2\n  state Active {\n    A --> B\n    --\n    C --> D\n  }\n  Active --> A\n",
                profile,
            )?;
            let (scene, _) = layout(&input)?;
            let frame = scene
                .boxes()
                .iter()
                .find(|b| b.id == "Active")
                .ok_or(GeomError::Domain)?;
            let route = scene
                .routes()
                .iter()
                .find(|r| r.from == "Active" && r.to == "A")
                .ok_or(GeomError::Domain)?;
            let first = route.points.first().ok_or(GeomError::Domain)?;
            assert!(
                first.y == frame.rect.y
                    && first.x >= frame.rect.x
                    && first.x <= frame.rect.x + frame.rect.w,
                "{profile:?}: route from composite must start on the frame top edge, \
                 got {:?} with frame {:?}",
                first,
                frame.rect
            );
            let second = route.points.get(1).ok_or(GeomError::Domain)?;
            assert!(
                second.x == frame.rect.x
                    && second.y >= frame.rect.y
                    && second.y <= frame.rect.y + frame.rect.h,
                "{profile:?}: route from composite must leave through the frame left edge, \
                 got {:?} with frame {:?}",
                second,
                frame.rect
            );
            assert!(
                route
                    .points
                    .windows(2)
                    .all(|w| w[0].x == w[1].x || w[0].y == w[1].y),
                "{profile:?}: route must stay orthogonal, got {:?}",
                route.points
            );
        }
        Ok(())
    }
}
