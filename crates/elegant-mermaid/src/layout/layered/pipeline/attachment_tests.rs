use super::*;
use crate::layout::input::{
    Attachment, AttachmentSide, Box as InputBox, Group as InputGroup, Route as InputRoute,
};

fn input(profile: Profile, direction: Direction) -> Input {
    Input {
        kind: "state",
        profile,
        direction,
        options: DumpOptions {
            profile,
            thoroughness: 1,
            ..DumpOptions::default()
        },
        boxes: Vec::new(),
        routes: Vec::new(),
        labels: Vec::new(),
        groups: Vec::new(),
        sizes: Vec::new(),
        attachments: Vec::new(),
    }
}

fn node(input: &mut Input, id: &str, parent: &str) -> usize {
    let index = input.boxes.len();
    input.boxes.push(InputBox {
        id: id.into(),
        role: BoxRole::Node,
        shape: String::new(),
        parent: parent.into(),
        exclusive: true,
        text: id.into(),
        direction: String::new(),
    });
    input.sizes.push(SizeRule::Measured);
    index
}

fn group(input: &mut Input, id: &str, parent: &str) -> usize {
    let index = node(input, id, parent);
    input.boxes[index].role = BoxRole::Group;
    input.boxes[index].exclusive = false;
    input.groups.push(InputGroup {
        id: id.into(),
        parent: parent.into(),
        direction: String::new(),
        direction_span: crate::source::Span { start: 0, end: 0 },
    });
    index
}

fn edge(input: &mut Input, from: &str, to: &str, label: &str) {
    let id = format!("e{}", input.routes.len());
    if !label.is_empty() {
        input.labels.push(crate::layout::input::Label {
            id: format!("{id}.label"),
            owner: id.clone(),
            role: TextRole::Label,
            text: label.into(),
        });
    }
    input.routes.push(InputRoute {
        id,
        from: from.into(),
        to: to.into(),
        orthogonal: true,
        marker_start: String::new(),
        marker_end: String::new(),
        line: "solid".into(),
        min_length: 1,
    });
}

fn attach(input: &mut Input, target: usize, note: usize, side: AttachmentSide) {
    input.attachments.push(Attachment { target, note, side });
    let from = input.boxes[note].id.clone();
    let to = input.boxes[target].id.clone();
    edge(input, &from, &to, "");
}

fn render(input: &Input) -> Result<Scene, LayoutError> {
    let edges: Vec<_> = input
        .routes
        .iter()
        .map(|_| EdgeOptions {
            marker_start: None,
            marker_end: None,
            stroke: "",
            min_length: 1,
        })
        .collect();
    layout_family(input, &edges).map(|(scene, _)| scene)
}

fn assert_attachments(input: &Input, scene: &Scene) -> Result<(), LayoutError> {
    let dump = scene.dump_part();
    assert_eq!(
        dump.boxes.len(),
        input.boxes.len(),
        "no algorithmic envelope reaches the dump"
    );
    assert_eq!(dump.routes.len(), input.routes.len());
    for attachment in &input.attachments {
        let target = dump.boxes[attachment.target].rect;
        let note = dump.boxes[attachment.note].rect;
        match attachment.side {
            AttachmentSide::Left => {
                assert!(
                    i64::from(note.x) + i64::from(note.w) <= i64::from(target.x),
                    "left note must end before its target begins: note={note:?}, target={target:?}"
                )
            }
            AttachmentSide::Right => {
                assert!(
                    i64::from(target.x) + i64::from(target.w) <= i64::from(note.x),
                    "right note must begin after its target ends: target={target:?}, note={note:?}"
                )
            }
        }
    }
    assert_eq!(
        crate::scene::validate(scene.canvas(), dump)?,
        None,
        "{}",
        scene.dump()
    );
    Ok(())
}

#[test]
fn attachments_preserve_screen_sides_and_exact_loop_targets() -> Result<(), LayoutError> {
    for profile in [Profile::Cell, Profile::Vector] {
        for direction in [Direction::Tb, Direction::Bt, Direction::Lr, Direction::Rl] {
            let mut input = input(profile, direction);
            node(&mut input, "unrelated", "");
            node(&mut input, "source", "");
            let target = node(&mut input, "target", "");
            input.boxes[target].text.clear();
            let side = if profile == Profile::Cell { 1 } else { 896 };
            input.sizes[target] = SizeRule::Exact(Size { w: side, h: side });
            node(&mut input, "exit", "");
            let left = node(&mut input, "left", "");
            let right = node(&mut input, "right", "");
            let left_again = node(&mut input, "left_again", "");
            attach(&mut input, target, left, AttachmentSide::Left);
            attach(&mut input, target, right, AttachmentSide::Right);
            attach(&mut input, target, left_again, AttachmentSide::Left);
            edge(&mut input, "source", "target", "incoming");
            edge(&mut input, "target", "exit", "outgoing");
            edge(&mut input, "exit", "target", "back");
            edge(&mut input, "target", "target", "first loop");
            edge(&mut input, "target", "target", "second loop");
            let scene = render(&input)?;
            assert_attachments(&input, &scene)?;
            let rect = scene.dump_part().boxes[target].rect;
            assert_eq!((rect.w, rect.h), (side, side));
        }
    }
    Ok(())
}

#[test]
fn attachments_follow_actual_nested_composite_frames_with_external_transitions()
-> Result<(), LayoutError> {
    for profile in [Profile::Cell, Profile::Vector] {
        for direction in [Direction::Tb, Direction::Bt, Direction::Lr, Direction::Rl] {
            let mut input = input(profile, direction);
            node(&mut input, "unrelated", "");
            node(&mut input, "outside", "");
            group(&mut input, "outer", "");
            let target = group(&mut input, "composite", "outer");
            group(&mut input, "nested", "composite");
            input.groups[1].direction = "BT".into();
            input.boxes[target].direction = "BT".into();
            node(&mut input, "a", "nested");
            node(&mut input, "b", "nested");
            let left = node(&mut input, "left", "outer");
            let right = node(&mut input, "right", "outer");
            attach(&mut input, target, left, AttachmentSide::Left);
            attach(&mut input, target, right, AttachmentSide::Right);
            edge(&mut input, "a", "b", "internal label wider than a title");
            edge(&mut input, "b", "b", "internal loop");
            edge(&mut input, "outside", "a", "enter");
            edge(&mut input, "b", "outside", "leave");
            let inner_target = input
                .boxes
                .iter()
                .position(|item| item.id == "a")
                .ok_or(LayoutError::Domain)?;
            let inner_note = node(&mut input, "inner_note", "nested");
            attach(&mut input, inner_target, inner_note, AttachmentSide::Right);
            edge(&mut input, "outside", "left", "note entry");
            edge(&mut input, "right", "outside", "note exit");
            let scene = render(&input)?;
            assert_attachments(&input, &scene)?;
            let rect = scene.dump_part().boxes[target].rect;
            assert!(
                rect.w > 0,
                "a populated composite must retain positive frame width: frame={rect:?}"
            );
        }
    }
    Ok(())
}

#[test]
fn attachments_project_sparse_indices_through_local_direction_isolation() -> Result<(), LayoutError>
{
    let mut input = input(Profile::Cell, Direction::Tb);
    node(&mut input, "unrelated", "");
    group(&mut input, "local", "");
    input.groups[0].direction = "RL".into();
    input.boxes[1].direction = "RL".into();
    node(&mut input, "preceding", "local");
    let target = node(&mut input, "target", "local");
    let note = node(&mut input, "note", "local");
    attach(&mut input, target, note, AttachmentSide::Left);
    input.routes.clear();
    edge(&mut input, "preceding", "target", "");
    let scene = render(&input)?;
    assert_attachments(&input, &scene)
}

#[test]
fn malformed_attachment_indices_and_ownership_return_domain() {
    let mut input = input(Profile::Cell, Direction::Tb);
    let target = node(&mut input, "target", "");
    let note = node(&mut input, "note", "");
    attach(&mut input, target, note, AttachmentSide::Left);
    input.attachments[0].note = usize::MAX;
    assert_eq!(
        attachment_metadata::validate(&input),
        Err(LayoutError::Domain)
    );
    input.attachments[0].note = note;
    input.boxes[note].parent = "missing".into();
    assert_eq!(
        attachment_metadata::validate(&input),
        Err(LayoutError::Domain)
    );
    input.boxes[note].parent.clear();
    input.attachments.push(input.attachments[0]);
    assert_eq!(
        attachment_metadata::validate(&input),
        Err(LayoutError::Domain)
    );
}
