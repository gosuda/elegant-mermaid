use std::collections::BTreeMap;

use super::*;
use crate::layout::input::Attachment;

pub(super) fn validate(input: &Input) -> Result<(), LayoutError> {
    if input.attachments.is_empty() {
        return Ok(());
    }
    let ids: BTreeMap<_, _> = input
        .boxes
        .iter()
        .enumerate()
        .map(|(index, item)| (item.id.as_str(), index))
        .collect();
    if ids.len() != input.boxes.len() {
        return Err(LayoutError::Domain);
    }
    let parents = parents(input, &ids)?;
    validate_parent_chains(&parents)?;
    validate_pairs(input)
}

fn parents(input: &Input, ids: &BTreeMap<&str, usize>) -> Result<Vec<Option<usize>>, LayoutError> {
    input
        .boxes
        .iter()
        .map(|item| {
            if item.parent.is_empty() {
                return Ok(None);
            }
            let index = *ids.get(item.parent.as_str()).ok_or(LayoutError::Domain)?;
            if input.boxes[index].role != BoxRole::Group {
                return Err(LayoutError::Domain);
            }
            Ok(Some(index))
        })
        .collect()
}

fn validate_parent_chains(parents: &[Option<usize>]) -> Result<(), LayoutError> {
    for (start, _) in parents.iter().enumerate() {
        let mut cursor = Some(start);
        let mut depth = 0;
        while let Some(index) = cursor {
            depth += 1;
            if depth > 65 {
                return Err(LayoutError::Domain);
            }
            cursor = parents[index];
        }
    }
    Ok(())
}

fn validate_pairs(input: &Input) -> Result<(), LayoutError> {
    let mut targets = vec![false; input.boxes.len()];
    let mut notes = vec![false; input.boxes.len()];
    for attachment in &input.attachments {
        let target = input
            .boxes
            .get(attachment.target)
            .ok_or(LayoutError::Domain)?;
        let note = input
            .boxes
            .get(attachment.note)
            .ok_or(LayoutError::Domain)?;
        if attachment.target == attachment.note
            || notes[attachment.target]
            || notes[attachment.note]
            || targets[attachment.note]
            || target.parent != note.parent
            || note.role != BoxRole::Node
        {
            return Err(LayoutError::Domain);
        }
        targets[attachment.target] = true;
        notes[attachment.note] = true;
    }
    Ok(())
}

pub(in crate::layout::layered) fn project(
    input: &Input,
    retained: &[bool],
) -> Result<Vec<Attachment>, LayoutError> {
    if retained.len() != input.boxes.len() {
        return Err(LayoutError::Domain);
    }
    let mut next = 0;
    let mapping: Vec<_> = retained
        .iter()
        .map(|&keep| {
            if !keep {
                return None;
            }
            let index = next;
            next += 1;
            Some(index)
        })
        .collect();
    let mut result = Vec::new();
    for attachment in &input.attachments {
        let target = *mapping.get(attachment.target).ok_or(LayoutError::Domain)?;
        let note = *mapping.get(attachment.note).ok_or(LayoutError::Domain)?;
        match (target, note) {
            (Some(target), Some(note)) => result.push(Attachment {
                target,
                note,
                side: attachment.side,
            }),
            (None, None) => {}
            _ => return Err(LayoutError::Domain),
        }
    }
    Ok(result)
}

pub(super) fn connect(graph: &mut Graph, input: &Input) {
    graph
        .edges
        .extend(input.attachments.iter().map(|attachment| Edge {
            tail: attachment.target,
            head: attachment.note,
            min_len: 1,
            decl: i32::MAX,
            reversed: false,
        }));
}
