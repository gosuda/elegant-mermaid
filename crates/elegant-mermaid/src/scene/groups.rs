use super::{BoxRole, Dump, Item};

/// The role of a group.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GroupRole {
    /// A decoration under the diagram, over it, or both.
    Decor,
    /// A frame: one group for each dump box with role `group`.
    Group,
    /// One group for each dump route.
    Edge,
    /// One group for each dump box with role `node`.
    Node,
}

impl GroupRole {
    /// The role name of the group's class attribute.
    pub const fn as_str(self) -> &'static str {
        match self {
            GroupRole::Decor => "decor",
            GroupRole::Group => "group",
            GroupRole::Edge => "edge",
            GroupRole::Node => "node",
        }
    }
}

/// One group of the display list: a role, an owner, and its primitives.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Group {
    /// The group role.
    pub role: GroupRole,
    /// The id of the dump box for roles `group` and `node`, the id of the dump route for
    /// role `edge`, and the empty string for `decor`.
    pub owner: String,
    /// The primitives, in draw order.
    pub items: Vec<Item>,
}

impl Group {
    /// A group of one role with one owner.
    pub fn new(role: GroupRole, owner: impl Into<String>) -> Group {
        Group {
            role,
            owner: owner.into(),
            items: Vec::new(),
        }
    }

    /// The same group with its items replaced.
    pub fn with_items(mut self, items: Vec<Item>) -> Group {
        self.items = items;
        self
    }
}

/// The first violation of the group rules of `spec/scene.md`.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum GroupOrder {
    /// A decor group is neither the first group nor the last group.
    #[error("group {group} is neither the leading nor the trailing decor group")]
    UnexpectedDecor {
        /// The group index.
        group: usize,
    },
    /// A decor group carries an owner.
    #[error("decor group {group} carries the owner {owner}")]
    DecorOwner {
        /// The group index.
        group: usize,
        /// The owner the group carries.
        owner: String,
    },
    /// A group draws an owner other than the one its place calls for.
    #[error("group {group} draws {expected} {owner_expected}, not {owner}")]
    OwnerMismatch {
        /// The group index.
        group: usize,
        /// The group role the place calls for.
        expected: &'static str,
        /// The owner the place calls for.
        owner_expected: String,
        /// The owner the group carries.
        owner: String,
    },
    /// A group draws an owner that the dump does not hold.
    #[error("group {group} draws a {role} that the dump does not hold")]
    UnexpectedGroup {
        /// The group index.
        group: usize,
        /// The group role.
        role: &'static str,
    },
    /// A dump box or route has no group.
    #[error("{role} {id} has no group")]
    MissingGroup {
        /// The group role that is missing.
        role: &'static str,
        /// The owner id that has no group.
        id: String,
    },
    /// A group places an item of an earlier class after a later one.
    #[error("group {group} places a {later} item after a {earlier} item")]
    ItemOrder {
        /// The group index.
        group: usize,
        /// The class of the earlier item.
        earlier: &'static str,
        /// The class of the later item.
        later: &'static str,
    },
}

/// One owner that the body groups must draw, in group order.
struct Expected {
    role: GroupRole,
    owner: String,
}

/// The owners that the body groups must draw, in the group order of `spec/scene.md`: one
/// group per dump box with role `group`, then one per dump route, then one per dump box
/// with role `node`.
fn expected_owners(dump: &Dump) -> Vec<Expected> {
    let mut expected = Vec::new();
    let groups = dump.boxes.iter().filter(|b| b.role == BoxRole::Group);
    expected.extend(groups.map(|b| Expected {
        role: GroupRole::Group,
        owner: b.id.clone(),
    }));
    expected.extend(dump.routes.iter().map(|r| Expected {
        role: GroupRole::Edge,
        owner: r.id.clone(),
    }));
    let nodes = dump.boxes.iter().filter(|b| b.role == BoxRole::Node);
    expected.extend(nodes.map(|b| Expected {
        role: GroupRole::Node,
        owner: b.id.clone(),
    }));
    expected
}

/// Checks the group rules of `spec/scene.md`: at most one decor group before and one after
/// the body, one group per dump owner in dump order, an empty owner for decor, and the item
/// classes of a group in non-decreasing order.
pub fn check_groups(groups: &[Group], dump: &Dump) -> Result<(), GroupOrder> {
    let last = groups.len().saturating_sub(1);
    for (index, group) in groups.iter().enumerate() {
        check_item_order(index, &group.items)?;
        if group.role != GroupRole::Decor {
            continue;
        }
        if !group.owner.is_empty() {
            return Err(GroupOrder::DecorOwner {
                group: index,
                owner: group.owner.clone(),
            });
        }
        if index != 0 && index != last {
            return Err(GroupOrder::UnexpectedDecor { group: index });
        }
    }
    let expected = expected_owners(dump);
    let body: Vec<(usize, &Group)> = groups
        .iter()
        .enumerate()
        .filter(|(_, group)| group.role != GroupRole::Decor)
        .collect();
    for (position, (index, group)) in body.iter().enumerate() {
        let Some(want) = expected.get(position) else {
            return Err(GroupOrder::UnexpectedGroup {
                group: *index,
                role: group.role.as_str(),
            });
        };
        if want.role != group.role || want.owner != group.owner {
            return Err(GroupOrder::OwnerMismatch {
                group: *index,
                expected: want.role.as_str(),
                owner_expected: want.owner.clone(),
                owner: group.owner.clone(),
            });
        }
    }
    match expected.get(body.len()) {
        None => Ok(()),
        Some(want) => Err(GroupOrder::MissingGroup {
            role: want.role.as_str(),
            id: want.owner.clone(),
        }),
    }
}

/// Checks that the item classes of one group do not decrease.
fn check_item_order(group: usize, items: &[Item]) -> Result<(), GroupOrder> {
    items.windows(2).try_for_each(|pair| {
        let earlier = pair[0].class();
        let later = pair[1].class();
        if later < earlier {
            return Err(GroupOrder::ItemOrder {
                group,
                earlier: earlier.as_str(),
                later: later.as_str(),
            });
        }
        Ok(())
    })
}
