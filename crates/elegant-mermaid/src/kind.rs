#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DiagramKind {
    Flowchart,
    Swimlane,
    Agentflow,
    Class,
    State,
    Er,
    Requirement,
    Usecase,
    C4,
    Sequence,
    Block,
    Architecture,
    Kanban,
    Packet,
    Mindmap,
    Treeview,
    Ishikawa,
    Gitgraph,
    Eventmodeling,
    Timeline,
    Journey,
    Gantt,
    Xychart,
    Quadrant,
    Treemap,
    Wardley,
    Pie,
    Radar,
    Sankey,
    Venn,
    Cynefin,
    Railroad,
    Info,
}

impl DiagramKind {
    pub fn from_id(id: &str) -> Option<Self> {
        const ALL: [DiagramKind; 33] = [
            DiagramKind::Flowchart,
            DiagramKind::Swimlane,
            DiagramKind::Agentflow,
            DiagramKind::Class,
            DiagramKind::State,
            DiagramKind::Er,
            DiagramKind::Requirement,
            DiagramKind::Usecase,
            DiagramKind::C4,
            DiagramKind::Sequence,
            DiagramKind::Block,
            DiagramKind::Architecture,
            DiagramKind::Kanban,
            DiagramKind::Packet,
            DiagramKind::Mindmap,
            DiagramKind::Treeview,
            DiagramKind::Ishikawa,
            DiagramKind::Gitgraph,
            DiagramKind::Eventmodeling,
            DiagramKind::Timeline,
            DiagramKind::Journey,
            DiagramKind::Gantt,
            DiagramKind::Xychart,
            DiagramKind::Quadrant,
            DiagramKind::Treemap,
            DiagramKind::Wardley,
            DiagramKind::Pie,
            DiagramKind::Radar,
            DiagramKind::Sankey,
            DiagramKind::Venn,
            DiagramKind::Cynefin,
            DiagramKind::Railroad,
            DiagramKind::Info,
        ];
        ALL.into_iter().find(|kind| kind.id() == id)
    }

    pub const fn id(self) -> &'static str {
        match self {
            DiagramKind::Flowchart => "flowchart",
            DiagramKind::Swimlane => "swimlane",
            DiagramKind::Agentflow => "agentflow",
            DiagramKind::Class => "class",
            DiagramKind::State => "state",
            DiagramKind::Er => "er",
            DiagramKind::Requirement => "requirement",
            DiagramKind::Usecase => "usecase",
            DiagramKind::C4 => "c4",
            DiagramKind::Sequence => "sequence",
            DiagramKind::Block => "block",
            DiagramKind::Architecture => "architecture",
            DiagramKind::Kanban => "kanban",
            DiagramKind::Packet => "packet",
            DiagramKind::Mindmap => "mindmap",
            DiagramKind::Treeview => "treeview",
            DiagramKind::Ishikawa => "ishikawa",
            DiagramKind::Gitgraph => "gitgraph",
            DiagramKind::Eventmodeling => "eventmodeling",
            DiagramKind::Timeline => "timeline",
            DiagramKind::Journey => "journey",
            DiagramKind::Gantt => "gantt",
            DiagramKind::Xychart => "xychart",
            DiagramKind::Quadrant => "quadrant",
            DiagramKind::Treemap => "treemap",
            DiagramKind::Wardley => "wardley",
            DiagramKind::Pie => "pie",
            DiagramKind::Radar => "radar",
            DiagramKind::Sankey => "sankey",
            DiagramKind::Venn => "venn",
            DiagramKind::Cynefin => "cynefin",
            DiagramKind::Railroad => "railroad",
            DiagramKind::Info => "info",
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::DiagramKind;
    use crate::r#gen::kinds::KINDS;
    #[test]
    fn kind_id_round_trip() {
        for (kind, id) in IN_ORDER {
            assert_eq!(DiagramKind::from_id(id), Some(kind));
        }
        assert_eq!(DiagramKind::from_id("Flowchart"), None);
        assert_eq!(DiagramKind::from_id(""), None);
    }

    const IN_ORDER: [(DiagramKind, &str); 33] = [
        (DiagramKind::Flowchart, "flowchart"),
        (DiagramKind::Swimlane, "swimlane"),
        (DiagramKind::Agentflow, "agentflow"),
        (DiagramKind::Class, "class"),
        (DiagramKind::State, "state"),
        (DiagramKind::Er, "er"),
        (DiagramKind::Requirement, "requirement"),
        (DiagramKind::Usecase, "usecase"),
        (DiagramKind::C4, "c4"),
        (DiagramKind::Sequence, "sequence"),
        (DiagramKind::Block, "block"),
        (DiagramKind::Architecture, "architecture"),
        (DiagramKind::Kanban, "kanban"),
        (DiagramKind::Packet, "packet"),
        (DiagramKind::Mindmap, "mindmap"),
        (DiagramKind::Treeview, "treeview"),
        (DiagramKind::Ishikawa, "ishikawa"),
        (DiagramKind::Gitgraph, "gitgraph"),
        (DiagramKind::Eventmodeling, "eventmodeling"),
        (DiagramKind::Timeline, "timeline"),
        (DiagramKind::Journey, "journey"),
        (DiagramKind::Gantt, "gantt"),
        (DiagramKind::Xychart, "xychart"),
        (DiagramKind::Quadrant, "quadrant"),
        (DiagramKind::Treemap, "treemap"),
        (DiagramKind::Wardley, "wardley"),
        (DiagramKind::Pie, "pie"),
        (DiagramKind::Radar, "radar"),
        (DiagramKind::Sankey, "sankey"),
        (DiagramKind::Venn, "venn"),
        (DiagramKind::Cynefin, "cynefin"),
        (DiagramKind::Railroad, "railroad"),
        (DiagramKind::Info, "info"),
    ];

    #[test]
    fn id_matches_declaration_order() {
        for (kind, want) in IN_ORDER {
            assert_eq!(kind.id(), want, "{}", kind.id());
        }
    }

    #[test]
    fn variant_set_equals_the_generated_table() {
        let from_enum: BTreeSet<&str> = IN_ORDER.iter().map(|(_, id)| *id).collect();
        let from_table: BTreeSet<&str> = KINDS.iter().map(|row| row.id).collect();
        assert_eq!(from_enum, from_table);
        assert_eq!(from_enum.len(), 33);
    }
    #[test]
    fn generated_table_is_sorted_and_covers_every_variant() {
        let table_ids: Vec<&str> = KINDS.iter().map(|row| row.id).collect();
        let mut sorted = table_ids.clone();
        sorted.sort_unstable();
        assert_eq!(table_ids, sorted);
        for (kind, _) in IN_ORDER {
            assert!(table_ids.contains(&kind.id()));
        }
    }

    #[test]
    fn ids_are_unique_and_lowercase() {
        let ids: BTreeSet<&str> = IN_ORDER.iter().map(|(_, id)| *id).collect();
        assert_eq!(ids.len(), IN_ORDER.len());
        for (kind, _) in IN_ORDER {
            let id = kind.id();
            assert!(!id.is_empty());
            assert!(
                id.bytes()
                    .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit())
            );
        }
    }
}
