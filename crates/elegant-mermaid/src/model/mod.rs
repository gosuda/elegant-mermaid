pub mod agentflow;
pub mod architecture;
pub mod block;
pub mod c4;
pub mod chart;
pub mod class;
pub mod cynefin;
pub mod er;
pub mod eventmodeling;
mod edges;
pub mod flowchart;
pub mod gantt;
pub mod gitgraph;
pub mod info;
pub mod ishikawa;
pub mod journey;
pub mod kanban;
pub mod mindmap;
pub mod packet;
pub mod pie;
pub mod quadrant;
pub mod radar;
pub mod railroad;
pub mod requirement;
pub mod sankey;
pub mod sequence;
pub mod state;
pub mod swimlane;
pub mod timeline;
pub mod treemap;
pub mod treeview;
pub mod usecase;
pub mod venn;
pub mod wardley;
pub mod xychart;

#[derive(Debug)]
pub enum Resolved {
    Flowchart(flowchart::Model),
    Class(class::Model),
    State(state::Model),
    C4(c4::Model),
    Requirement(requirement::Model),
    Er(er::Model),
    Agentflow(agentflow::Model),
    Swimlane(swimlane::Model),
    Usecase(usecase::Model),
    Sequence(sequence::Model),
    Mindmap(mindmap::Model),
    Eventmodeling(eventmodeling::Model),
    Gitgraph(gitgraph::Model),
    Block(block::Model),
    Xychart(xychart::Model),
    Timeline(timeline::Model),
    Railroad(railroad::Model),
    Radar(radar::Model),
    Cynefin(cynefin::Model),
    Info(info::Model),
    Packet(packet::Model),
    Kanban(kanban::Model),
    Wardley(wardley::Model),
    Pie(pie::Model),
    Quadrant(quadrant::Model),
    Journey(journey::Model),
    Ishikawa(ishikawa::Model),
    Gantt(gantt::Model),
    Venn(venn::Model),
    Architecture(architecture::Model),
    Treeview(treeview::Model),
    Treemap(treemap::Model),
    Sankey(sankey::Model),
}

impl Resolved {
    pub fn parse(
        kind: crate::DiagramKind,
        source: &str,
        removed: &[crate::Span],
    ) -> (Option<Self>, Vec<crate::Diagnostic>) {
        match kind {
            crate::DiagramKind::Flowchart => {
                let parsed = crate::syntax::flowchart::parse(source, removed);
                let (model, mut diagnostics) = flowchart::resolve(source, &parsed.document);
                diagnostics.extend(parsed.diagnostics);
                (Some(Self::Flowchart(model)), diagnostics)
            }
            crate::DiagramKind::Class => {
                let parsed = crate::syntax::class::parse(source, removed);
                let (model, mut diagnostics) = class::resolve(source, &parsed.document);
                diagnostics.extend(parsed.diagnostics);
                (Some(Self::Class(model)), diagnostics)
            }
            crate::DiagramKind::State => {
                let parsed = crate::syntax::state::parse(source, removed);
                let (model, mut diagnostics) = state::resolve(source, &parsed.document);
                diagnostics.extend(parsed.diagnostics);
                (Some(Self::State(model)), diagnostics)
            }
            crate::DiagramKind::C4 => {
                let parsed = crate::syntax::c4::parse(source, removed);
                let (model, mut diagnostics) = c4::resolve(source, &parsed.document);
                diagnostics.extend(parsed.diagnostics);
                (Some(Self::C4(model)), diagnostics)
            }
            crate::DiagramKind::Requirement => {
                let parsed = crate::syntax::requirement::parse(source, removed);
                let (model, mut diagnostics) = requirement::resolve(source, &parsed.document);
                diagnostics.extend(parsed.diagnostics);
                (Some(Self::Requirement(model)), diagnostics)
            }
            crate::DiagramKind::Er => {
                let parsed = crate::syntax::er::parse(source, removed);
                let (model, mut diagnostics) = er::resolve(source, &parsed.document);
                diagnostics.extend(parsed.diagnostics);
                (Some(Self::Er(model)), diagnostics)
            }
            crate::DiagramKind::Agentflow => {
                let parsed = crate::syntax::agentflow::parse(source, removed);
                let (model, mut diagnostics) = agentflow::resolve(source, &parsed.document);
                diagnostics.extend(parsed.diagnostics);
                (Some(Self::Agentflow(model)), diagnostics)
            }
            crate::DiagramKind::Usecase => {
                let parsed = crate::syntax::usecase::parse(source, removed);
                let (model, mut diagnostics) = usecase::resolve(source, &parsed.document);
                diagnostics.extend(parsed.diagnostics);
                (Some(Self::Usecase(model)), diagnostics)
            }
            crate::DiagramKind::Swimlane => {
                let parsed = crate::syntax::swimlane::parse(source, removed);
                let (model, mut diagnostics) = swimlane::resolve(source, &parsed.document);
                diagnostics.extend(parsed.diagnostics);
                (Some(Self::Swimlane(model)), diagnostics)
            }
            crate::DiagramKind::Sequence => {
                let parsed = crate::syntax::sequence::parse(source, removed);
                let (model, mut diagnostics) = sequence::resolve(source, &parsed.document);
                diagnostics.extend(parsed.diagnostics);
                (Some(Self::Sequence(model)), diagnostics)
            }
            crate::DiagramKind::Mindmap => {
                let parsed = crate::syntax::mindmap::parse(source, removed);
                let (model, mut diagnostics) = mindmap::resolve(source, &parsed.document);
                diagnostics.extend(parsed.diagnostics);
                (Some(Self::Mindmap(model)), diagnostics)
            }
            crate::DiagramKind::Eventmodeling => {
                let parsed = crate::syntax::eventmodeling::parse(source, removed);
                let (model, mut diagnostics) = eventmodeling::resolve(&parsed.document);
                diagnostics.extend(parsed.diagnostics);
                (Some(Self::Eventmodeling(model)), diagnostics)
            }
            crate::DiagramKind::Gitgraph => {
                let parsed = crate::syntax::gitgraph::parse(source, removed);
                let (model, mut diagnostics) = gitgraph::resolve(source, &parsed.document);
                diagnostics.extend(parsed.diagnostics);
                (Some(Self::Gitgraph(model)), diagnostics)
            }
            crate::DiagramKind::Block => {
                let parsed = crate::syntax::block::parse(source, removed);
                let (model, mut diagnostics) = block::resolve(source, &parsed.document);
                diagnostics.extend(parsed.diagnostics);
                (Some(Self::Block(model)), diagnostics)
            }
            crate::DiagramKind::Xychart => {
                let parsed = crate::syntax::xychart::parse(source, removed);
                let (model, mut diagnostics) = xychart::resolve(source, &parsed.document);
                diagnostics.extend(parsed.diagnostics);
                (Some(Self::Xychart(model)), diagnostics)
            }
            crate::DiagramKind::Timeline => {
                let parsed = crate::syntax::timeline::parse(source, removed);
                let (model, mut diagnostics) = timeline::resolve(source, &parsed.document);
                diagnostics.extend(parsed.diagnostics);
                (Some(Self::Timeline(model)), diagnostics)
            }
            crate::DiagramKind::Railroad => {
                let parsed = crate::syntax::railroad::parse(source, removed);
                let (model, mut diagnostics) = railroad::resolve(&parsed.document);
                diagnostics.extend(parsed.diagnostics);
                (Some(Self::Railroad(model)), diagnostics)
            }
            crate::DiagramKind::Radar => {
                let parsed = crate::syntax::radar::parse(source, removed);
                let (model, mut diagnostics) = radar::resolve(source, &parsed.document);
                diagnostics.extend(parsed.diagnostics);
                (Some(Self::Radar(model)), diagnostics)
            }
            crate::DiagramKind::Cynefin => {
                let parsed = crate::syntax::cynefin::parse(source, removed);
                let (model, mut diagnostics) = cynefin::resolve(source, &parsed.document);
                diagnostics.extend(parsed.diagnostics);
                (Some(Self::Cynefin(model)), diagnostics)
            }
            crate::DiagramKind::Info => {
                let parsed = crate::syntax::info::parse(source, removed);
                let (model, mut diagnostics) = info::resolve(&parsed.document);
                diagnostics.extend(parsed.diagnostics);
                (Some(Self::Info(model)), diagnostics)
            }
            crate::DiagramKind::Packet => {
                let parsed = crate::syntax::packet::parse(source, removed);
                let (model, mut diagnostics) = packet::resolve(source, &parsed.document);
                diagnostics.extend(parsed.diagnostics);
                (Some(Self::Packet(model)), diagnostics)
            }
            crate::DiagramKind::Kanban => {
                let parsed = crate::syntax::kanban::parse(source, removed);
                let (model, mut diagnostics) = kanban::resolve(source, &parsed.document);
                diagnostics.extend(parsed.diagnostics);
                (Some(Self::Kanban(model)), diagnostics)
            }
            crate::DiagramKind::Wardley => {
                let parsed = crate::syntax::wardley::parse(source, removed);
                let (model, mut diagnostics) = wardley::resolve(source, &parsed.document);
                diagnostics.extend(parsed.diagnostics);
                (Some(Self::Wardley(model)), diagnostics)
            }
            crate::DiagramKind::Pie => {
                let parsed = crate::syntax::pie::parse(source, removed);
                let (model, mut diagnostics) = pie::resolve(source, &parsed.document);
                diagnostics.extend(parsed.diagnostics);
                (Some(Self::Pie(model)), diagnostics)
            }
            crate::DiagramKind::Quadrant => {
                let parsed = crate::syntax::quadrant::parse(source, removed);
                let (model, mut diagnostics) = quadrant::resolve(source, &parsed.document);
                diagnostics.extend(parsed.diagnostics);
                (Some(Self::Quadrant(model)), diagnostics)
            }
            crate::DiagramKind::Journey => {
                let parsed = crate::syntax::journey::parse(source, removed);
                let (model, mut diagnostics) = journey::resolve(source, &parsed.document);
                diagnostics.extend(parsed.diagnostics);
                (Some(Self::Journey(model)), diagnostics)
            }
            crate::DiagramKind::Ishikawa => {
                let parsed = crate::syntax::ishikawa::parse(source, removed);
                let (model, mut diagnostics) = ishikawa::resolve(&parsed.document);
                diagnostics.extend(parsed.diagnostics);
                (Some(Self::Ishikawa(model)), diagnostics)
            }
            crate::DiagramKind::Gantt => {
                let parsed = crate::syntax::gantt::parse(source, removed);
                let (model, mut diagnostics) = gantt::resolve(source, &parsed.document);
                diagnostics.extend(parsed.diagnostics);
                (Some(Self::Gantt(model)), diagnostics)
            }
            crate::DiagramKind::Venn => {
                let (model, diagnostics) = venn::parse_and_resolve(source, removed);
                (Some(Self::Venn(model)), diagnostics)
            }
            crate::DiagramKind::Architecture => {
                let parsed = crate::syntax::architecture::parse(source, removed);
                let (model, mut diagnostics) = architecture::resolve(source, &parsed.document);
                diagnostics.extend(parsed.diagnostics);
                (Some(Self::Architecture(model)), diagnostics)
            }
            crate::DiagramKind::Treeview => {
                let parsed = crate::syntax::treeview::parse(source, removed);
                let (model, mut diagnostics) = treeview::resolve(source, &parsed.document);
                diagnostics.extend(parsed.diagnostics);
                (Some(Self::Treeview(model)), diagnostics)
            }
            crate::DiagramKind::Treemap => {
                let (document, mut diagnostics) = crate::syntax::treemap::parse(source, removed);
                let (model, resolved_diagnostics) = treemap::resolve(source, &document);
                diagnostics.extend(resolved_diagnostics);
                (Some(Self::Treemap(model)), diagnostics)
            }
            crate::DiagramKind::Sankey => {
                let (document, mut diagnostics) = crate::syntax::sankey::parse(source, removed);
                let (model, resolved_diagnostics) = sankey::resolve(source, &document);
                diagnostics.extend(resolved_diagnostics);
                (Some(Self::Sankey(model)), diagnostics)
            }
        }
    }

    pub fn input(
        &self,
        profile: crate::scene::Profile,
        options: crate::scene::DumpOptions,
    ) -> Result<crate::layout::input::Input, crate::geom::GeomError> {
        match self {
            Self::Flowchart(model) => Ok(crate::layout::flowchart::from_flowchart(
                model, profile, options,
            )),
            Self::Class(model) => crate::layout::class::from_class(model, profile, options),
            Self::State(model) => crate::layout::state::from_state(model, profile, options),
            Self::C4(model) => crate::layout::c4::from_c4(model, profile, options),
            Self::Requirement(model) => {
                crate::layout::requirement::from_requirement(model, profile, options)
            }
            Self::Er(model) => crate::layout::er::from_er(model, profile, options),
            Self::Agentflow(model) => {
                crate::layout::agentflow::from_agentflow(model, profile, options)
            }
            Self::Swimlane(model) => Ok(crate::layout::swimlane::from_swimlane(
                model, profile, options,
            )),
            Self::Usecase(model) => crate::layout::usecase::from_usecase(model, profile, options),
            Self::Sequence(model) => {
                crate::layout::sequence::from_sequence(model, profile, options)
            }
            Self::Mindmap(model) => crate::layout::mindmap::from_mindmap(model, profile, options),
            Self::Eventmodeling(model) => Ok(crate::layout::eventmodeling::from_eventmodeling(
                model, profile, options,
            )),
            Self::Gitgraph(model) => {
                crate::layout::gitgraph::from_gitgraph(model, profile, options)
            }
            Self::Block(model) => crate::layout::block::from_block(model, profile, options),
            Self::Xychart(model) => crate::layout::xychart::from_xychart(model, profile, options),
            Self::Timeline(model) => {
                crate::layout::timeline::from_timeline(model, profile, options)
            }
            Self::Railroad(model) => {
                crate::layout::railroad::from_railroad(model, profile, options)
            }
            Self::Radar(model) => crate::layout::radar::from_radar(model, profile, options),
            Self::Cynefin(model) => crate::layout::cynefin::from_cynefin(model, profile, options),
            Self::Info(model) => crate::layout::info::from_info(model, profile, options),
            Self::Packet(model) => crate::layout::packet::from_packet(model, profile, options),
            Self::Kanban(model) => crate::layout::kanban::from_kanban(model, profile, options),
            Self::Wardley(model) => crate::layout::wardley::from_wardley(model, profile, options),
            Self::Pie(model) => crate::layout::pie::from_pie(model, profile, options),
            Self::Quadrant(model) => {
                crate::layout::quadrant::from_quadrant(model, profile, options)
            }
            Self::Journey(model) => crate::layout::journey::from_journey(model, profile, options),
            Self::Ishikawa(model) => {
                crate::layout::ishikawa::from_ishikawa(model, profile, options)
            }
            Self::Gantt(model) => crate::layout::gantt::from_gantt(model, profile, options),
            Self::Venn(model) => crate::layout::venn::from_venn(model, profile, options),
            Self::Architecture(model) => {
                crate::layout::architecture::from_architecture(model, profile, options)
            }
            Self::Treeview(model) => {
                crate::layout::treeview::from_treeview(model, profile, options)
            }
            Self::Treemap(model) => crate::layout::treemap::from_treemap(model, profile, options),
            Self::Sankey(model) => crate::layout::sankey::from_sankey(model, profile, options),
        }
    }

    pub fn accessibility(&self) -> (&str, &str, &'static str) {
        match self {
            Self::Flowchart(model) => (&model.acc_title, &model.acc_descr, "flowchart"),
            Self::Class(model) => (&model.acc_title, &model.acc_descr, "class"),
            Self::State(model) => (
                model
                    .acc_title
                    .as_ref()
                    .map_or("", |text| text.value.as_str()),
                model
                    .acc_descr
                    .as_ref()
                    .map_or("", |text| text.value.as_str()),
                "state",
            ),
            Self::C4(model) => (&model.acc_title, &model.acc_descr, "c4"),
            Self::Requirement(model) => (&model.acc_title, &model.acc_descr, "requirement"),
            Self::Er(model) => (&model.acc_title, &model.acc_descr, "er"),
            Self::Agentflow(model) => (&model.acc_title, &model.acc_descr, "agentflow"),
            Self::Swimlane(model) => (
                &model.flowchart.acc_title,
                &model.flowchart.acc_descr,
                "swimlane",
            ),
            Self::Usecase(model) => (&model.acc_title, &model.acc_descr, "usecase"),
            Self::Sequence(model) => (&model.acc_title, &model.acc_descr, "sequence"),
            Self::Mindmap(_) => ("", "", "mindmap"),
            Self::Eventmodeling(_) => ("", "", "eventmodeling"),
            Self::Gitgraph(model) => (&model.acc_title, &model.acc_descr, "gitgraph"),
            Self::Block(_) => ("", "", "block"),
            Self::Xychart(model) => (&model.acc_title, &model.acc_descr, "xychart"),
            Self::Timeline(model) => (&model.acc_title, &model.acc_descr, "timeline"),
            Self::Railroad(model) => (&model.acc_title, &model.acc_descr, "railroad"),
            Self::Radar(model) => (&model.acc_title, &model.acc_descr, "radar"),
            Self::Cynefin(model) => (&model.acc_title, &model.acc_descr, "cynefin"),
            Self::Info(_) => ("", "", "info"),
            Self::Packet(model) => (&model.acc_title, &model.acc_descr, "packet"),
            Self::Kanban(_) => ("", "", "kanban"),
            Self::Wardley(model) => (&model.acc_title, &model.acc_descr, "wardley"),
            Self::Pie(model) => (&model.acc_title, &model.acc_descr, "pie"),
            Self::Quadrant(model) => (&model.acc_title, &model.acc_descr, "quadrant"),
            Self::Journey(model) => (&model.acc_title, &model.acc_descr, "journey"),
            Self::Ishikawa(_) => ("", "", "ishikawa"),
            Self::Gantt(model) => (&model.acc_title, &model.acc_descr, "gantt"),
            Self::Venn(_) => ("", "", "venn"),
            Self::Architecture(model) => (&model.acc_title, &model.acc_descr, "architecture"),
            Self::Treeview(model) => (&model.acc_title, &model.acc_descr, "treeview"),
            Self::Treemap(model) => (&model.acc_title, &model.acc_descr, "treemap"),
            Self::Sankey(_) => ("", "", "sankey"),
        }
    }

    pub fn links(&self) -> Vec<crate::interaction::OwnerLink<'_>> {
        match self {
            Self::State(model) => model
                .links
                .iter()
                .filter_map(|link| {
                    let url = crate::interaction::SafeUrl::new(&link.url.value)?;
                    Some(crate::interaction::OwnerLink {
                        owner: &link.target,
                        role: crate::scene::GroupRole::Node,
                        url,
                        tooltip: link
                            .tooltip
                            .as_ref()
                            .map(|text| text.value.as_str())
                            .filter(|tip| !tip.is_empty()),
                    })
                })
                .collect(),
            Self::Agentflow(model) => model
                .links
                .iter()
                .filter_map(|link| {
                    let url = crate::interaction::SafeUrl::new(link.url.as_deref()?)?;
                    Some(crate::interaction::OwnerLink {
                        owner: &link.id,
                        role: crate::scene::GroupRole::Node,
                        url,
                        tooltip: link.tooltip.as_deref().filter(|tip| !tip.is_empty()),
                    })
                })
                .collect(),
            Self::Flowchart(model) => model
                .links
                .iter()
                .filter_map(|link| {
                    let url = crate::interaction::SafeUrl::new(&link.url)?;
                    Some(crate::interaction::OwnerLink {
                        owner: &link.target,
                        role: crate::scene::GroupRole::Node,
                        url,
                        tooltip: link.tooltip.as_deref().filter(|tip| !tip.is_empty()),
                    })
                })
                .collect(),
            Self::Sequence(model) => model
                .actors
                .iter()
                .flat_map(|actor| {
                    actor.links.iter().filter_map(|(label, url)| {
                        crate::interaction::SafeUrl::new(url).map(|safe| {
                            crate::interaction::OwnerLink {
                                owner: actor.id.as_str(),
                                role: crate::scene::GroupRole::Node,
                                url: safe,
                                tooltip: (!label.is_empty()).then_some(label.as_str()),
                            }
                        })
                    })
                })
                .collect(),
            Self::Gantt(model) => model
                .tasks
                .iter()
                .filter_map(|task| {
                    let url = crate::interaction::SafeUrl::new(task.link.as_deref()?)?;
                    Some(crate::interaction::OwnerLink {
                        owner: &task.owner,
                        role: crate::scene::GroupRole::Node,
                        url,
                        tooltip: None,
                    })
                })
                .collect(),
            Self::Class(_)
            | Self::Swimlane(_)
            | Self::C4(_)
            | Self::Requirement(_)
            | Self::Er(_)
            | Self::Usecase(_)
            | Self::Mindmap(_)
            | Self::Eventmodeling(_)
            | Self::Gitgraph(_)
            | Self::Block(_)
            | Self::Xychart(_)
            | Self::Timeline(_)
            | Self::Railroad(_)
            | Self::Radar(_)
            | Self::Cynefin(_)
            | Self::Info(_)
            | Self::Packet(_)
            | Self::Wardley(_)
            | Self::Pie(_)
            | Self::Quadrant(_)
            | Self::Journey(_)
            | Self::Ishikawa(_)
            | Self::Venn(_)
            | Self::Architecture(_)
            | Self::Treeview(_)
            | Self::Treemap(_)
            | Self::Sankey(_)
            | Self::Kanban(_) => Vec::new(),
        }
    }

    pub fn icon_refs(&self) -> Vec<crate::icons::IconRef<'_>> {
        match self {
            Self::Architecture(model) => crate::layout::architecture::icon_refs(model),
            Self::Flowchart(model) => model
                .nodes
                .iter()
                .filter_map(|node| {
                    let name = node.attrs.get("icon").filter(|name| !name.is_empty())?;
                    Some(crate::icons::IconRef {
                        owner: &node.id,
                        name,
                        span: node.span,
                        placement: crate::icons::Placement::Edge,
                    })
                })
                .collect(),
            _ => Vec::new(),
        }
    }
}
