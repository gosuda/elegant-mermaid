use crate::diag::{Diagnostic, Severity};
use crate::document::Document;
use crate::r#gen::lintrules::{LINT_RULES, LintRule};
use crate::options::{FixOutcome, LintConfig};
use std::collections::{BTreeMap, BTreeSet};

use super::common::{self, Block};
use super::flowchart;
use super::suppression::{self, FileScope};

/// Runs steps 2 to 4 of the engine pipeline over the document: the enabled
/// registry rules in order, their effective severities, and the suppression
/// pass.
pub fn lint(document: &Document<'_>, config: &LintConfig) -> Vec<Diagnostic> {
    pass(document, config).lint
}

/// Runs the full pass over one document and returns the syntax diagnostics
/// and the lint-rule and `meta/*` diagnostics after suppression, in output
/// order.
pub fn lint_document(document: &Document<'_>, config: &LintConfig) -> Vec<Diagnostic> {
    let Pass { syntax, lint } = pass(document, config);
    let mut combined = syntax;
    combined.extend(lint);
    crate::diag::sort(&mut combined);
    combined
}

pub(crate) struct Pass {
    pub syntax: Vec<Diagnostic>,
    pub lint: Vec<Diagnostic>,
}

pub(crate) fn pass(document: &Document<'_>, config: &LintConfig) -> Pass {
    scoped_pass(document, config, None)
}

/// One block of a Markdown host: host-wide directives apply to it and record
/// that they were used, and the host reports them once after every block.
pub(crate) fn host_pass(
    document: &Document<'_>,
    config: &LintConfig,
    file: &mut FileScope,
) -> Pass {
    scoped_pass(document, config, Some(file))
}

fn scoped_pass(document: &Document<'_>, config: &LintConfig, file: Option<&mut FileScope>) -> Pass {
    let source = document.source();
    let prep = crate::syntax::preprocess::preprocess(source);
    let detection = crate::syntax::detect::detect(source, &prep.removed);
    let block = Block {
        source,
        host_offset: 0,
        header: detection.header,
        kind: detection.kind.map(crate::kind::DiagramKind::id),
        frontmatter: prep.frontmatter.as_ref().map(|front| front.body),
    };
    let rules = rule_diagnostics(&block, document.resolved(), config);
    let body_start = block.frontmatter.map_or(0, |front| front.end);
    let outcome = suppression::run(
        source,
        body_start,
        document.diagnostics().to_vec(),
        rules,
        file,
    );
    let mut lint = outcome.lint;
    lint.extend(configured_meta(outcome.meta, config));
    crate::diag::sort(&mut lint);
    Pass {
        syntax: outcome.syntax,
        lint,
    }
}

/// Keeps the `meta/*` diagnostics whose rule the configuration enables, at
/// the configured severity.
pub(crate) fn configured_meta(meta: Vec<Diagnostic>, config: &LintConfig) -> Vec<Diagnostic> {
    meta.into_iter()
        .filter_map(|mut diagnostic| {
            let row = LINT_RULES.iter().find(|row| row.code == diagnostic.code)?;
            diagnostic.severity = effective(row, config)?;
            Some(diagnostic)
        })
        .collect()
}

fn rule_diagnostics(
    block: &Block<'_>,
    model: Option<&crate::model::Resolved>,
    config: &LintConfig,
) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    let flowchart_diagnostics = |row: &LintRule| match row.code {
        "flowchart/duplicate-ids"
        | "flowchart/subgraph-id-collision"
        | "flowchart/label-at-in-unquoted"
            if block.kind == Some("flowchart") =>
        {
            flowchart_model(model, row)
        }
        _ => Vec::new(),
    };
    let xychart_diagnostics = |row: &LintRule| match row.code {
        "xychart/missing-x-axis" if block.kind == Some("xychart") => {
            if let Some(crate::model::Resolved::Xychart(m)) = model {
                super::xychart::missing_x_axis(m, row)
            } else {
                Vec::new()
            }
        }
        "xychart/missing-y-axis" if block.kind == Some("xychart") => {
            if let Some(crate::model::Resolved::Xychart(m)) = model {
                super::xychart::missing_y_axis(m, row)
            } else {
                Vec::new()
            }
        }
        "xychart/no-series" if block.kind == Some("xychart") => {
            if let Some(crate::model::Resolved::Xychart(m)) = model {
                super::xychart::no_series(m, row)
            } else {
                Vec::new()
            }
        }
        "xychart/series-length-mismatch" if block.kind == Some("xychart") => {
            if let Some(crate::model::Resolved::Xychart(m)) = model {
                super::xychart::series_length_mismatch(m, row)
            } else {
                Vec::new()
            }
        }
        _ => Vec::new(),
    };
    let timeline_diagnostics = |row: &LintRule| match row.code {
        "timeline/no-entries" if block.kind == Some("timeline") => {
            if let Some(crate::model::Resolved::Timeline(m)) = model {
                super::timeline::no_entries(m, block.header, row)
            } else {
                Vec::new()
            }
        }
        "timeline/empty-section" if block.kind == Some("timeline") => {
            if let Some(crate::model::Resolved::Timeline(m)) = model {
                super::timeline::empty_section(m, row)
            } else {
                Vec::new()
            }
        }
        "timeline/empty-event" if block.kind == Some("timeline") => {
            if let Some(crate::model::Resolved::Timeline(m)) = model {
                super::timeline::empty_event(m, row)
            } else {
                Vec::new()
            }
        }
        _ => Vec::new(),
    };
    let packet_diagnostics = |row: &LintRule| match row.code {
        "packet/no-fields" if block.kind == Some("packet") => {
            if let Some(crate::model::Resolved::Packet(m)) = model {
                super::packet::no_fields(m, block.header, row)
            } else {
                Vec::new()
            }
        }
        "packet/empty-labels" if block.kind == Some("packet") => {
            if let Some(crate::model::Resolved::Packet(m)) = model {
                super::packet::empty_labels(m, row)
            } else {
                Vec::new()
            }
        }
        _ => Vec::new(),
    };
    let radar_diagnostics = |row: &LintRule| match row.code {
        "radar/no-curves" if block.kind == Some("radar") => {
            if let Some(crate::model::Resolved::Radar(m)) = model {
                super::radar::no_curves(m, row)
            } else {
                Vec::new()
            }
        }
        "radar/duplicate-axis" if block.kind == Some("radar") => {
            if let Some(crate::model::Resolved::Radar(m)) = model {
                super::radar::duplicate_axis(m, row)
            } else {
                Vec::new()
            }
        }
        "radar/curve-length-mismatch" if block.kind == Some("radar") => {
            if let Some(crate::model::Resolved::Radar(m)) = model {
                super::radar::curve_length_mismatch(m, row)
            } else {
                Vec::new()
            }
        }
        _ => Vec::new(),
    };
    let sequence_diagnostics = |row: &LintRule| match row.code {
        "sequence/no-activate-without-deactivate" if block.kind == Some("sequence") => {
            if let Some(crate::model::Resolved::Sequence(m)) = model {
                super::sequence::no_activate_without_deactivate(m, row)
            } else {
                Vec::new()
            }
        }
        "sequence/prefer-explicit-participants" if block.kind == Some("sequence") => {
            if let Some(crate::model::Resolved::Sequence(m)) = model {
                super::sequence::prefer_explicit_participants(m, row)
            } else {
                Vec::new()
            }
        }
        "sequence/duplicate-participant" if block.kind == Some("sequence") => {
            if let Some(crate::model::Resolved::Sequence(m)) = model {
                super::sequence::duplicate_participant(m, row)
            } else {
                Vec::new()
            }
        }
        _ => Vec::new(),
    };
    let gitgraph_diagnostics = |row: &LintRule| match row.code {
        "gitgraph/duplicate-tag" if block.kind == Some("gitgraph") => {
            if let Some(crate::model::Resolved::Gitgraph(m)) = model {
                super::gitgraph::duplicate_tag(m, row)
            } else {
                Vec::new()
            }
        }
        "gitgraph/no-commits" if block.kind == Some("gitgraph") => {
            if let Some(crate::model::Resolved::Gitgraph(m)) = model {
                super::gitgraph::no_commits(m, row)
            } else {
                Vec::new()
            }
        }
        _ => Vec::new(),
    };
    let mindmap_diagnostics = |row: &LintRule| match row.code {
        "mindmap/duplicate-sibling" if block.kind == Some("mindmap") => {
            if let Some(crate::model::Resolved::Mindmap(m)) = model {
                super::mindmap::duplicate_sibling(m, row)
            } else {
                Vec::new()
            }
        }
        "mindmap/no-nodes" if block.kind == Some("mindmap") => {
            if let Some(crate::model::Resolved::Mindmap(m)) = model {
                super::mindmap::no_nodes(m, row)
            } else {
                Vec::new()
            }
        }
        "mindmap/deep-nesting" if block.kind == Some("mindmap") => {
            if let Some(crate::model::Resolved::Mindmap(m)) = model {
                super::mindmap::deep_nesting(m, row)
            } else {
                Vec::new()
            }
        }
        _ => Vec::new(),
    };
    let block_diagnostics = |row: &LintRule| match row.code {
        "block/no-blocks" if block.kind == Some("block") => {
            if let Some(crate::model::Resolved::Block(m)) = model {
                super::block::no_blocks(m, row)
            } else {
                Vec::new()
            }
        }
        _ => Vec::new(),
    };
    let eventmodeling_diagnostics = |row: &LintRule| match row.code {
        "eventmodeling/undefined-frame" if block.kind == Some("eventmodeling") => {
            if let Some(crate::model::Resolved::Eventmodeling(m)) = model {
                super::eventmodeling::undefined_frame(m, row)
            } else {
                Vec::new()
            }
        }
        "eventmodeling/invalid-flow" if block.kind == Some("eventmodeling") => {
            if let Some(crate::model::Resolved::Eventmodeling(m)) = model {
                super::eventmodeling::invalid_flow(m, row)
            } else {
                Vec::new()
            }
        }
        _ => Vec::new(),
    };
    let class_diagnostics = |row: &LintRule| match row.code {
        "class/duplicate-class" | "class/no-duplicate-methods" if block.kind == Some("class") => {
            if let Some(crate::model::Resolved::Class(m)) = model {
                super::class::run(m, row)
            } else {
                Vec::new()
            }
        }
        _ => Vec::new(),
    };
    let state_diagnostics = |row: &LintRule| match row.code {
        "state/duplicate-state"
        | "state/duplicate-transition"
        | "state/empty-composite"
        | "state/self-transition"
            if block.kind == Some("state") =>
        {
            if let Some(crate::model::Resolved::State(m)) = model {
                super::state::run(m, row)
            } else {
                Vec::new()
            }
        }
        _ => Vec::new(),
    };
    let er_diagnostics = |row: &LintRule| match row.code {
        "er/duplicate-attribute" | "er/duplicate-entity" | "er/standalone-entity"
            if block.kind == Some("er") =>
        {
            if let Some(crate::model::Resolved::Er(m)) = model {
                match row.code {
                    "er/duplicate-attribute" => super::er::duplicate_attribute(m, row),
                    "er/duplicate-entity" => super::er::duplicate_entity(m, row),
                    "er/standalone-entity" => super::er::standalone_entity(m, row),
                    _ => Vec::new(),
                }
            } else {
                Vec::new()
            }
        }
        _ => Vec::new(),
    };
    let requirement_diagnostics = |row: &LintRule| match row.code {
        "requirement/duplicate-name"
        | "requirement/duplicate-id"
        | "requirement/undefined-reference"
            if block.kind == Some("requirement") =>
        {
            if let Some(crate::model::Resolved::Requirement(m)) = model {
                super::requirement::run(m, row)
            } else {
                Vec::new()
            }
        }
        _ => Vec::new(),
    };
    let c4_diagnostics = |row: &LintRule| match row.code {
        "c4/duplicate-id"
        | "c4/undefined-relationship-endpoint"
        | "c4/undefined-element-style"
        | "c4/undefined-relationship-style-endpoint"
            if block.kind == Some("c4") =>
        {
            if let Some(crate::model::Resolved::C4(m)) = model {
                super::c4::run(m, row)
            } else {
                Vec::new()
            }
        }
        _ => Vec::new(),
    };
    let treeview_diagnostics = |row: &LintRule| match row.code {
        "treeview/no-nodes" if block.kind == Some("treeview") => {
            if let Some(crate::model::Resolved::Treeview(m)) = model {
                super::treeview::no_nodes(m, row)
            } else {
                Vec::new()
            }
        }
        "treeview/duplicate-sibling" if block.kind == Some("treeview") => {
            if let Some(crate::model::Resolved::Treeview(m)) = model {
                super::treeview::duplicate_sibling(m, row)
            } else {
                Vec::new()
            }
        }
        _ => Vec::new(),
    };
    let ishikawa_diagnostics = |row: &LintRule| match row.code {
        "ishikawa/no-causes" if block.kind == Some("ishikawa") => {
            if let Some(crate::model::Resolved::Ishikawa(m)) = model {
                super::ishikawa::no_causes(m, row)
            } else {
                Vec::new()
            }
        }
        "ishikawa/empty-category" if block.kind == Some("ishikawa") => {
            if let Some(crate::model::Resolved::Ishikawa(m)) = model {
                super::ishikawa::empty_category(m, row)
            } else {
                Vec::new()
            }
        }
        "ishikawa/deep-nesting" if block.kind == Some("ishikawa") => {
            if let Some(crate::model::Resolved::Ishikawa(m)) = model {
                super::ishikawa::deep_nesting(m, row)
            } else {
                Vec::new()
            }
        }
        "ishikawa/duplicate-sibling" if block.kind == Some("ishikawa") => {
            if let Some(crate::model::Resolved::Ishikawa(m)) = model {
                super::ishikawa::duplicate_sibling(m, row)
            } else {
                Vec::new()
            }
        }
        _ => Vec::new(),
    };
    let kanban_diagnostics = |row: &LintRule| match row.code {
        "kanban/no-columns" if block.kind == Some("kanban") => {
            if let Some(crate::model::Resolved::Kanban(m)) = model {
                super::kanban::no_columns(m, row)
            } else {
                Vec::new()
            }
        }
        "kanban/empty-column" if block.kind == Some("kanban") => {
            if let Some(crate::model::Resolved::Kanban(m)) = model {
                super::kanban::empty_column(m, row)
            } else {
                Vec::new()
            }
        }
        "kanban/duplicate-column" if block.kind == Some("kanban") => {
            if let Some(crate::model::Resolved::Kanban(m)) = model {
                super::kanban::duplicate_column(m, row)
            } else {
                Vec::new()
            }
        }
        "kanban/duplicate-task-id" if block.kind == Some("kanban") => {
            if let Some(crate::model::Resolved::Kanban(m)) = model {
                super::kanban::duplicate_task_id(m, row)
            } else {
                Vec::new()
            }
        }
        _ => Vec::new(),
    };
    let architecture_diagnostics = |row: &LintRule| match row.code {
        "architecture/no-elements" if block.kind == Some("architecture") => {
            if let Some(crate::model::Resolved::Architecture(m)) = model {
                super::architecture::no_elements(m, row)
            } else {
                Vec::new()
            }
        }
        "architecture/no-edges" if block.kind == Some("architecture") => {
            if let Some(crate::model::Resolved::Architecture(m)) = model {
                super::architecture::no_edges(m, row)
            } else {
                Vec::new()
            }
        }
        "architecture/duplicate-edge" if block.kind == Some("architecture") => {
            if let Some(crate::model::Resolved::Architecture(m)) = model {
                super::architecture::duplicate_edge(m, row)
            } else {
                Vec::new()
            }
        }
        _ => Vec::new(),
    };
    let treemap_diagnostics = |row: &LintRule| match row.code {
        "treemap/zero-value"
        | "treemap/no-leaves"
        | "treemap/duplicate-sibling"
        | "treemap/branch-with-value"
            if block.kind == Some("treemap") =>
        {
            if let Some(crate::model::Resolved::Treemap(m)) = model {
                super::treemap::run(m, row)
            } else {
                Vec::new()
            }
        }
        _ => Vec::new(),
    };
    let sankey_diagnostics = |row: &LintRule| match row.code {
        "sankey/non-positive-value" | "sankey/duplicate-link" | "sankey/self-loop"
            if block.kind == Some("sankey") =>
        {
            if let Some(crate::model::Resolved::Sankey(m)) = model {
                super::sankey::run(m, row)
            } else {
                Vec::new()
            }
        }
        _ => Vec::new(),
    };
    let gantt_diagnostics = |row: &LintRule| match row.code {
        "gantt/duplicate-task-id" | "gantt/undefined-dependency" | "gantt/empty-section"
            if block.kind == Some("gantt") =>
        {
            if let Some(crate::model::Resolved::Gantt(m)) = model {
                super::gantt::run(m, row)
            } else {
                Vec::new()
            }
        }
        _ => Vec::new(),
    };
    let quadrant_diagnostics = |row: &LintRule| match row.code {
        "quadrant/duplicate-point"
        | "quadrant/no-points"
        | "quadrant/missing-x-axis"
        | "quadrant/missing-y-axis"
        | "quadrant/duplicate-quadrant"
            if block.kind == Some("quadrant") =>
        {
            if let Some(crate::model::Resolved::Quadrant(m)) = model {
                super::quadrant::run(m, row)
            } else {
                Vec::new()
            }
        }
        _ => Vec::new(),
    };
    let wardley_diagnostics = |row: &LintRule| match row.code {
        "wardley/undefined-component"
        | "wardley/orphan-component"
        | "wardley/no-components"
        | "wardley/mixed-coordinate-scale"
        | "wardley/duplicate-component"
            if block.kind == Some("wardley") =>
        {
            if let Some(crate::model::Resolved::Wardley(m)) = model {
                super::wardley::run(m, row)
            } else {
                Vec::new()
            }
        }
        _ => Vec::new(),
    };
    let pie_diagnostics = |row: &LintRule| match row.code {
        "pie/duplicate-label" | "pie/zero-value" | "pie/no-data" if block.kind == Some("pie") => {
            if let Some(crate::model::Resolved::Pie(m)) = model {
                super::pie::run(m, row)
            } else {
                Vec::new()
            }
        }
        _ => Vec::new(),
    };
    let venn_diagnostics = |row: &LintRule| match row.code {
        "venn/duplicate-set"
        | "venn/non-positive-size"
        | "venn/single-set"
        | "venn/self-union"
        | "venn/duplicate-union"
            if block.kind == Some("venn") =>
        {
            if let Some(crate::model::Resolved::Venn(m)) = model {
                super::venn::run(m, row)
            } else {
                Vec::new()
            }
        }
        _ => Vec::new(),
    };
    let journey_diagnostics = |row: &LintRule| match row.code {
        "journey/empty-section" | "journey/task-without-actor" | "journey/no-tasks"
            if block.kind == Some("journey") =>
        {
            if let Some(crate::model::Resolved::Journey(m)) = model {
                super::journey::run(m, row)
            } else {
                Vec::new()
            }
        }
        _ => Vec::new(),
    };
    for row in LINT_RULES {
        let Some(severity) = effective(row, config) else {
            continue;
        };
        for mut diagnostic in match row.code {
            "common/acc-title-missing" => common::acc_title_missing(block, row),
            "common/acc-descr-missing" => common::acc_descr_missing(block, row),
            "common/no-experimental" => common::no_experimental(block, row),
            _ => match block.kind {
                Some("flowchart") => flowchart_diagnostics(row),
                Some("xychart") => xychart_diagnostics(row),
                Some("timeline") => timeline_diagnostics(row),
                Some("packet") => packet_diagnostics(row),
                Some("radar") => radar_diagnostics(row),
                Some("sequence") => sequence_diagnostics(row),
                Some("gitgraph") => gitgraph_diagnostics(row),
                Some("mindmap") => mindmap_diagnostics(row),
                Some("block") => block_diagnostics(row),
                Some("eventmodeling") => eventmodeling_diagnostics(row),
                Some("class") => class_diagnostics(row),
                Some("state") => state_diagnostics(row),
                Some("er") => er_diagnostics(row),
                Some("requirement") => requirement_diagnostics(row),
                Some("c4") => c4_diagnostics(row),
                Some("treeview") => treeview_diagnostics(row),
                Some("ishikawa") => ishikawa_diagnostics(row),
                Some("kanban") => kanban_diagnostics(row),
                Some("architecture") => architecture_diagnostics(row),
                Some("treemap") => treemap_diagnostics(row),
                Some("sankey") => sankey_diagnostics(row),
                Some("gantt") => gantt_diagnostics(row),
                Some("quadrant") => quadrant_diagnostics(row),
                Some("wardley") => wardley_diagnostics(row),
                Some("pie") => pie_diagnostics(row),
                Some("venn") => venn_diagnostics(row),
                Some("journey") => journey_diagnostics(row),
                _ => Vec::new(),
            },
        } {
            diagnostic.severity = severity;
            out.push(diagnostic);
        }
    }
    out
}

fn flowchart_model(model: Option<&crate::model::Resolved>, row: &LintRule) -> Vec<Diagnostic> {
    let Some(crate::model::Resolved::Flowchart(model)) = model else {
        return Vec::new();
    };
    match row.code {
        "flowchart/duplicate-ids" => flowchart::duplicate_ids(model, row),
        "flowchart/subgraph-id-collision" => flowchart::subgraph_id_collisions(model, row),
        "flowchart/label-at-in-unquoted" => flowchart::label_at_in_unquoted(model, row),
        _ => Vec::new(),
    }
}

/// Whether a configured code, written as an alias or as a current code, names
/// the row.
fn names_row(configured: &str, row: &LintRule) -> bool {
    super::describe::canonical_code(configured).unwrap_or(configured) == row.code
}

fn effective(row: &LintRule, config: &LintConfig) -> Option<Severity> {
    let listed = |codes: &[String]| codes.iter().any(|code| names_row(code, row));
    if listed(&config.off) || listed(&config.ignore) {
        return None;
    }
    let overridden = config
        .severity
        .iter()
        .find(|(code, _)| names_row(code, row))
        .map(|(_, severity)| *severity);
    let selected_or_default = if config.select.is_empty() {
        row.severity != "off"
    } else {
        listed(&config.select)
    };
    if overridden.is_none() && !selected_or_default {
        return None;
    }
    let default = match row.severity {
        "off" => Severity::Warning,
        other => severity_of(other)?,
    };
    Some(overridden.unwrap_or(default))
}

fn severity_of(word: &str) -> Option<Severity> {
    match word {
        "error" => Some(Severity::Error),
        "warning" => Some(Severity::Warning),
        "info" => Some(Severity::Info),
        _ => None,
    }
}

/// Parses, lints, and applies fixes of safety at most `max` until a pass
/// applies no fix, with at most 10 passes; a pass that adds an error by the
/// `(code, span start)` multiset rule is discarded and fixing stops.
pub fn apply_fixes(source: &[u8], config: &LintConfig, max: crate::diag::FixSafety) -> FixOutcome {
    fix_passes(source, max, |text| {
        let document = crate::document::parse_bytes(text.as_bytes());
        let current = pass(&document, config);
        let mut combined = current.syntax;
        combined.extend(current.lint);
        crate::diag::sort(&mut combined);
        combined
    })
}

/// The fix loop shared by single sources and Markdown hosts. `analyze` returns
/// the sorted diagnostics of one text, with spans in that text.
pub(crate) fn fix_passes(
    source: &[u8],
    max: crate::diag::FixSafety,
    analyze: impl Fn(&str) -> Vec<Diagnostic>,
) -> FixOutcome {
    let (repaired, _) = crate::source::repair_utf8(source);
    let mut text = repaired.into_owned();
    let mut applied = 0;
    for _ in 0..10 {
        let Some(next) = one_pass(&text, max, &analyze, &mut applied) else {
            break;
        };
        text = next;
    }
    FixOutcome { text, applied }
}

fn one_pass(
    text: &str,
    max: crate::diag::FixSafety,
    analyze: &impl Fn(&str) -> Vec<Diagnostic>,
    applied: &mut usize,
) -> Option<String> {
    let combined = analyze(text);
    let edits = chosen_edits(&combined, max);
    let kept = non_overlapping(&edits);
    if kept.is_empty() {
        return None;
    }
    let next = apply_edits(text, &kept);
    let after_all = analyze(&next);
    if adds_error(&combined, &after_all, &kept) {
        return None;
    }
    *applied += distinct_orders(&edits) - dropped_orders(&edits).len();
    Some(next)
}

type OrderedEdit<'a> = (&'a crate::diag::Edit, usize);

fn chosen_edits<'a>(
    diagnostics: &'a [Diagnostic],
    max: crate::diag::FixSafety,
) -> Vec<OrderedEdit<'a>> {
    let mut edits: Vec<OrderedEdit<'a>> = Vec::new();
    for (order, diagnostic) in diagnostics.iter().enumerate() {
        let Some(fix) = diagnostic.fixes.iter().find(|fix| fix.safety <= max) else {
            continue;
        };
        for edit in &fix.edits {
            edits.push((edit, order));
        }
    }
    edits.sort_by(|(left, left_order), (right, right_order)| {
        left.span
            .start
            .cmp(&right.span.start)
            .then(left.span.end.cmp(&right.span.end))
            .then(left_order.cmp(right_order))
    });
    edits
}

fn non_overlapping<'a>(edits: &[OrderedEdit<'a>]) -> Vec<&'a crate::diag::Edit> {
    let dropped = dropped_orders(edits);
    let mut last_end = 0;
    let mut kept = Vec::new();
    for (edit, order) in edits {
        if dropped.contains(order) {
            continue;
        }
        if edit.span.start >= last_end {
            kept.push(*edit);
            last_end = last_end.max(edit.span.end);
        }
    }
    kept
}

fn dropped_orders(edits: &[OrderedEdit<'_>]) -> BTreeSet<usize> {
    let mut dropped = BTreeSet::new();
    let mut last_end = 0;
    for (edit, order) in edits {
        if dropped.contains(order) {
            continue;
        }
        if edit.span.start < last_end {
            dropped.insert(*order);
        } else {
            last_end = last_end.max(edit.span.end);
        }
    }
    dropped
}

fn distinct_orders(edits: &[OrderedEdit<'_>]) -> usize {
    edits
        .iter()
        .map(|(_, order)| *order)
        .collect::<BTreeSet<_>>()
        .len()
}

fn apply_edits(text: &str, edits: &[&crate::diag::Edit]) -> String {
    let mut next = String::with_capacity(text.len());
    let mut cursor = 0;
    for edit in edits {
        next.push_str(&text[cursor..edit.span.start]);
        next.push_str(&edit.new_text);
        cursor = edit.span.end;
    }
    next.push_str(&text[cursor..]);
    next
}

/// Compares the multiset of `(code, span start)` over the error-severity
/// diagnostics; the before-pass starts shift through the applied edits, so a
/// diagnostic that only moved counts as the same element.
fn adds_error(before: &[Diagnostic], after: &[Diagnostic], edits: &[&crate::diag::Edit]) -> bool {
    let mut counts: BTreeMap<(&str, usize), i64> = BTreeMap::new();
    for diagnostic in before {
        if diagnostic.severity == Severity::Error {
            let start = shifted_start(diagnostic.span.start, edits);
            *counts.entry((diagnostic.code, start)).or_insert(0) += 1;
        }
    }
    for diagnostic in after {
        if diagnostic.severity != Severity::Error {
            continue;
        }
        let count = counts
            .entry((diagnostic.code, diagnostic.span.start))
            .or_insert(0);
        *count -= 1;
        if *count < 0 {
            return true;
        }
    }
    false
}

fn shifted_start(start: usize, edits: &[&crate::diag::Edit]) -> usize {
    let mut delta: isize = 0;
    for edit in edits {
        let removed = isize::try_from(edit.span.end - edit.span.start).unwrap_or(isize::MAX);
        let added = isize::try_from(edit.new_text.len()).unwrap_or(isize::MAX);
        if edit.span.end <= start {
            delta += added - removed;
        } else if edit.span.start <= start {
            return edit.span.start.saturating_add_signed(delta);
        } else {
            break;
        }
    }
    start.saturating_add_signed(delta)
}
