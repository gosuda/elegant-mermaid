use super::*;
use crate::syntax::preprocess::preprocess;

fn resolved(source: &str) -> (Model, Vec<Diagnostic>) {
    let removed = preprocess(source).removed;
    let parsed = crate::syntax::gitgraph::parse(source, &removed);
    let (model, mut diagnostics) = resolve(source, &parsed.document);
    let mut all = parsed.diagnostics;
    all.append(&mut diagnostics);
    (model, all)
}

fn ids(model: &Model) -> Vec<&str> {
    model.commits.iter().map(|c| c.id.as_str()).collect()
}

fn messages(diagnostics: &[Diagnostic]) -> Vec<String> {
    diagnostics
        .iter()
        .map(|d| format!("{} {}: {}", d.severity.as_str(), d.code, d.message))
        .collect()
}

#[test]
fn generated_ids_use_the_global_index() {
    let (model, diagnostics) = resolved(
        "gitGraph\ncommit\ncommit id: \"\"\nbranch dev\ncommit\ncheckout main\nmerge dev\ncommit id: \"x\"\nbranch other\ncherry-pick id: \"x\"\n",
    );
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    assert_eq!(
        ids(&model),
        ["main-0", "main-1", "dev-2", "main-3", "x", "other-5"]
    );
    assert_eq!(model.commits[3].kind, CommitKind::Merge);
    assert_eq!(model.commits[3].parents, ["main-1", "dev-2"]);
    assert_eq!(model.commits[5].kind, CommitKind::CherryPick);
    assert_eq!(model.commits[5].pick, "x");
}

#[test]
fn branch_copies_the_head_and_checkout_restores_it() {
    let (model, diagnostics) = resolved(
        "gitGraph\ncommit id: \"a\"\nbranch dev\ncommit id: \"b\"\ncheckout main\ncommit id: \"c\"\ncheckout dev\ncommit id: \"d\"\nbranch empty\ncheckout main\nbranch fresh\n",
    );
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    let parents: Vec<&[String]> = model.commits[..4]
        .iter()
        .map(|c| c.parents.as_slice())
        .collect();
    assert_eq!(
        parents,
        [
            &[][..],
            &["a".to_owned()][..],
            &["a".to_owned()][..],
            &["b".to_owned()][..]
        ]
    );
    let names: Vec<&str> = model.branches.iter().map(|b| b.name.as_str()).collect();
    assert_eq!(names, ["main", "dev", "empty", "fresh"]);
}

#[test]
fn branch_order_keeps_absence_separate_from_zero() {
    let (model, diagnostics) =
        resolved("gitGraph\nbranch a\nbranch b order: 0\nbranch c order: 4\n");
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    assert!(!model.branches[1].has_order);
    assert!(model.branches[2].has_order);
    assert_eq!(model.branches[2].order, 0);
    assert_eq!(model.branches[3].order, 4);
}

#[test]
fn branch_and_checkout_errors() {
    let (model, diagnostics) =
        resolved("gitGraph\nbranch main\ncheckout nope\nbranch dev\nbranch dev\ncommit\n");
    assert_eq!(
        messages(&diagnostics),
        [
            "error gitgraph/branch-already-exists: branch main already exists",
            "error gitgraph/unknown-branch: branch nope does not exist",
            "error gitgraph/branch-already-exists: branch dev already exists",
        ]
    );
    assert_eq!(model.commits[0].id, "dev-0");
    assert_eq!(model.commits[0].branch, 1);
}

#[test]
fn merge_validation_order() {
    let self_merge = "error gitgraph/merge-with-self: cannot merge branch main into itself";
    for (source, want) in [
        ("gitGraph\ncommit\nmerge main", self_merge),
        (
            "gitGraph\ncommit\nbranch dev\ncommit\ncheckout main\nbranch x\nmerge main",
            self_merge,
        ),
        (
            "gitGraph\nmerge dev",
            "error gitgraph/merge-current-empty: current branch main has no commits to merge",
        ),
        (
            "gitGraph\ncommit\nmerge dev",
            "error gitgraph/merge-unknown-branch: merge branch dev does not exist",
        ),
        (
            "gitGraph\nbranch empty\ncheckout main\ncommit\nmerge empty",
            "error gitgraph/merge-branch-empty: merge branch empty has no commits",
        ),
        (
            "gitGraph\ncommit\nbranch dev\ncheckout main\nmerge dev",
            "error gitgraph/merge-same-head: branches have the same head",
        ),
        (
            "gitGraph\ncommit id: \"a\"\nbranch dev\ncommit\ncheckout main\ncommit\nmerge dev id: \"a\"",
            "error gitgraph/merge-duplicate-commit-id: merge commit id a already exists",
        ),
    ] {
        let (model, diagnostics) = resolved(source);
        assert_eq!(messages(&diagnostics), [want], "{source}");
        assert!(
            model.commits.iter().all(|c| c.kind != CommitKind::Merge),
            "{source}"
        );
    }
}

#[test]
fn rejected_statements_leave_the_sequence_untouched() {
    let (model, diagnostics) = resolved("gitGraph\ncommit\nmerge main\ncommit\n");
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(ids(&model), ["main-0", "main-1"]);
}

#[test]
fn cherry_pick_validation_order_and_tags() {
    let prefix = "gitGraph\ncommit id: \"a\"\nbranch dev\ncommit id: \"b\"\ncheckout main\ncommit id: \"c\"\nmerge dev id: \"m\"\nbranch topic\n";
    for (pick, want) in [
        (
            "cherry-pick",
            "error gitgraph/cherry-pick-source-unknown: cherry-pick requires an existing source commit",
        ),
        (
            "cherry-pick id: \"zz\"",
            "error gitgraph/cherry-pick-source-unknown: cherry-pick requires an existing source commit zz",
        ),
        (
            "cherry-pick id: \"b\" parent: \"zz\"",
            "error gitgraph/cherry-pick-parent-invalid: commit zz is not an immediate parent of b",
        ),
        (
            "cherry-pick id: \"m\"",
            "error gitgraph/cherry-pick-parent-required: cherry-pick of merge commit m requires a parent",
        ),
        (
            "cherry-pick id: \"c\" parent: \"m\"",
            "error gitgraph/cherry-pick-parent-invalid: commit m is not an immediate parent of c",
        ),
    ] {
        let (_, diagnostics) = resolved(&format!("{prefix}{pick}\n"));
        assert_eq!(messages(&diagnostics), [want], "{pick}");
    }
    let (_, diagnostics) = resolved("gitGraph\ncommit id: \"a\"\ncherry-pick id: \"a\"\n");
    assert_eq!(
        messages(&diagnostics),
        ["error gitgraph/cherry-pick-current-branch: commit a is already on the current branch"]
    );
    let (_, diagnostics) = resolved(
        "gitGraph\ncommit id: \"a\"\nbranch dev\ncheckout main\nbranch empty\ncherry-pick id: \"a\"\ncheckout dev\n",
    );
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    let (model, diagnostics) = resolved(&format!(
        "{prefix}cherry-pick id: \"m\" parent: \"c\"\ncherry-pick id: \"b\" tag: \"mine\"\n"
    ));
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    let last = &model.commits[model.commits.len() - 2..];
    assert_eq!(last[0].tags, ["cherry-pick:m|parent:c"]);
    assert_eq!(last[1].tags, ["mine"]);
    assert_eq!(last[0].parents, ["m"]);
    assert_eq!(model.branches[last[0].branch].name, "topic");
}

#[test]
fn cherry_pick_into_empty_branch_is_rejected() {
    let (_, diagnostics) =
        resolved("gitGraph\nbranch dev\ncommit id: \"z\"\ncheckout main\ncherry-pick id: \"z\"\n");
    assert_eq!(
        messages(&diagnostics),
        [
            "error gitgraph/cherry-pick-current-empty: current branch main has no commits for cherry-pick"
        ]
    );
}

#[test]
fn duplicate_commit_id_replaces_the_record_in_place() -> Result<(), &'static str> {
    let source = "gitGraph\ncommit id: \"a\" tag: \"first\"\ncommit id: \"b\"\ncommit id: \"a\" type: REVERSE\ncommit\n";
    let (model, diagnostics) = resolved(source);
    assert_eq!(diagnostics.len(), 1);
    let duplicates = &diagnostics;
    assert_eq!(duplicates[0].code, "gitgraph/duplicate-commit-id");
    assert_eq!(duplicates[0].severity, crate::Severity::Warning);
    assert_eq!(duplicates[0].message, "commit id a already exists");
    let start = source.rfind("\"a\"").ok_or("duplicate commit id")?;
    assert_eq!(
        duplicates[0].span,
        Span {
            start,
            end: start + 3
        }
    );
    assert!(duplicates[0].related.is_empty());
    assert_eq!(
        &source[duplicates[0].span.start..duplicates[0].span.end],
        "\"a\""
    );
    assert_replaced_commit_record(&model);
    Ok(())
}

fn assert_replaced_commit_record(model: &Model) {
    assert_eq!(ids(model), ["a", "b", "main-3"]);
    assert_eq!(model.commits[0].seq, 2);
    assert_eq!(model.commits[0].commit_type, CommitType::Reverse);
    assert!(model.commits[0].tags.is_empty());
    assert_eq!(model.commits[2].parents, ["a"]);
    assert_eq!(model.commit_history.len(), 4);
    assert_eq!(model.commit_history[0].tags, ["first"]);
    assert_eq!(model.commit_history[2].id, "a");
}

#[test]
fn generated_id_collision_warns_at_the_keyword() {
    let source = "gitGraph\ncommit id: \"main-1\"\ncommit\n";
    let (model, diagnostics) = resolved(source);
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(ids(&model), ["main-1"]);
    assert_eq!(model.commits[0].seq, 1);
    let duplicates = &diagnostics;
    assert_eq!(duplicates[0].code, "gitgraph/duplicate-commit-id");
    assert_eq!(duplicates[0].severity, crate::Severity::Warning);
    assert_eq!(duplicates[0].span, Span { start: 29, end: 35 });
    assert_eq!(duplicates[0].message, "commit id main-1 already exists");
    assert!(duplicates[0].related.is_empty());
    assert_eq!(model.commit_history.len(), 2);
    assert_eq!(model.commit_history[0].seq, 0);
    assert_eq!(model.commit_history[1].seq, 1);
}

#[test]
fn main_branch_name_and_order_config() {
    let (model, diagnostics) = resolved(
        "---\nconfig:\n  gitGraph:\n    mainBranchName: 'trunk'\n    mainBranchOrder: 3\n---\ngitGraph\ncommit\ncheckout trunk\ncommit\nbranch main\ncommit\n",
    );
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    assert_eq!(model.branches[0].name, "trunk");
    assert!(model.branches[0].has_order);
    assert_eq!(model.branches[0].order, 3);
    assert_eq!(model.branches[1].name, "main");
    assert_eq!(ids(&model), ["trunk-0", "trunk-1", "main-2"]);
}

#[test]
fn main_branch_rename_rejects_the_default_name() {
    let (_, diagnostics) = resolved(
        "---\nconfig:\n  gitGraph:\n    mainBranchName: trunk\n---\ngitGraph\ncommit\ncheckout main\n",
    );
    assert_eq!(
        messages(&diagnostics),
        ["error gitgraph/unknown-branch: branch main does not exist"]
    );
}

#[test]
fn main_branch_init_directive_overrides_frontmatter() {
    let (model, diagnostics) = resolved(
        "---\nconfig:\n  gitGraph:\n    mainBranchName: trunk\n    mainBranchOrder: 1\n---\n%%{init: {'gitGraph': {'mainBranchName': 'prod', 'mainBranchOrder': -2}}}%%\ngitGraph\ncommit\n",
    );
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    assert_eq!(model.branches[0].name, "prod");
    assert_eq!(model.branches[0].order, -2);
    assert_eq!(model.commits[0].id, "prod-0");
}

#[test]
fn main_branch_config_ignores_unusable_values() {
    let (model, diagnostics) = resolved(
        "---\nconfig:\n  gitGraph:\n    mainBranchName: 5\n    mainBranchOrder: 1.5\n---\ngitGraph\ncommit\n",
    );
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    assert_eq!(model.branches[0].name, "main");
    assert!(!model.branches[0].has_order);
    let (model, diagnostics) =
        resolved("---\nconfig:\n  gitGraph:\n    mainBranchName: ''\n---\ngitGraph\ncommit\n");
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    assert_eq!(model.branches[0].name, "main");
}

#[test]
fn config_keys_and_direction() {
    let (model, diagnostics) = resolved(
        "---\nconfig:\n  gitGraph:\n    showBranches: false\n    rotateCommitLabel: true\n    parallelCommits: true\n---\n%%{init: {'gitGraph': {'showBranches': true, 'showCommitLabel': false}}}%%\ngitGraph BT:\ncommit\n",
    );
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    assert_eq!(model.direction, "BT");
    let config: Vec<(&str, bool)> = model.config.iter().map(|(k, v)| (k.as_str(), *v)).collect();
    assert_eq!(
        config,
        [
            ("rotateCommitLabel", true),
            ("showBranches", true),
            ("showCommitLabel", false)
        ]
    );
    let (model, _) = resolved("gitGraph\ncommit\n");
    assert_eq!(model.direction, "LR");
    assert!(model.config.is_empty());
}

#[test]
fn metadata_last_occurrence_wins() {
    let (model, diagnostics) =
        resolved("gitGraph\ntitle one\ntitle two\naccTitle: a\naccDescr: d\naccTitle: b\n");
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    assert_eq!(
        [
            model.title.as_str(),
            model.acc_title.as_str(),
            model.acc_descr.as_str()
        ],
        ["two", "b", "d"]
    );
}
