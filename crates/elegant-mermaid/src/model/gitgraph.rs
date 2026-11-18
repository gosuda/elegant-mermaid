//! Semantic resolution of the gitgraph model (`spec/grammar/gitgraph.md`, resolution).

use std::collections::BTreeMap;

use crate::diag::Diagnostic;
use crate::source::Span;
use crate::syntax::config_value::ConfigValue;
use crate::syntax::gitgraph::ast::{
    Branch as BranchNode, Checkout, CherryPicking, Commit as CommitNode, Merge, Metadata, Start,
    Statement, StatementKind, Value,
};
use crate::syntax::gitgraph::diagnostic;
use crate::syntax::preprocess::preprocess;

pub const DEFAULT_MAIN_BRANCH: &str = "main";

pub const HONOURED: &[&str] = &["rotateCommitLabel", "showBranches", "showCommitLabel"];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CommitKind {
    Commit,
    Merge,
    CherryPick,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CommitType {
    Normal,
    Reverse,
    Highlight,
}

#[derive(Debug, Clone)]
pub struct Branch {
    pub name: String,
    pub order: i64,
    pub has_order: bool,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Commit {
    pub id: String,
    pub seq: usize,
    pub branch: usize,
    pub parents: Vec<String>,
    pub pick: String,
    pub kind: CommitKind,
    pub commit_type: CommitType,
    pub tags: Vec<String>,
    pub message: String,
    pub span: Span,
}

#[derive(Debug, Clone, Default)]
pub struct Model {
    pub acc_title: String,
    pub acc_descr: String,
    pub title: String,
    pub direction: String,
    pub branches: Vec<Branch>,
    pub commits: Vec<Commit>,
    pub config: BTreeMap<String, bool>,
    pub commit_history: Vec<Commit>,
}

#[derive(Clone, Default)]
struct Head {
    id: String,
    set: bool,
}

pub fn resolve(source: &str, document: &Start) -> (Model, Vec<Diagnostic>) {
    let mut resolver = Resolver::new(source, document);
    for statement in &document.statements {
        resolver.statement(statement);
    }
    (resolver.model, resolver.diagnostics)
}

struct Resolver {
    model: Model,
    diagnostics: Vec<Diagnostic>,
    heads: Vec<Head>,
    current: usize,
    seq: usize,
    commits: BTreeMap<String, usize>,
    names: BTreeMap<String, usize>,
}

fn read_config(model: &mut Model, block: &ConfigValue) {
    let ConfigValue::Mapping(entries) = block else {
        return;
    };
    let Some(git) = entries.iter().find(|entry| entry.key == "gitGraph") else {
        return;
    };
    let ConfigValue::Mapping(fields) = &git.value else {
        return;
    };
    for field in fields {
        read_field(model, &field.key, &field.value);
    }
}

fn read_field(model: &mut Model, key: &str, value: &ConfigValue) {
    match (key, value) {
        ("mainBranchName", ConfigValue::String(name)) if !name.is_empty() => {
            model.branches[0].name.clone_from(name);
        }
        ("mainBranchOrder", ConfigValue::Integer(text)) => {
            if let Ok(order) = text.parse::<i64>() {
                model.branches[0].order = order;
                model.branches[0].has_order = true;
            }
        }
        (_, ConfigValue::Bool(flag)) if HONOURED.contains(&key) => {
            model.config.insert(key.to_owned(), *flag);
        }
        _ => {}
    }
}

fn commit_type(value: Option<&Value>) -> CommitType {
    match value.map(|v| v.text.as_str()) {
        Some("REVERSE") => CommitType::Reverse,
        Some("HIGHLIGHT") => CommitType::Highlight,
        _ => CommitType::Normal,
    }
}

fn values(tags: &[Value]) -> Vec<String> {
    tags.iter().map(|tag| tag.text.clone()).collect()
}

impl Resolver {
    fn new(source: &str, document: &Start) -> Self {
        let mut model = Model {
            direction: document
                .direction
                .as_ref()
                .map_or("LR", |token| token.kind)
                .to_owned(),
            branches: vec![Branch {
                name: DEFAULT_MAIN_BRANCH.to_owned(),
                order: 0,
                has_order: false,
                span: Span { start: 0, end: 0 },
            }],
            ..Model::default()
        };
        let preprocessed = preprocess(source);
        for block in [
            preprocessed.frontmatter.and_then(|f| f.config),
            preprocessed.init_config,
        ]
        .into_iter()
        .flatten()
        {
            read_config(&mut model, &block);
        }
        let names = BTreeMap::from([(model.branches[0].name.clone(), 0)]);
        Resolver {
            model,
            diagnostics: Vec::new(),
            heads: vec![Head::default()],
            current: 0,
            seq: 0,
            commits: BTreeMap::new(),
            names,
        }
    }

    fn issue(&mut self, code: &'static str, message: String, span: Span) {
        self.diagnostics.push(diagnostic(code, message, span));
    }

    fn statement(&mut self, statement: &Statement) {
        match &statement.kind {
            StatementKind::Commit(node) => self.commit(statement.span, node),
            StatementKind::Branch(node) => self.branch(node),
            StatementKind::Merge(node) => self.merge(statement.span, node),
            StatementKind::Checkout(node) => self.checkout(node),
            StatementKind::CherryPicking(node) => self.cherry_pick(statement.span, node),
            StatementKind::Metadata(node) => self.metadata(node),
        }
    }

    fn metadata(&mut self, node: &Metadata) {
        match node.field {
            "title" => self.model.title.clone_from(&node.value),
            "accTitle" => self.model.acc_title.clone_from(&node.value),
            _ => self.model.acc_descr.clone_from(&node.value),
        }
    }

    fn branch_name(&self, index: usize) -> &str {
        self.model
            .branches
            .get(index)
            .map_or("", |branch| branch.name.as_str())
    }

    fn head_id(&self) -> Option<&str> {
        self.heads
            .get(self.current)
            .filter(|head| head.set)
            .map(|head| head.id.as_str())
    }

    fn parents_of_head(&self) -> Vec<String> {
        self.head_id().map(str::to_owned).into_iter().collect()
    }

    fn new_commit(&mut self, kind: CommitKind, span: Span) -> Commit {
        let commit = Commit {
            id: String::new(),
            seq: self.seq,
            branch: self.current,
            parents: self.parents_of_head(),
            pick: String::new(),
            kind,
            commit_type: CommitType::Normal,
            tags: Vec::new(),
            message: String::new(),
            span,
        };
        self.seq += 1;
        commit
    }

    fn identify(&mut self, mut commit: Commit, explicit: Option<&Value>, keyword: Span) {
        match explicit.filter(|value| !value.text.is_empty()) {
            Some(value) => {
                commit.id.clone_from(&value.text);
                self.record(commit, value.span);
            }
            None => {
                commit.id = format!("{}-{}", self.branch_name(commit.branch), commit.seq);
                self.record(commit, keyword);
            }
        }
    }

    fn record(&mut self, commit: Commit, id_span: Span) {
        self.model.commit_history.push(commit.clone());
        let id = commit.id.clone();
        if let Some(&at) = self.commits.get(&id) {
            let mut warning = diagnostic(
                "gitgraph/duplicate-commit-id",
                format!("commit id {id} already exists"),
                id_span,
            );
            warning.severity = crate::diag::Severity::Warning;
            self.diagnostics.push(warning);
            self.model.commits[at] = commit;
        } else {
            self.commits.insert(id.clone(), self.model.commits.len());
            self.model.commits.push(commit);
        }
        self.heads[self.current] = Head { id, set: true };
    }

    fn commit(&mut self, span: Span, node: &CommitNode) {
        let mut commit = self.new_commit(CommitKind::Commit, span);
        commit.commit_type = commit_type(node.commit_type.as_ref());
        commit.tags = values(&node.tags);
        if let Some(message) = &node.message {
            commit.message.clone_from(&message.text);
        }
        self.identify(commit, node.id.as_ref(), node.keyword);
    }

    fn branch(&mut self, node: &BranchNode) {
        let name = &node.name;
        if self.names.contains_key(&name.text) {
            let message = format!("branch {} already exists", name.text);
            self.issue("gitgraph/branch-already-exists", message, name.span);
            return;
        }
        let mut branch = Branch {
            name: name.text.clone(),
            order: 0,
            has_order: false,
            span: name.span,
        };
        if let Some(order) = &node.order {
            branch.order = order.value;
            branch.has_order = true;
        }
        let copied = self.heads[self.current].clone();
        self.names
            .insert(name.text.clone(), self.model.branches.len());
        self.model.branches.push(branch);
        self.heads.push(copied);
        self.current = self.model.branches.len() - 1;
    }

    fn checkout(&mut self, node: &Checkout) {
        match self.names.get(&node.branch.text) {
            Some(&index) => self.current = index,
            None => {
                let message = format!("branch {} does not exist", node.branch.text);
                self.issue("gitgraph/unknown-branch", message, node.branch.span);
            }
        }
    }

    fn merge(&mut self, span: Span, node: &Merge) {
        let Some(other) = self.merge_target(node) else {
            return;
        };
        let mut commit = self.new_commit(CommitKind::Merge, span);
        let current = self.heads[self.current].id.clone();
        commit.parents = vec![current, self.heads[other].id.clone()];
        commit.commit_type = commit_type(node.commit_type.as_ref());
        commit.tags = values(&node.tags);
        self.identify(commit, node.id.as_ref(), node.keyword);
    }

    fn self_merge(&self, other: usize, known: bool) -> bool {
        if !known {
            return false;
        }
        if self.current == other {
            return true;
        }
        let Some(current) = self.head_id() else {
            return false;
        };
        self.heads[other].set
            && self
                .commits
                .get(current)
                .is_some_and(|&at| self.model.commits[at].branch == other)
    }

    fn merge_target(&mut self, node: &Merge) -> Option<usize> {
        let name = &node.branch;
        let found = self.names.get(&name.text).copied();
        let other = found.unwrap_or(0);
        let current = self.head_id().map(str::to_owned);
        if self.self_merge(other, found.is_some()) {
            let message = format!("cannot merge branch {} into itself", name.text);
            self.issue("gitgraph/merge-with-self", message, name.span);
            return None;
        }
        let failure = if current.is_none() {
            Some((
                "gitgraph/merge-current-empty",
                format!(
                    "current branch {} has no commits to merge",
                    self.branch_name(self.current)
                ),
                node.keyword,
            ))
        } else if found.is_none() {
            Some((
                "gitgraph/merge-unknown-branch",
                format!("merge branch {} does not exist", name.text),
                name.span,
            ))
        } else if !self.heads[other].set {
            Some((
                "gitgraph/merge-branch-empty",
                format!("merge branch {} has no commits", name.text),
                name.span,
            ))
        } else if current.as_deref() == Some(self.heads[other].id.as_str()) {
            Some((
                "gitgraph/merge-same-head",
                "branches have the same head".to_owned(),
                name.span,
            ))
        } else {
            self.duplicate_merge_id(node)
        };
        match failure {
            Some((code, message, span)) => {
                self.issue(code, message, span);
                None
            }
            None => Some(other),
        }
    }

    fn duplicate_merge_id(&self, node: &Merge) -> Option<(&'static str, String, Span)> {
        let id = node.id.as_ref().filter(|id| !id.text.is_empty())?;
        self.commits.contains_key(&id.text).then(|| {
            (
                "gitgraph/merge-duplicate-commit-id",
                format!("merge commit id {} already exists", id.text),
                id.span,
            )
        })
    }

    fn cherry_pick(&mut self, span: Span, node: &CherryPicking) {
        let Some(picked) = self.pick_source(node) else {
            return;
        };
        let mut commit = self.new_commit(CommitKind::CherryPick, span);
        commit.pick.clone_from(&picked.id);
        commit.tags = values(&node.tags);
        if commit.tags.is_empty() {
            commit.tags = vec![pick_tag(&picked, node.parent.as_ref())];
        }
        self.identify(commit, None, node.keyword);
    }

    fn pick_source(&mut self, node: &CherryPicking) -> Option<Commit> {
        let at = node
            .id
            .as_ref()
            .and_then(|id| self.commits.get(&id.text).copied());
        let Some(at) = at else {
            self.pick_unknown(node);
            return None;
        };
        let picked = self.model.commits[at].clone();
        match self.pick_failure(node, &picked) {
            Some((code, message, span)) => {
                self.issue(code, message, span);
                None
            }
            None => Some(picked),
        }
    }

    fn pick_failure(
        &self,
        node: &CherryPicking,
        picked: &Commit,
    ) -> Option<(&'static str, String, Span)> {
        let id_span = node.id.as_ref().map_or(node.keyword, |id| id.span);
        if let Some(parent) = &node.parent
            && !picked.parents.contains(&parent.text)
        {
            return Some((
                "gitgraph/cherry-pick-parent-invalid",
                format!(
                    "commit {} is not an immediate parent of {}",
                    parent.text, picked.id
                ),
                parent.span,
            ));
        }
        if picked.kind == CommitKind::Merge && node.parent.is_none() {
            return Some((
                "gitgraph/cherry-pick-parent-required",
                format!(
                    "cherry-pick of merge commit {} requires a parent",
                    picked.id
                ),
                id_span,
            ));
        }
        if picked.branch == self.current {
            return Some((
                "gitgraph/cherry-pick-current-branch",
                format!("commit {} is already on the current branch", picked.id),
                id_span,
            ));
        }
        if !self.heads[self.current].set {
            return Some((
                "gitgraph/cherry-pick-current-empty",
                format!(
                    "current branch {} has no commits for cherry-pick",
                    self.branch_name(self.current)
                ),
                node.keyword,
            ));
        }
        None
    }

    fn pick_unknown(&mut self, node: &CherryPicking) {
        let mut message = "cherry-pick requires an existing source commit".to_owned();
        let mut span = node.keyword;
        if let Some(id) = &node.id {
            message = format!("{message} {}", id.text);
            span = id.span;
        }
        self.issue("gitgraph/cherry-pick-source-unknown", message, span);
    }
}

fn pick_tag(picked: &Commit, parent: Option<&Value>) -> String {
    let mut tag = format!("cherry-pick:{}", picked.id);
    if let Some(parent) = parent
        && picked.kind == CommitKind::Merge
    {
        tag.push_str(&format!("|parent:{}", parent.text));
    }
    tag
}

#[cfg(test)]
mod tests;
