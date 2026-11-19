package gitgraph

import (
	"slices"
	"strconv"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/gitgraph"
)

func (r *resolver) branchName(index int) string { return r.model.Branches[index].Name }

func (r *resolver) headID() (string, bool) {
	current := r.heads[r.current]
	return current.id, current.set
}

func (r *resolver) parentsOfHead() []string {
	if id, ok := r.headID(); ok {
		return []string{id}
	}
	return nil
}

func (r *resolver) newCommit(kind CommitKind, span source.Span) Commit {
	c := Commit{Seq: r.seq, Branch: r.current, Kind: kind, Span: span, Parents: r.parentsOfHead()}
	r.seq++
	return c
}

func (r *resolver) identify(c *Commit, explicit *syn.Value, keyword source.Span) {
	if explicit != nil && explicit.Text != "" {
		c.ID = explicit.Text
		r.record(*c, explicit.Span)
		return
	}
	c.ID = r.branchName(c.Branch) + "-" + strconv.Itoa(c.Seq)
	r.record(*c, keyword)
}

func (r *resolver) record(c Commit, idSpan source.Span) {
	r.model.CommitHistory = append(r.model.CommitHistory, c)
	if at, duplicate := r.commits[c.ID]; duplicate {
		d := syn.Diagnostic("gitgraph/duplicate-commit-id", "commit id "+c.ID+" already exists", idSpan)
		d.Severity = diag.SeverityWarning
		r.diags = append(r.diags, d)
		r.model.Commits[at] = c
	} else {
		r.commits[c.ID] = len(r.model.Commits)
		r.model.Commits = append(r.model.Commits, c)
	}
	r.heads[r.current] = head{id: c.ID, set: true}
}

func (r *resolver) commit(span source.Span, node *syn.Commit) {
	c := r.newCommit(KindCommit, span)
	c.Type = commitType(node.Type)
	c.Tags = values(node.Tags)
	if node.Message != nil {
		c.Message = node.Message.Text
	}
	r.identify(&c, node.ID, node.Keyword)
}

func (r *resolver) branch(node *syn.Branch) {
	name := node.Name
	if _, exists := r.names[name.Text]; exists {
		r.issue("gitgraph/branch-already-exists", "branch "+name.Text+" already exists", name.Span)
		return
	}
	branch := Branch{Name: name.Text, Span: name.Span}
	if node.Order != nil {
		branch.Order, branch.HasOrder = node.Order.Value, true
	}
	copied := r.heads[r.current]
	r.names[name.Text] = len(r.model.Branches)
	r.model.Branches = append(r.model.Branches, branch)
	r.heads = append(r.heads, copied)
	r.current = len(r.model.Branches) - 1
}

func (r *resolver) checkout(node *syn.Checkout) {
	index, exists := r.names[node.Branch.Text]
	if !exists {
		r.issue("gitgraph/unknown-branch", "branch "+node.Branch.Text+" does not exist", node.Branch.Span)
		return
	}
	r.current = index
}

func (r *resolver) merge(span source.Span, node *syn.Merge) {
	other, ok := r.mergeTarget(node)
	if !ok {
		return
	}
	currentID, _ := r.headID()
	c := r.newCommit(KindMerge, span)
	c.Parents = []string{currentID, r.heads[other].id}
	c.Type = commitType(node.Type)
	c.Tags = values(node.Tags)
	r.identify(&c, node.ID, node.Keyword)
}

func (r *resolver) selfMerge(other int, known bool) bool {
	if !known {
		return false
	}
	if r.current == other {
		return true
	}
	current, hasCurrent := r.headID()
	return hasCurrent && r.heads[other].set && r.model.Commits[r.commits[current]].Branch == other
}

func (r *resolver) mergeTarget(node *syn.Merge) (int, bool) {
	name := node.Branch
	other, known := r.names[name.Text]
	current, hasCurrent := r.headID()
	if r.selfMerge(other, known) {
		r.issue("gitgraph/merge-with-self", "cannot merge branch "+name.Text+" into itself", name.Span)
		return 0, false
	}
	switch {
	case !hasCurrent:
		r.issue("gitgraph/merge-current-empty", "current branch "+r.branchName(r.current)+" has no commits to merge", node.Keyword)
	case !known:
		r.issue("gitgraph/merge-unknown-branch", "merge branch "+name.Text+" does not exist", name.Span)
	case !r.heads[other].set:
		r.issue("gitgraph/merge-branch-empty", "merge branch "+name.Text+" has no commits", name.Span)
	case r.heads[other].id == current:
		r.issue("gitgraph/merge-same-head", "branches have the same head", name.Span)
	case r.duplicateMergeID(node):
		r.issue("gitgraph/merge-duplicate-commit-id", "merge commit id "+node.ID.Text+" already exists", node.ID.Span)
	default:
		return other, true
	}
	return 0, false
}

func (r *resolver) duplicateMergeID(node *syn.Merge) bool {
	if node.ID == nil || node.ID.Text == "" {
		return false
	}
	_, duplicate := r.commits[node.ID.Text]
	return duplicate
}

func (r *resolver) cherryPick(span source.Span, node *syn.CherryPicking) {
	picked, ok := r.pickSource(node)
	if !ok {
		return
	}
	c := r.newCommit(KindCherryPick, span)
	c.Pick = picked.ID
	c.Tags = values(node.Tags)
	if len(c.Tags) == 0 {
		c.Tags = []string{pickTag(picked, node.Parent)}
	}
	r.identify(&c, nil, node.Keyword)
}

func pickTag(picked Commit, parent *syn.Value) string {
	tag := "cherry-pick:" + picked.ID
	if picked.Kind == KindMerge && parent != nil {
		tag += "|parent:" + parent.Text
	}
	return tag
}

func (r *resolver) pickSource(node *syn.CherryPicking) (Commit, bool) {
	at, known := 0, false
	if node.ID != nil {
		at, known = r.commits[node.ID.Text]
	}
	if !known {
		r.pickUnknown(node)
		return Commit{}, false
	}
	picked := r.model.Commits[at]
	switch {
	case node.Parent != nil && !slices.Contains(picked.Parents, node.Parent.Text):
		r.issue("gitgraph/cherry-pick-parent-invalid", "commit "+node.Parent.Text+" is not an immediate parent of "+picked.ID, node.Parent.Span)
	case picked.Kind == KindMerge && node.Parent == nil:
		r.issue("gitgraph/cherry-pick-parent-required", "cherry-pick of merge commit "+picked.ID+" requires a parent", node.ID.Span)
	case picked.Branch == r.current:
		r.issue("gitgraph/cherry-pick-current-branch", "commit "+picked.ID+" is already on the current branch", node.ID.Span)
	case !r.heads[r.current].set:
		r.issue("gitgraph/cherry-pick-current-empty", "current branch "+r.branchName(r.current)+" has no commits for cherry-pick", node.Keyword)
	default:
		return picked, true
	}
	return Commit{}, false
}

func (r *resolver) pickUnknown(node *syn.CherryPicking) {
	message, span := "cherry-pick requires an existing source commit", node.Keyword
	if node.ID != nil {
		message, span = message+" "+node.ID.Text, node.ID.Span
	}
	r.issue("gitgraph/cherry-pick-source-unknown", message, span)
}
