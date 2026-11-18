package gitgraph

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/gitgraph"
)

func resolve(src string) (*Model, []diag.Diagnostic) {
	prep := syntax.Preprocess([]byte(src))
	start, parsed := syn.Parse([]byte(src), prep.Removed)
	model, resolved := Resolve([]byte(src), start)
	return model, append(parsed, resolved...)
}

func ids(m *Model) []string {
	out := make([]string, len(m.Commits))
	for i, c := range m.Commits {
		out[i] = c.ID
	}
	return out
}

func messages(ds []diag.Diagnostic) []string {
	out := make([]string, len(ds))
	for i, d := range ds {
		out[i] = d.Severity.String() + " " + d.Code + ": " + d.Message
	}
	return out
}

func TestGeneratedIdsUseTheGlobalIndex(t *testing.T) {
	m, ds := resolve("gitGraph\ncommit\ncommit id: \"\"\nbranch dev\ncommit\ncheckout main\nmerge dev\ncommit id: \"x\"\nbranch other\ncherry-pick id: \"x\"\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"main-0", "main-1", "dev-2", "main-3", "x", "other-5"}, ids(m))
	require.Equal(t, KindMerge, m.Commits[3].Kind)
	require.Equal(t, []string{"main-1", "dev-2"}, m.Commits[3].Parents)
	require.Equal(t, KindCherryPick, m.Commits[5].Kind)
	require.Equal(t, "x", m.Commits[5].Pick)
}

func TestBranchCopiesTheHeadAndCheckoutRestoresIt(t *testing.T) {
	m, ds := resolve("gitGraph\ncommit id: \"a\"\nbranch dev\ncommit id: \"b\"\ncheckout main\ncommit id: \"c\"\ncheckout dev\ncommit id: \"d\"\nbranch empty\ncheckout main\nbranch fresh\n")
	require.Empty(t, ds)
	require.Equal(t, [][]string{nil, {"a"}, {"a"}, {"b"}}, [][]string{m.Commits[0].Parents, m.Commits[1].Parents, m.Commits[2].Parents, m.Commits[3].Parents})
	require.Equal(t, []string{"main", "dev", "empty", "fresh"}, []string{m.Branches[0].Name, m.Branches[1].Name, m.Branches[2].Name, m.Branches[3].Name})
}

func TestBranchOrderKeepsAbsenceSeparateFromZero(t *testing.T) {
	m, ds := resolve("gitGraph\nbranch a\nbranch b order: 0\nbranch c order: 4\n")
	require.Empty(t, ds)
	require.False(t, m.Branches[1].HasOrder)
	require.True(t, m.Branches[2].HasOrder)
	require.Equal(t, int64(0), m.Branches[2].Order)
	require.Equal(t, int64(4), m.Branches[3].Order)
}

func TestBranchAndCheckoutErrors(t *testing.T) {
	m, ds := resolve("gitGraph\nbranch main\ncheckout nope\nbranch dev\nbranch dev\ncommit\n")
	require.Equal(t, []string{
		"error gitgraph/branch-already-exists: branch main already exists",
		"error gitgraph/unknown-branch: branch nope does not exist",
		"error gitgraph/branch-already-exists: branch dev already exists",
	}, messages(ds))
	require.Equal(t, "dev-0", m.Commits[0].ID)
	require.Equal(t, 1, m.Commits[0].Branch)
}

func TestMergeValidationOrder(t *testing.T) {
	for _, tc := range []struct {
		src, want string
	}{
		{"gitGraph\ncommit\nmerge main", "error gitgraph/merge-with-self: cannot merge branch main into itself"},
		{"gitGraph\ncommit\nbranch dev\ncommit\ncheckout main\nbranch x\nmerge main", "error gitgraph/merge-with-self: cannot merge branch main into itself"},
		{"gitGraph\nmerge dev", "error gitgraph/merge-current-empty: current branch main has no commits to merge"},
		{"gitGraph\ncommit\nmerge dev", "error gitgraph/merge-unknown-branch: merge branch dev does not exist"},
		{"gitGraph\nbranch empty\ncheckout main\ncommit\nmerge empty", "error gitgraph/merge-branch-empty: merge branch empty has no commits"},
		{"gitGraph\ncommit\nbranch dev\ncheckout main\nmerge dev", "error gitgraph/merge-same-head: branches have the same head"},
		{"gitGraph\ncommit id: \"a\"\nbranch dev\ncommit\ncheckout main\ncommit\nmerge dev id: \"a\"", "error gitgraph/merge-duplicate-commit-id: merge commit id a already exists"},
	} {
		m, ds := resolve(tc.src)
		require.Equal(t, []string{tc.want}, messages(ds), tc.src)
		for _, c := range m.Commits {
			require.NotEqual(t, KindMerge, c.Kind, tc.src)
		}
	}
}

func TestRejectedStatementsLeaveTheSequenceUntouched(t *testing.T) {
	m, ds := resolve("gitGraph\ncommit\nmerge main\ncommit\n")
	require.Len(t, ds, 1)
	require.Equal(t, []string{"main-0", "main-1"}, ids(m))
}

func TestCherryPickValidationOrderAndTags(t *testing.T) {
	prefix := "gitGraph\ncommit id: \"a\"\nbranch dev\ncommit id: \"b\"\ncheckout main\ncommit id: \"c\"\nmerge dev id: \"m\"\nbranch topic\n"
	for _, tc := range []struct {
		pick, want string
	}{
		{"cherry-pick", "error gitgraph/cherry-pick-source-unknown: cherry-pick requires an existing source commit"},
		{"cherry-pick id: \"zz\"", "error gitgraph/cherry-pick-source-unknown: cherry-pick requires an existing source commit zz"},
		{"cherry-pick id: \"b\" parent: \"zz\"", "error gitgraph/cherry-pick-parent-invalid: commit zz is not an immediate parent of b"},
		{"cherry-pick id: \"m\"", "error gitgraph/cherry-pick-parent-required: cherry-pick of merge commit m requires a parent"},
		{"cherry-pick id: \"c\" parent: \"m\"", "error gitgraph/cherry-pick-parent-invalid: commit m is not an immediate parent of c"},
	} {
		_, ds := resolve(prefix + tc.pick + "\n")
		require.Equal(t, []string{tc.want}, messages(ds), tc.pick)
	}
	_, ds := resolve("gitGraph\ncommit id: \"a\"\ncherry-pick id: \"a\"\n")
	require.Equal(t, []string{"error gitgraph/cherry-pick-current-branch: commit a is already on the current branch"}, messages(ds))
	_, ds = resolve("gitGraph\ncommit id: \"a\"\nbranch dev\ncheckout main\nbranch empty\ncherry-pick id: \"a\"\ncheckout dev\n")
	require.Empty(t, ds)
	m, ds := resolve(prefix + "cherry-pick id: \"m\" parent: \"c\"\ncherry-pick id: \"b\" tag: \"mine\"\n")
	require.Empty(t, ds)
	last := m.Commits[len(m.Commits)-2:]
	require.Equal(t, []string{"cherry-pick:m|parent:c"}, last[0].Tags)
	require.Equal(t, []string{"mine"}, last[1].Tags)
	require.Equal(t, []string{"m"}, last[0].Parents)
	require.Equal(t, "topic", m.Branches[last[0].Branch].Name)
}

func TestCherryPickIntoEmptyBranchIsRejected(t *testing.T) {
	_, ds := resolve("gitGraph\nbranch dev\ncommit id: \"z\"\ncheckout main\ncherry-pick id: \"z\"\n")
	require.Equal(t, []string{"error gitgraph/cherry-pick-current-empty: current branch main has no commits for cherry-pick"}, messages(ds))
}

func TestDuplicateCommitIdReplacesTheRecordInPlace(t *testing.T) {
	m, ds := resolve("gitGraph\ncommit id: \"a\" tag: \"first\"\ncommit id: \"b\"\ncommit id: \"a\" type: REVERSE\ncommit\n")
	require.Equal(t, []string{"warning gitgraph/duplicate-commit-id: commit id a already exists"}, messages(ds))
	require.Len(t, m.CommitHistory, 4)
	require.Equal(t, []string{"a", "b", "main-3"}, ids(m))
	require.Equal(t, 2, m.Commits[0].Seq)
	require.Equal(t, TypeReverse, m.Commits[0].Type)
	require.Empty(t, m.Commits[0].Tags)
	require.Equal(t, []string{"a"}, m.Commits[2].Parents)
}

func TestGeneratedIdCollisionRetainsTheKeyword(t *testing.T) {
	_, ds := resolve("gitGraph\ncommit id: \"main-1\"\ncommit\n")
	require.Equal(t, []string{"warning gitgraph/duplicate-commit-id: commit id main-1 already exists"}, messages(ds))
	require.Equal(t, 29, ds[0].Span.Start)
}

func TestMainBranchNameAndOrderConfig(t *testing.T) {
	m, ds := resolve("---\nconfig:\n  gitGraph:\n    mainBranchName: 'trunk'\n    mainBranchOrder: 3\n---\ngitGraph\ncommit\ncheckout trunk\ncommit\nbranch main\ncommit\n")
	require.Empty(t, ds)
	require.Equal(t, "trunk", m.Branches[0].Name)
	require.True(t, m.Branches[0].HasOrder)
	require.Equal(t, int64(3), m.Branches[0].Order)
	require.Equal(t, "main", m.Branches[1].Name)
	require.Equal(t, []string{"trunk-0", "trunk-1", "main-2"}, ids(m))
}

func TestMainBranchRenameRejectsTheDefaultName(t *testing.T) {
	_, ds := resolve("---\nconfig:\n  gitGraph:\n    mainBranchName: trunk\n---\ngitGraph\ncommit\ncheckout main\n")
	require.Equal(t, []string{"error gitgraph/unknown-branch: branch main does not exist"}, messages(ds))
}

func TestMainBranchInitDirectiveOverridesFrontmatter(t *testing.T) {
	m, ds := resolve("---\nconfig:\n  gitGraph:\n    mainBranchName: trunk\n    mainBranchOrder: 1\n---\n%%{init: {'gitGraph': {'mainBranchName': 'prod', 'mainBranchOrder': -2}}}%%\ngitGraph\ncommit\n")
	require.Empty(t, ds)
	require.Equal(t, "prod", m.Branches[0].Name)
	require.Equal(t, int64(-2), m.Branches[0].Order)
	require.Equal(t, "prod-0", m.Commits[0].ID)
}

func TestMainBranchConfigIgnoresUnusableValues(t *testing.T) {
	m, ds := resolve("---\nconfig:\n  gitGraph:\n    mainBranchName: 5\n    mainBranchOrder: 1.5\n---\ngitGraph\ncommit\n")
	require.Empty(t, ds)
	require.Equal(t, "main", m.Branches[0].Name)
	require.False(t, m.Branches[0].HasOrder)
	m, ds = resolve("---\nconfig:\n  gitGraph:\n    mainBranchName: ''\n---\ngitGraph\ncommit\n")
	require.Empty(t, ds)
	require.Equal(t, "main", m.Branches[0].Name)
}

func TestConfigKeysAndDirection(t *testing.T) {
	m, ds := resolve("---\nconfig:\n  gitGraph:\n    showBranches: false\n    rotateCommitLabel: true\n    parallelCommits: true\n---\n%%{init: {'gitGraph': {'showBranches': true, 'showCommitLabel': false}}}%%\ngitGraph BT:\ncommit\n")
	require.Empty(t, ds)
	require.Equal(t, "BT", m.Direction)
	require.Equal(t, []ConfigEntry{{"rotateCommitLabel", true}, {"showBranches", true}, {"showCommitLabel", false}}, m.Config)
	m, _ = resolve("gitGraph\ncommit\n")
	require.Equal(t, "LR", m.Direction)
	require.Empty(t, m.Config)
}

func TestMetadataLastOccurrenceWins(t *testing.T) {
	m, ds := resolve("gitGraph\ntitle one\ntitle two\naccTitle: a\naccDescr: d\naccTitle: b\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"two", "b", "d"}, []string{m.Title, m.AccTitle, m.AccDescr})
}
