package layout

import (
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/cells"
	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const gitgraphSample = "gitGraph\n" +
	"commit id: \"A\"\n" +
	"commit id: \"B\" tag: \"v1\" tag: \"rc\" type: HIGHLIGHT\n" +
	"branch develop order: 2\n" +
	"commit type: REVERSE\n" +
	"checkout main\n" +
	"commit\n" +
	"merge develop tag: \"m\" type: REVERSE\n" +
	"cherry-pick id: \"develop-2\"\n"

func gitgraphInput(t *testing.T, src string, profile scene.Profile) Input {
	t.Helper()
	d := ParseDiagram([]byte(src))
	require.Empty(t, errorsOf(d.Diagnostics))
	in, err := d.Input(profile, scene.Options{})
	require.NoError(t, err)
	return in
}

func errorsOf(ds []diag.Diagnostic) []diag.Diagnostic {
	var out []diag.Diagnostic
	for _, d := range ds {
		if d.Severity == diag.SeverityError {
			out = append(out, d)
		}
	}
	return out
}

func TestGitgraphInputEncodesTheModel(t *testing.T) {
	in := gitgraphInput(t, gitgraphSample, scene.ProfileVector)
	require.Equal(t, scene.DirectionLR, in.Direction)
	var boxes []string
	for _, b := range in.Boxes {
		boxes = append(boxes, b.ID+"|"+b.Role.String()+"|"+b.Shape+"|"+b.Parent)
	}
	require.Equal(t, []string{
		"lane0|group|branch|", "lane1|group|branch:2|",
		"A|node|commit|lane0", "B|node|highlight|lane0", "develop-2|node|reverse|lane1",
		"main-3|node|commit|lane0", "main-4|node|merge-reverse|lane0", "main-5|node|cherry-pick|lane0",
	}, boxes)
	var routes []string
	for _, r := range in.Routes {
		routes = append(routes, r.ID+"|"+r.From+">"+r.To+"|"+r.Line)
	}
	require.Equal(t, []string{
		"e0|A>B|normal", "e1|B>develop-2|normal", "e2|B>main-3|normal",
		"e3|main-3>main-4|normal", "e4|develop-2>main-4|normal",
		"e5|main-4>main-5|normal", "e6|develop-2>main-5|dotted",
	}, routes)
	var labels []string
	for _, l := range in.Labels {
		labels = append(labels, l.ID+"|"+l.Owner+"|"+l.Text+"|"+l.Role.String())
	}
	require.Equal(t, []string{
		"lane0.label|lane0|main|label", "lane1.label|lane1|develop|label",
		"A.label|A|A|body", "B.label|B|B|body", "B.tag0|B|v1|body", "B.tag1|B|rc|body",
		"develop-2.label|develop-2|develop-2|body", "main-3.label|main-3|main-3|body",
		"main-4.label|main-4|main-4|body", "main-4.tag0|main-4|m|body",
		"main-5.label|main-5|main-5|body", "main-5.tag0|main-5|cherry-pick:develop-2|body",
	}, labels)
}

func TestGitgraphIdsStayUnique(t *testing.T) {
	in := gitgraphInput(t, "gitGraph\ncommit id: \"lane0\"\ncommit id: \"e0\"\ncommit id: \"e0.label\"\ncommit id: \"lane0.label\"\n", scene.ProfileCell)
	seen := map[string]bool{}
	for _, id := range slices.Concat(boxIDs(in), routeIDs(in), labelIDs(in)) {
		require.False(t, seen[id], id)
		seen[id] = true
	}
}

func boxIDs(in Input) []string {
	var out []string
	for _, b := range in.Boxes {
		out = append(out, b.ID)
	}
	return out
}

func routeIDs(in Input) []string {
	var out []string
	for _, r := range in.Routes {
		out = append(out, r.ID)
	}
	return out
}

func labelIDs(in Input) []string {
	var out []string
	for _, l := range in.Labels {
		out = append(out, l.ID)
	}
	return out
}

func TestGitgraphConfigTogglesLabels(t *testing.T) {
	src := "%%{init: {'gitGraph': {'showBranches': false, 'showCommitLabel': false}}}%%\ngitGraph\ncommit id: \"A\" tag: \"t\"\n"
	in := gitgraphInput(t, src, scene.ProfileVector)
	require.Equal(t, []string{"A.tag0"}, labelIDs(in))
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		in.Profile = profile
		s, _, err := Layout(in)
		require.NoError(t, err)
		require.Len(t, s.Labels, 1)
		require.Equal(t, []string{"t"}, s.Labels[0].Lines)
		for _, group := range s.Groups {
			if group.Role == scene.GroupRoleGroup {
				require.Empty(t, group.Items)
			}
		}
	}
}

func TestGitgraphLayoutSatisfiesTheHardConstraints(t *testing.T) {
	for _, src := range []string{
		gitgraphSample,
		"gitGraph TB:\n" + strings.TrimPrefix(gitgraphSample, "gitGraph\n"),
		"gitGraph BT:\n" + strings.TrimPrefix(gitgraphSample, "gitGraph\n"),
		"gitGraph\n",
		"gitGraph\nbranch a\nbranch b order: 1\n",
		"gitGraph BT:\ncommit id: \"x\"\ncommit id: \"x\" tag: \"dup\"\n",
	} {
		for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
			s, _, err := Layout(gitgraphInput(t, src, profile))
			require.NoError(t, err, src)
			clause, failed, err := s.Validate()
			require.NoError(t, err, src)
			require.False(t, failed, "%s %v: %s", src, profile, clause)
		}
	}
}

func TestGitgraphCorpusLayoutsAreValid(t *testing.T) {
	paths, err := filepath.Glob(filepath.Join("..", "..", "corpus", "gitgraph", "*", "*.mmd"))
	require.NoError(t, err)
	require.NotEmpty(t, paths)
	for _, path := range paths {
		src, err := os.ReadFile(path)
		require.NoError(t, err)
		d := ParseDiagram(src)
		if len(errorsOf(d.Diagnostics)) > 0 {
			continue
		}
		for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
			in, err := d.Input(profile, scene.Options{})
			require.NoError(t, err, path)
			s, _, err := Layout(in)
			require.NoError(t, err, path)
			clause, failed, err := s.Validate()
			require.NoError(t, err, path)
			require.False(t, failed, "%s %v: %s", path, profile, clause)
		}
	}
}

func TestGitgraphRejectsForeignRouteEndpoints(t *testing.T) {
	in := Input{Kind: "gitgraph", Options: scene.DefaultOptions(), Boxes: []Box{{ID: "A", Exclusive: true}}, Routes: []Route{{ID: "e", From: "A", To: "nowhere"}}}
	_, _, err := Layout(in)
	require.ErrorIs(t, err, errGitgraphInput)
}

func TestGitgraphCellMarkersFollowCommitKinds(t *testing.T) {
	in := gitgraphInput(t, gitgraphSample, scene.ProfileCell)
	s, _, err := Layout(in)
	require.NoError(t, err)
	var symbols []string
	for _, group := range s.Groups {
		if group.Role != scene.GroupRoleNode {
			continue
		}
		for _, item := range group.Items {
			if symbol, ok := item.(*scene.SymbolRef); ok {
				symbols = append(symbols, symbol.Symbol)
			}
		}
	}
	require.Equal(t, []string{"disc", "diamond", "ring", "disc", "bullseye", "diamond-hollow"}, symbols)
}

func TestGitgraphCellLabelsAreNeverOverwritten(t *testing.T) {
	body := strings.TrimPrefix(gitgraphSample, "gitGraph\n")
	for _, header := range []string{"gitGraph\n", "gitGraph TB:\n", "gitGraph BT:\n"} {
		s, _, err := Layout(gitgraphInput(t, header+body, scene.ProfileCell))
		require.NoError(t, err, header)
		assertCellText(t, s, "main", "develop", "develop-2", "main-3", "main-4", "main-5", "cherry-pick:develop-2", "v1", "rc")
	}
}

const gitgraphDuplicateIDs = "commit id: \"alpha\"\n" +
	"commit id: \"bravo\"\n" +
	"branch dev\n" +
	"commit id: \"xray\"\n" +
	"commit id: \"yankee\"\n" +
	"checkout main\n" +
	"commit id: \"charlie\"\n" +
	"merge dev\n" +
	"commit id: \"yankee\"\n"

func TestGitgraphDuplicateIDsKeepCellLabelsApart(t *testing.T) {
	for _, header := range []string{"gitGraph\n", "gitGraph TB:\n", "gitGraph BT:\n"} {
		s, _, err := Layout(gitgraphInput(t, header+gitgraphDuplicateIDs, scene.ProfileCell))
		require.NoError(t, err, header)
		assertCellText(t, s, "alpha", "bravo", "xray", "yankee", "charlie")
	}
}

func TestGitgraphCorpusCellTextIsNeverOverwritten(t *testing.T) {
	paths, err := filepath.Glob(filepath.Join("..", "..", "corpus", "gitgraph", "*", "*.mmd"))
	require.NoError(t, err)
	require.NotEmpty(t, paths)
	for _, path := range paths {
		src, err := os.ReadFile(path)
		require.NoError(t, err)
		d := ParseDiagram(src)
		if len(errorsOf(d.Diagnostics)) > 0 {
			continue
		}
		in, err := d.Input(scene.ProfileCell, scene.Options{})
		require.NoError(t, err, path)
		s, _, err := Layout(in)
		require.NoError(t, err, path)
		res, err := cells.Render(s, cells.Options{})
		require.NoError(t, err, path)
		require.Zero(t, res.RefusedClusters, path)
	}
}
