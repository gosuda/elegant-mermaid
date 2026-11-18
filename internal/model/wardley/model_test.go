package wardley

import (
	"os"
	"path/filepath"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/wardley"
)

func resolve(src string) (*Model, []diag.Diagnostic) {
	prep := syntax.Preprocess([]byte(src))
	ast, parsed := syn.Parse([]byte(src), prep.Removed)
	if len(parsed) > 0 {
		panic(parsed[0].Message)
	}
	return Resolve([]byte(src), ast)
}

func messages(ds []diag.Diagnostic) []string {
	out := make([]string, len(ds))
	for i, d := range ds {
		out[i] = d.Code + ": " + d.Message
	}
	return out
}

func TestCorpusResolvesWithoutDiagnostics(t *testing.T) {
	paths, err := filepath.Glob(filepath.Join("..", "..", "..", "corpus", "wardley", "*", "*.mmd"))
	require.NoError(t, err)
	require.NotEmpty(t, paths)
	for _, path := range paths {
		src, err := os.ReadFile(path)
		require.NoError(t, err)
		_, ds := resolve(string(src))
		require.Empty(t, messages(ds), path)
	}
}

func TestCoordinatesAreNormalisedThousandths(t *testing.T) {
	for _, tc := range []struct {
		value string
		want  int64
	}{
		{"0.0", 0}, {"0.5", 50000}, {"0.95", 95000}, {"1.0", 100000}, {"0.123456", 12346}, {"0.999999", 100000},
		{"1.5", 1500}, {"12.5", 12500}, {"99.9996", 100000}, {"100.0", 100000}, {"00100.000", 100000},
	} {
		m, ds := resolve("wardley-beta\ncomponent A [" + tc.value + ", " + tc.value + "]\n")
		require.Empty(t, messages(ds), tc.value)
		require.Equal(t, tc.want, m.Nodes[0].X, tc.value)
		require.Equal(t, tc.want, m.Nodes[0].Y, tc.value)
	}
}

func TestCoordinateOutOfRange(t *testing.T) {
	_, ds := resolve("wardley-beta\ncomponent A [100.5, 0.5]\nanchor B [0.5, 250.25]\n")
	require.Equal(t, []string{
		`wardley/coordinate-out-of-range: Anchor "B" evolution must be between 0-1 (decimal) or 0-100 (percentage). Received: 250.25`,
		`wardley/coordinate-out-of-range: Component "A" visibility must be between 0-1 (decimal) or 0-100 (percentage). Received: 100.5`,
	}, messages(ds))
	_, ds = resolve("wardley-beta\ncomponent A [100.0001, 0.5]\n")
	require.Len(t, ds, 1)
}

func TestVisibilityIsYAndEvolutionIsX(t *testing.T) {
	m, ds := resolve("wardley-beta\ncomponent A [0.2, 0.7]\nnote \"n\" [0.3, 0.6]\nannotations [0.1, 0.9]\nannotation 4,[0.4, 0.8] \"t\"\naccelerator F [0.5, 0.55]\ndeaccelerator G [0.45, 0.35]\n")
	require.Empty(t, messages(ds))
	require.Equal(t, [2]int64{70000, 20000}, [2]int64{m.Nodes[0].X, m.Nodes[0].Y})
	require.Equal(t, Note{Text: "n", X: 60000, Y: 30000}, m.Notes[0])
	require.Equal(t, Point{X: 90000, Y: 10000}, *m.Box)
	require.Equal(t, Annotation{Number: 4, X: 80000, Y: 40000, Text: "t"}, m.Annotations[0])
	require.Equal(t, Force{Name: "F", X: 55000, Y: 50000}, m.Accelerators[0])
	require.Equal(t, Force{Name: "G", X: 35000, Y: 45000}, m.Deaccelerators[0])
}

func TestFirstAnnotationsBoxWins(t *testing.T) {
	m, _ := resolve("wardley-beta\nannotations [0.1, 0.9]\nannotations [0.3, 0.4]\n")
	require.Equal(t, Point{X: 90000, Y: 10000}, *m.Box)
}

func TestLaterDeclarationReplacesButKeepsPositionAndLabelOffset(t *testing.T) {
	m, ds := resolve("wardley-beta\ncomponent A [0.1, 0.2] label [-5, 6] (build) (inertia)\ncomponent B [0.3, 0.3]\ncomponent A [0.5, 0.6]\n")
	require.Empty(t, messages(ds))
	require.Len(t, m.Nodes, 2)
	a := m.Nodes[0]
	require.Equal(t, "A", a.ID)
	require.Equal(t, [2]int64{60000, 50000}, [2]int64{a.X, a.Y})
	require.True(t, a.HasOffset)
	require.Equal(t, [2]int64{-5, 6}, [2]int64{a.OffsetX, a.OffsetY})
	require.Equal(t, StrategyNone, a.Strategy)
	require.False(t, a.Inertia)
	m, _ = resolve("wardley-beta\nanchor A [0.1, 0.2]\ncomponent A [0.5, 0.6]\n")
	require.False(t, m.Nodes[0].Anchor)
}

func TestPipelineInheritsVisibilityAndKeepsMembers(t *testing.T) {
	m, ds := resolve("wardley-beta\ncomponent K [0.45, 0.57]\npipeline K {\n  component Fire [0.35] label [-60, 35]\n  component Gas [0.53]\n}\nK -> Fire\nFire -> K\n")
	require.Empty(t, messages(ds))
	require.Len(t, m.Nodes, 3)
	require.True(t, m.Nodes[0].PipelineParent)
	fire := m.Nodes[1]
	require.Equal(t, "K_Fire", fire.ID)
	require.Equal(t, "Fire", fire.Name)
	require.Equal(t, [2]int64{35000, 45000}, [2]int64{fire.X, fire.Y})
	require.Equal(t, [2]int64{-60, 35}, [2]int64{fire.OffsetX, fire.OffsetY})
	require.Equal(t, []Pipeline{{Node: "K", Components: []string{"K_Fire", "K_Gas"}}}, m.Pipelines)
	require.Equal(t, "K_Fire", m.Links[0].Target)
	require.Equal(t, "K_Fire", m.Links[1].Source)
}

func TestRepeatedPipelineReplacesMembership(t *testing.T) {
	m, _ := resolve("wardley-beta\ncomponent K [0.45, 0.57]\npipeline K {\n component A [0.1]\n}\npipeline K {\n component B [0.2]\n}\n")
	require.Equal(t, []Pipeline{{Node: "K", Components: []string{"K_B"}}}, m.Pipelines)
	require.Len(t, m.Nodes, 3)
}

func TestPipelineParentMustExist(t *testing.T) {
	_, ds := resolve("wardley-beta\npipeline Nope {\n component A [0.1]\n}\n")
	require.Equal(t, []string{`wardley/pipeline-parent-unknown: Pipeline "Nope" must reference an existing component with coordinates.`}, messages(ds))
}

func TestLinkFlowsLabelsAndDashes(t *testing.T) {
	m, ds := resolve("wardley-beta\ncomponent A [0.1, 0.1]\ncomponent B [0.2, 0.2]\nA +> B; first\nA +<> B\nA +'q'< B; ignored\nA +''> B; dropped\nA -.-> B +<\nA --> B\nA > B\nA -> Ghost\n")
	require.Empty(t, messages(ds))
	var got []Link
	for _, l := range m.Links {
		got = append(got, Link{Source: l.Source, Target: l.Target, Dashed: l.Dashed, Label: l.Label, Flow: l.Flow})
	}
	require.Equal(t, []Link{
		{Source: "A", Target: "B", Flow: FlowForward, Label: "first"},
		{Source: "A", Target: "B", Flow: FlowBidirectional},
		{Source: "A", Target: "B", Flow: FlowBackward, Label: "q"},
		{Source: "A", Target: "B", Flow: FlowForward},
		{Source: "A", Target: "B", Dashed: true, Flow: FlowBackward},
		{Source: "A", Target: "B"},
		{Source: "A", Target: "B"},
		{Source: "A", Target: "Ghost"},
	}, got)
}

func TestEvolveNeedsKnownNodeAndReplacesTrend(t *testing.T) {
	m, ds := resolve("wardley-beta\ncomponent A [0.4, 0.2]\ncomponent B [0.1, 0.1]\nevolve A 0.5\nevolve B 0.6\nevolve A 0.7\nevolve Ghost 999.5\n")
	require.Empty(t, messages(ds))
	require.Equal(t, []Trend{{Node: "A", TargetX: 70000, TargetY: 40000}, {Node: "B", TargetX: 60000, TargetY: 10000}}, m.Trends)
	_, ds = resolve("wardley-beta\ncomponent A [0.4, 0.2]\nevolve A 150.5\n")
	require.Equal(t, []string{`wardley/coordinate-out-of-range: Evolve target for "A" must be between 0-1 (decimal) or 0-100 (percentage). Received: 150.5`}, messages(ds))
}

func TestEvolutionStagesAndBoundaries(t *testing.T) {
	m, _ := resolve("wardley-beta\nevolution Genesis@0.25 -> Custom / Concept -> Product@0.8125\n")
	require.Equal(t, []string{"Genesis", "Custom / Concept", "Product"}, m.Stages)
	require.Equal(t, []int64{250, 813}, m.Boundaries)
	m, _ = resolve("wardley-beta\nevolution A -> B\nevolution C -> D -> E\n")
	require.Equal(t, []string{"C", "D", "E"}, m.Stages)
	require.Empty(t, m.Boundaries)
}

func TestSizeAndConfig(t *testing.T) {
	m, _ := resolve("wardley-beta\nsize [1100, 800]\n")
	require.Equal(t, []ConfigEntry{{"height", 800}, {"width", 1100}}, m.Config)
	m, _ = resolve("---\nconfig:\n  wardley-beta:\n    width: 700\n    padding: 20\n    nodeRadius: 9\n---\nwardley-beta\nsize [1100, 0]\n")
	require.Equal(t, []ConfigEntry{{"padding", 20}, {"width", 1100}}, m.Config)
	m, _ = resolve("%%{init: {\"wardley-beta\": {\"width\": 90000, \"height\": 400}}}%%\nwardley-beta\n")
	require.Equal(t, []ConfigEntry{{"height", 400}}, m.Config)
}

func TestTitleAndAccessibility(t *testing.T) {
	m, _ := resolve("---\ntitle: Front\n---\nwardley-beta\naccTitle: T\naccDescr: D\n")
	require.Equal(t, "Front", m.Title)
	require.Equal(t, "T", m.AccTitle)
	require.Equal(t, "D", m.AccDescr)
	m, _ = resolve("---\ntitle: Front\n---\nwardley-beta\ntitle One\ntitle Two &amp; #35;x\n")
	require.Equal(t, "Two &amp; #x", m.Title)
	m, _ = resolve("---\ntitle: Front\n---\nwardley-beta\ntitle One\ntitle\n")
	require.Equal(t, "Front", m.Title)
}

func TestEntitiesAreDecodedInDisplayTextOnly(t *testing.T) {
	m, _ := resolve("wardley-beta\ncomponent \"a #35; b\" [0.1, 0.1]\n\"a #35; b\" -> \"a #35; b\"\n")
	require.Equal(t, "a #35; b", m.Nodes[0].ID)
	require.Equal(t, "a # b", m.Nodes[0].Label)
	require.Len(t, m.Links, 1)
}
