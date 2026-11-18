package layout

import (
	"os"
	"path/filepath"
	"testing"

	"github.com/stretchr/testify/require"

	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func treemapCorpus(t testing.TB) [][]byte {
	t.Helper()
	paths, err := filepath.Glob(filepath.Join("..", "..", "corpus", "treemap", "*", "*.mmd"))
	require.NoError(t, err)
	require.NotEmpty(t, paths)
	out := make([][]byte, len(paths))
	for i, path := range paths {
		out[i], err = os.ReadFile(path)
		require.NoError(t, err)
	}
	return out
}

func requireSameTree(t *testing.T, want, got []*chartmodel.TreemapNode, source string) {
	t.Helper()
	require.Len(t, got, len(want), source)
	for i := range want {
		require.Equal(t, want[i].Name, got[i].Name, source)
		require.Equal(t, want[i].ValueText, got[i].ValueText, source)
		require.Equal(t, want[i].Index, got[i].Index, source)
		requireSameTree(t, want[i].Children, got[i].Children, source)
	}
}

func assertTreemapInputCarriesThePayload(t *testing.T, source string) {
	t.Helper()
	d := ParseDiagram([]byte(source))
	if len(d.Diagnostics) != 0 {
		return
	}
	in, err := d.Input(scene.ProfileVector, scene.Options{})
	require.NoError(t, err)
	want := treemapPayload(d.treemap, treemapFlat(d.treemap))
	got := treemapFromInput(in)
	require.Equal(t, want.Title, got.Title, source)
	requireSameTree(t, want.Treemap.Roots, got.Treemap.Roots, source)
	for _, entry := range want.Config {
		require.Contains(t, got.Config, entry, source)
	}
}

func TestTreemapInputCarriesTheWholePayload(t *testing.T) {
	for _, source := range []string{
		"treemap-beta\n\"A\"\n  \"B\": 1\n",
		"treemap-beta\ntitle T\n\"A\"\n  \"B\": 1,234.5\n  \"C\"\n    \"D\": 2\n\"E\"\n  \"F\": 3\n",
		"---\nconfig:\n  treemap:\n    nodeWidth: 50\n    padding: 4\n---\ntreemap-beta\n\"A\"\n  \"B\": 7654321\n  \"C\": 1000000000\n",
		"treemap-beta\n\"A\"\n  \"\": 5\n  \"B\": ...\n",
	} {
		assertTreemapInputCarriesThePayload(t, source)
	}
}

func TestTreemapCorpusInputsCarryTheirPayloads(t *testing.T) {
	for _, data := range treemapCorpus(t) {
		assertTreemapInputCarriesThePayload(t, string(data))
	}
}

func TestTreemapModelDumpCarriesTheLeafValues(t *testing.T) {
	d := ParseDiagram([]byte("treemap-beta\n\"A\"\n  \"B\": 3\n  \"C\"\n    \"D\": 4\n"))
	require.Empty(t, d.Diagnostics)
	in, err := d.Input(scene.ProfileVector, scene.Options{})
	require.NoError(t, err)
	require.Len(t, in.RegionSets, 1)
	require.Equal(t, []int{0, 3000, 0, 4000}, in.RegionSets[0].Regions)
}

func TestTreemapHugeLeafValuesAreScaledIntoTheModelDump(t *testing.T) {
	d := ParseDiagram([]byte("treemap-beta\n\"A\"\n  \"B\": 1000000000\n  \"C\": 7654321\n"))
	require.Empty(t, d.Diagnostics)
	in, err := d.Input(scene.ProfileVector, scene.Options{})
	require.NoError(t, err)
	regions := in.RegionSets[0].Regions
	require.LessOrEqual(t, regions[1]+regions[2], 1<<24)
	require.Greater(t, regions[1], regions[2])
	require.Positive(t, regions[2])
}

func TestTreemapEveryProfileKeepsItsOwnInput(t *testing.T) {
	d := ParseDiagram([]byte("treemap-beta\n\"A\"\n  \"B\": 1\n"))
	require.Empty(t, d.Diagnostics)
	cell, err := d.Input(scene.ProfileCell, scene.Options{})
	require.NoError(t, err)
	vector, err := d.Input(scene.ProfileVector, scene.Options{})
	require.NoError(t, err)
	require.Equal(t, scene.ProfileCell, cell.Profile)
	require.Equal(t, scene.ProfileVector, vector.Profile)
	require.Equal(t, vector.RegionSets, cell.RegionSets)
}

func TestTreemapLayoutOverTheLimitsFails(t *testing.T) {
	d := ParseDiagram([]byte("treemap-beta\n\"A\"\n  \"B\": 1\n  \"C\": 2\n"))
	require.Empty(t, d.Diagnostics)
	in, err := d.Input(scene.ProfileVector, scene.Options{Limits: scene.Limits{MaxNodes: 2}})
	require.NoError(t, err)
	_, _, err = Layout(in)
	require.Error(t, err)
	in, err = d.Input(scene.ProfileVector, scene.Options{Limits: scene.Limits{MaxTextBytes: 2}})
	require.NoError(t, err)
	_, _, err = Layout(in)
	require.Error(t, err)
}
