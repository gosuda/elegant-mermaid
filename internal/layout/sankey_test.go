package layout

import (
	"os"
	"path/filepath"
	"testing"

	"github.com/stretchr/testify/require"

	chartlayout "github.com/gosuda/elegant-mermaid/internal/layout/chart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func sankeyCorpus(tb testing.TB) []string {
	tb.Helper()
	paths, err := filepath.Glob(filepath.Join("..", "..", "corpus", "sankey", "*", "*.mmd"))
	require.NoError(tb, err)
	require.NotEmpty(tb, paths)
	return paths
}

func assertSankeyInputCarriesThePayload(t *testing.T, source string) {
	t.Helper()
	d := ParseDiagram([]byte(source))
	if len(d.Diagnostics) != 0 {
		return
	}
	in, err := d.Input(scene.ProfileVector, scene.Options{})
	require.NoError(t, err)
	want := sankeyPayload(d.sankey)
	got := sankeyFromInput(in)
	require.Len(t, got.Sankey.Nodes, len(want.Sankey.Nodes))
	for i, n := range want.Sankey.Nodes {
		require.Equal(t, n.Label, got.Sankey.Nodes[i].Label)
	}
	require.Equal(t, want.Sankey.Links, got.Sankey.Links)
	for _, entry := range want.Config {
		require.Contains(t, got.Config, entry)
	}
}

func TestSankeyInputCarriesTheWholePayload(t *testing.T) {
	for _, source := range []string{
		"sankey\na,b,1\n",
		"sankey\na,b,1.5\na,c,2\nb,c,0.25\n",
		"sankey\n\"x,y\",b,3\nb,\"say \"\"hi\"\"\",3\n",
		"---\nconfig:\n  sankey:\n    width: 400\n    height: 300\n    showValues: false\n    nodeAlignment: left\n---\nsankey\na,b,1\n",
		"sankey\na,b,abc\nb,c,-3\n",
	} {
		assertSankeyInputCarriesThePayload(t, source)
	}
}

func TestSankeyCorpusInputsCarryTheirPayloads(t *testing.T) {
	for _, path := range sankeyCorpus(t) {
		data, err := os.ReadFile(path)
		require.NoError(t, err)
		assertSankeyInputCarriesThePayload(t, string(data))
	}
}

func TestSankeyModelDumpCarriesTheLinkRegions(t *testing.T) {
	d := ParseDiagram([]byte("sankey\na,b,1.5\nb,c,2\n"))
	in, err := d.Input(scene.ProfileVector, scene.Options{})
	require.NoError(t, err)
	require.Len(t, in.RegionSets, 1)
	require.Equal(t, []int{0, 3000, 0, 4000}, in.RegionSets[0].Regions)
	require.Equal(t, chartlayout.SankeyLinkID(1), in.Routes[1].ID)
	require.Equal(t, chartlayout.SankeyNodeID(2), in.Routes[1].To)
}

func TestSankeyIgnoresTheCellProfile(t *testing.T) {
	d := ParseDiagram([]byte("sankey\na,b,1\nb,c,1\n"))
	vector, err := d.Input(scene.ProfileVector, scene.Options{})
	require.NoError(t, err)
	cell, err := d.Input(scene.ProfileCell, scene.Options{})
	require.NoError(t, err)
	require.Equal(t, scene.ProfileVector, cell.Profile)
	require.Equal(t, vector, cell)
	s, _, err := Layout(cell)
	require.NoError(t, err)
	require.Equal(t, scene.ProfileVector, s.Options.Profile)
}

func assertSankeyLaysOutValid(t *testing.T, d *Diagram) {
	t.Helper()
	in, err := d.Input(scene.ProfileVector, scene.Options{})
	if err != nil {
		return
	}
	s, _, err := Layout(in)
	if err != nil {
		return
	}
	clause, failed, err := s.Validate()
	if err != nil || failed {
		t.Fatalf("%v %v", clause, err)
	}
}

func FuzzSankeyLayout(f *testing.F) {
	for _, path := range sankeyCorpus(f) {
		data, err := os.ReadFile(path)
		require.NoError(f, err)
		f.Add(data)
	}
	f.Add([]byte("sankey\na,b,1\n"))
	f.Fuzz(func(t *testing.T, data []byte) {
		d := ParseDiagram(data)
		if d.Kind != sankeyKind || len(d.Diagnostics) != 0 {
			return
		}
		assertSankeyLaysOutValid(t, d)
	})
}
