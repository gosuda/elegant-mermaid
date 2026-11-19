package layout

import (
	"bytes"
	"os"
	"path/filepath"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func wardleyDiagram(t *testing.T, source string) *Diagram {
	t.Helper()
	d := ParseDiagram([]byte(source))
	require.Empty(t, d.Diagnostics)
	return d
}

func TestWardleyInputCarriesThePayloadForEveryCorpusFile(t *testing.T) {
	paths, err := filepath.Glob(filepath.Join("..", "..", "corpus", "wardley", "*", "*.mmd"))
	require.NoError(t, err)
	require.NotEmpty(t, paths)
	for _, path := range paths {
		data, err := os.ReadFile(path)
		require.NoError(t, err)
		d := ParseDiagram(data)
		if len(d.Diagnostics) != 0 {
			continue
		}
		for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
			in, err := d.Input(profile, scene.Options{})
			require.NoError(t, err)
			got, err := wardleyFromInput(in)
			require.NoError(t, err)
			require.Equal(t, wardleyPayload(d.wardley), got, path)
		}
	}
}

func TestWardleyDefaultsTheFourStagesWhenEvolutionIsAbsent(t *testing.T) {
	d := wardleyDiagram(t, "wardley-beta\ncomponent A [0.5, 0.5]\n")
	require.Equal(t, defaultWardleyStages, wardleyPayload(d.wardley).Stages)
	require.Empty(t, wardleyPayload(d.wardley).Boundaries)
}

func TestWardleyKeepsOnlyResolvedLinksThatAreNotPipelineSpokes(t *testing.T) {
	d := wardleyDiagram(t, "wardley-beta\ncomponent Kettle [0.5, 0.5]\ncomponent Pot [0.2, 0.2]\npipeline Kettle {\ncomponent Fire [0.3]\ncomponent Gas [0.6]\n}\nFire -> Kettle\nKettle -> Gas\nPot -> Missing\nPot -> Fire\n")
	w := wardleyPayload(d.wardley)
	require.Len(t, w.Links, 1)
	require.Equal(t, d.wardley.NodeIndex("Pot"), w.Links[0].From)
	require.Equal(t, d.wardley.NodeIndex("Kettle_Fire"), w.Links[0].To)
	require.Len(t, w.Pipelines, 1)
	require.Equal(t, d.wardley.NodeIndex("Kettle"), w.Pipelines[0].Parent)
}

func TestWardleyModelDumpCarriesTheRegionSets(t *testing.T) {
	d := wardleyDiagram(t, "wardley-beta\ncomponent A [0.5, 0.25] (buy)\n")
	in, err := d.Input(scene.ProfileVector, scene.Options{})
	require.NoError(t, err)
	var out bytes.Buffer
	require.NoError(t, WriteModelDump(&out, in))
	require.Contains(t, out.String(), "\"regions\":[[0,0,4,0],\n[0,1,0,2,25000,50000,0,0]]")
	require.Contains(t, out.String(), "\"kind\":\"wardley\"")
}

func TestWardleyLayoutAcceptsAnInputWithoutRegions(t *testing.T) {
	in := Input{Kind: wardleyKind, Options: scene.DefaultOptions()}
	s, _, err := Layout(in)
	require.NoError(t, err)
	require.Equal(t, "plot", s.Boxes[0].ID)
}
