package layout

import (
	"os"
	"path/filepath"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func radarCorpus(t testing.TB) [][]byte {
	t.Helper()
	paths, err := filepath.Glob(filepath.Join("..", "..", "corpus", "radar", "*", "*.mmd"))
	require.NoError(t, err)
	require.NotEmpty(t, paths)
	out := make([][]byte, len(paths))
	for i, path := range paths {
		out[i], err = os.ReadFile(path)
		require.NoError(t, err)
	}
	return out
}

func assertRadarInputCarriesThePayload(t *testing.T, source string) {
	t.Helper()
	d := ParseDiagram([]byte(source))
	if len(d.Diagnostics) != 0 {
		return
	}
	in, err := d.Input(scene.ProfileVector, scene.Options{})
	require.NoError(t, err)
	want := radarPayload(d.radar)
	got := radarFromInput(in)
	require.Equal(t, want.Title, got.Title, source)
	require.Equal(t, want.Radar, got.Radar, source)
	for _, entry := range want.Config {
		require.Contains(t, got.Config, entry, source)
	}
}

func TestRadarInputCarriesTheWholePayload(t *testing.T) {
	for _, source := range []string{
		"radar-beta\naxis A, B, C\ncurve c{1, 2, 3}\n",
		"radar-beta\ntitle T\naxis a[\"Alpha\"], b, c\ncurve x[\"X\"]{1, 2, 3}, y{3, 2, 1}\nmax 5\nmin 1\nticks 3\ngraticule polygon\nshowLegend false\n",
		"radar-beta\naxis A, B\ncurve k{B: 3, A: 1}\ncurve ragged{1}\n",
		"---\nconfig:\n  radar:\n    width: 400\n    curveTension: 0.5\n---\nradar-beta\naxis A, B, C\ncurve c{1, 2, 3}\n",
	} {
		assertRadarInputCarriesThePayload(t, source)
	}
}

func TestRadarCorpusInputsCarryTheirPayloads(t *testing.T) {
	for _, data := range radarCorpus(t) {
		assertRadarInputCarriesThePayload(t, string(data))
	}
}

func TestRadarModelDumpCarriesTheRegions(t *testing.T) {
	d := ParseDiagram([]byte("radar-beta\naxis A, B\ncurve c{1, 2}\nmax 4\nticks 3\ngraticule polygon\n"))
	require.Empty(t, d.Diagnostics)
	in, err := d.Input(scene.ProfileVector, scene.Options{})
	require.NoError(t, err)
	require.Len(t, in.RegionSets, 2)
	require.Equal(t, []int{radarTagOptions, 1, 1, 3000, 1, 8000, 0}, in.RegionSets[0].Regions)
	require.Equal(t, []int{radarTagCurve, 2, 2000, 4000}, in.RegionSets[1].Regions)
}

func TestRadarEveryProfileGivesTheVectorInput(t *testing.T) {
	d := ParseDiagram([]byte("radar-beta\naxis A, B, C\ncurve c{1, 2, 3}\n"))
	require.Empty(t, d.Diagnostics)
	cell, err := d.Input(scene.ProfileCell, scene.Options{})
	require.NoError(t, err)
	vector, err := d.Input(scene.ProfileVector, scene.Options{})
	require.NoError(t, err)
	require.Equal(t, scene.ProfileVector, cell.Profile)
	require.Equal(t, scene.ProfileVector, cell.Options.Profile)
	require.Equal(t, vector.RegionSets, cell.RegionSets)
}

func assertRadarLaysOutValid(t *testing.T, d *Diagram) {
	t.Helper()
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		in, err := d.Input(profile, scene.Options{})
		if err != nil {
			continue
		}
		s, _, err := Layout(in)
		if err != nil {
			continue
		}
		clause, failed, err := s.Validate()
		if err != nil || failed {
			t.Fatalf("%v: %v %v", profile, clause, err)
		}
	}
}

func TestRadarLayoutSatisfiesTheHardConstraints(t *testing.T) {
	for _, source := range []string{
		"radar-beta\naxis A, B, C\ncurve c{1, 2, 3}\n",
		"radar-beta\ntitle Skills\naxis m[\"Math\"], s[\"Sci\"], e[\"Eng\"], a[\"Art\"]\ncurve a{4, 3, 2, 1}, b{1, 2, 3, 4}\nmax 5\ngraticule polygon\n",
		"radar-beta\naxis A, B\ncurve c{1, 2}\nticks 0\nshowLegend false\n",
		"radar-beta\naxis A\ncurve c{3}\nmin 1\n",
		"radar-beta\ncurve c{1}\n",
	} {
		d := ParseDiagram([]byte(source))
		require.Empty(t, d.Diagnostics, source)
		in, err := d.Input(scene.ProfileVector, scene.Options{})
		require.NoError(t, err, source)
		s, _, err := Layout(in)
		require.NoError(t, err, source)
		clause, failed, err := s.Validate()
		require.NoError(t, err, source)
		require.False(t, failed, "%s: %v", source, clause)
	}
}

func TestRadarCorpusLayoutsAreValid(t *testing.T) {
	for _, data := range radarCorpus(t) {
		d := ParseDiagram(data)
		if len(d.Diagnostics) == 0 {
			assertRadarLaysOutValid(t, d)
		}
	}
}

func FuzzRadarLayout(f *testing.F) {
	for _, data := range radarCorpus(f) {
		f.Add(data)
	}
	f.Add([]byte("radar-beta\naxis A, B\ncurve c{1, 2}\n"))
	f.Fuzz(func(t *testing.T, data []byte) {
		d := ParseDiagram(data)
		if d.Kind != radarKind || len(d.Diagnostics) != 0 {
			return
		}
		assertRadarLaysOutValid(t, d)
	})
}
