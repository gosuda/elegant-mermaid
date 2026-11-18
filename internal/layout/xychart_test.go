package layout

import (
	"os"
	"path/filepath"
	"testing"

	"github.com/stretchr/testify/require"

	chartlayout "github.com/gosuda/elegant-mermaid/internal/layout/chart"
	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func TestZigzagRoundTripsSignedValues(t *testing.T) {
	for _, v := range []int64{0, 1, -1, 2, -2, 2147483647, -2147483647, 1 << 40, -(1 << 40)} {
		require.Equal(t, v, unzigzag(zigzag(v)))
		require.GreaterOrEqual(t, zigzag(v), 0)
	}
}

func titledPayload(c *chartmodel.Chart) *chartmodel.Chart {
	for i := range c.XY.Plots {
		c.XY.Plots[i].Title = chartlayout.SeriesTitle(i, c.XY.Plots[i].Title)
	}
	return c
}

func assertInputCarriesThePayload(t *testing.T, source string) {
	t.Helper()
	d := ParseDiagram([]byte(source))
	if len(d.Diagnostics) != 0 {
		return
	}
	in, err := d.Input(scene.ProfileVector, scene.Options{})
	require.NoError(t, err)
	want := titledPayload(xychartPayload(d.xychart))
	got := xychartFromInput(in)
	require.Equal(t, want.Title, got.Title)
	require.Equal(t, want.XY, got.XY)
	for _, entry := range want.Config {
		require.Contains(t, got.Config, entry)
	}
}

func TestXYChartInputCarriesTheWholePayload(t *testing.T) {
	for _, source := range []string{
		"xychart\nbar [1, -2.5, 3]\n",
		"xychart horizontal\ntitle T\nx-axis X [a, b, c, a]\ny-axis \"Y\" -5 --> 5\nbar \"B\" [1, 2]\nline [4 \"p\", -4, 3]\n",
		"xychart\nx-axis 0 --> 10\nline \"L\" [1, 2, 3]\nbar [3]\n",
		"---\nconfig:\n  xyChart:\n    width: 900\n    xAxis:\n      showLabel: false\n---\nxychart\nx-axis [a]\nbar [1]\nx-axis 1 --> 2\n",
	} {
		assertInputCarriesThePayload(t, source)
	}
}

func TestXYChartCorpusInputsCarryTheirPayloads(t *testing.T) {
	paths, err := filepath.Glob(filepath.Join("..", "..", "corpus", "xychart", "*", "*.mmd"))
	require.NoError(t, err)
	require.NotEmpty(t, paths)
	for _, path := range paths {
		data, err := os.ReadFile(path)
		require.NoError(t, err)
		assertInputCarriesThePayload(t, string(data))
	}
}

func TestXYChartModelDumpCarriesTheRegions(t *testing.T) {
	d := ParseDiagram([]byte("xychart\nx-axis [a, b]\nbar [1, 2]\n"))
	in, err := d.Input(scene.ProfileVector, scene.Options{})
	require.NoError(t, err)
	require.Len(t, in.RegionSets, 2)
	require.Equal(t, []int{xychartTagAxes, 0, 1, 0, 0, 2000, 4000}, in.RegionSets[0].Regions[:7])
}

func assertXYChartLaysOutValid(t *testing.T, d *Diagram) {
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

func FuzzXYChartLayout(f *testing.F) {
	paths, err := filepath.Glob(filepath.Join("..", "..", "corpus", "xychart", "*", "*.mmd"))
	require.NoError(f, err)
	for _, path := range paths {
		data, err := os.ReadFile(path)
		require.NoError(f, err)
		f.Add(data)
	}
	f.Add([]byte("xychart\nbar [1, 2]\n"))
	f.Fuzz(func(t *testing.T, data []byte) {
		d := ParseDiagram(data)
		if d.Kind != xychartKind || len(d.Diagnostics) != 0 {
			return
		}
		assertXYChartLaysOutValid(t, d)
	})
}
