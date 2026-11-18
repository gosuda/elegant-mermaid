package chart_test

import (
	"os"
	"path/filepath"
	"slices"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/layout"
	model "github.com/gosuda/elegant-mermaid/internal/model/radar"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/radar"
)

func radarCorpusFiles(t *testing.T) []string {
	t.Helper()
	paths, err := filepath.Glob(filepath.Join("..", "..", "..", "corpus", "radar", "*", "*.mmd"))
	require.NoError(t, err)
	require.NotEmpty(t, paths)
	slices.Sort(paths)
	return paths
}

func radarModel(t *testing.T, source []byte) *model.Model {
	t.Helper()
	start, ds := parser.Parse(source, syntax.Preprocess(source).Removed)
	require.Empty(t, ds)
	m, _ := model.Resolve(source, start)
	return m
}

func TestRadarSeriesLabels(t *testing.T) {
	for _, path := range radarCorpusFiles(t) {
		data, err := os.ReadFile(path)
		require.NoError(t, err)
		if len(layout.ParseDiagram(data).Diagnostics) != 0 {
			continue
		}
		m := radarModel(t, data)
		s := sceneOf(t, string(data), scene.ProfileVector)
		texts := textContents(s)
		for series := range usedSeries(s) {
			label := m.Curves[series].Label
			if label == "" || !m.Options.ShowLegend {
				continue
			}
			require.True(t, texts[label], "%s: series %d has no label", path, series)
		}
	}
}

func TestRadarCellProfileEqualsVector(t *testing.T) {
	for _, path := range radarCorpusFiles(t) {
		data, err := os.ReadFile(path)
		require.NoError(t, err)
		if len(layout.ParseDiagram(data).Diagnostics) != 0 {
			continue
		}
		vector := sceneOf(t, string(data), scene.ProfileVector)
		cell := sceneOf(t, string(data), scene.ProfileCell)
		require.Equal(t, vector.Canvas, cell.Canvas, path)
		require.Equal(t, vector.Boxes, cell.Boxes, path)
		require.Equal(t, vector.Labels, cell.Labels, path)
	}
}
