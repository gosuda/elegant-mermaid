package chart_test

import (
	"os"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/layout"
	"github.com/gosuda/elegant-mermaid/internal/layout/chart"
	model "github.com/gosuda/elegant-mermaid/internal/model/xychart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/xychart"
)

func usedSeries(s scene.Scene) map[uint8]bool {
	used := map[uint8]bool{}
	for _, g := range s.Groups {
		for _, item := range g.Items {
			switch v := item.(type) {
			case *scene.Rect:
				recordSeries(used, v.Shape)
			case *scene.Path:
				recordSeries(used, v.Shape)
			}
		}
	}
	return used
}

func recordSeries(used map[uint8]bool, shape scene.Shape) {
	if strings.HasPrefix(shape.Style, "series") {
		used[shape.Series] = true
	}
}

func textContents(s scene.Scene) map[string]bool {
	texts := map[string]bool{}
	for _, g := range s.Groups {
		for _, item := range g.Items {
			text, ok := item.(*scene.Text)
			if !ok {
				continue
			}
			var flat []string
			for _, line := range text.Lines {
				var runs strings.Builder
				for _, run := range line {
					runs.WriteString(run.Text)
				}
				flat = append(flat, runs.String())
			}
			texts[strings.Join(flat, "\n")] = true
		}
	}
	return texts
}

func plotTitles(t *testing.T, source []byte) []string {
	t.Helper()
	start, ds := parser.Parse(source, syntax.Preprocess(source).Removed)
	require.Empty(t, ds)
	m, _ := model.Resolve(source, start)
	var titles []string
	for _, plot := range m.Plots {
		titles = append(titles, plot.Title)
	}
	return titles
}

func TestSeriesLabels(t *testing.T) {
	for _, path := range corpusFiles(t) {
		data, err := os.ReadFile(path)
		require.NoError(t, err)
		if len(layout.ParseDiagram(data).Diagnostics) != 0 {
			continue
		}
		titles := plotTitles(t, data)
		for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
			s := sceneOf(t, string(data), profile)
			texts := textContents(s)
			used := usedSeries(s)
			require.Len(t, used, min(len(titles), 12), path)
			for i, title := range titles {
				require.True(t, used[uint8(i%12)], "%s series %d", path, i)
				require.True(t, texts[chart.SeriesTitle(i, title)], "%s %s: series %d has no label", path, profile, i)
			}
		}
	}
}
