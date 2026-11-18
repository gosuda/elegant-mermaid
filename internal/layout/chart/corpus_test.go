package chart_test

import (
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/cells"
	"github.com/gosuda/elegant-mermaid/internal/layout"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func corpusFiles(t *testing.T) []string {
	t.Helper()
	paths, err := filepath.Glob(filepath.Join("..", "..", "..", "corpus", "xychart", "*", "*.mmd"))
	require.NoError(t, err)
	require.NotEmpty(t, paths)
	slices.Sort(paths)
	return paths
}

func sceneOf(t *testing.T, source string, profile scene.Profile) scene.Scene {
	t.Helper()
	d := layout.ParseDiagram([]byte(source))
	if len(d.Diagnostics) != 0 {
		t.Skip("rejected source")
	}
	in, err := d.Input(profile, scene.Options{})
	require.NoError(t, err)
	s, _, err := layout.Layout(in)
	require.NoError(t, err)
	return s
}

func parseFor(t *testing.T, source string) *layout.Diagram {
	t.Helper()
	d := layout.ParseDiagram([]byte(source))
	require.Empty(t, d.Diagnostics)
	return d
}

func inputAndLayout(d *layout.Diagram) (scene.Scene, error) {
	in, err := d.Input(scene.ProfileVector, scene.Options{})
	if err != nil {
		return scene.Scene{}, err
	}
	s, _, err := layout.Layout(in)
	return s, err
}

func TestCorpusScenesAreValid(t *testing.T) {
	for _, path := range corpusFiles(t) {
		data, err := os.ReadFile(path)
		require.NoError(t, err)
		for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
			t.Run(strings.ReplaceAll(path, string(filepath.Separator), "/")+"/"+profile.String(), func(t *testing.T) {
				s := sceneOf(t, string(data), profile)
				clause, failed, err := s.Validate()
				require.NoError(t, err)
				require.False(t, failed, clause.Message)
				if profile == scene.ProfileCell {
					result, err := cells.Render(s, cells.Options{})
					require.NoError(t, err)
					require.Zero(t, result.RefusedClusters)
				}
			})
		}
	}
}
