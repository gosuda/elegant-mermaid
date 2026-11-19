package chart_test

import (
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/cells"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

var wardleyRefusals = map[string]int{
	"wardley~0011.mmd": 1,
	"wardley~0019.mmd": 12,
	"wardley~pr-check~1-should-render-tea-shop.mmd":                   1,
	"wardley~pr-check~6-should-render-gpt-tokeniser-architecture.mmd": 7,
}

func wardleyFiles(t *testing.T) []string {
	t.Helper()
	paths, err := filepath.Glob(filepath.Join("..", "..", "..", "corpus", "wardley", "*", "*.mmd"))
	require.NoError(t, err)
	require.NotEmpty(t, paths)
	slices.Sort(paths)
	return paths
}

func TestWardleyCorpusScenesAreValid(t *testing.T) {
	for _, path := range wardleyFiles(t) {
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
					require.Equal(t, wardleyRefusals[filepath.Base(path)], result.RefusedClusters)
				}
			})
		}
	}
}
