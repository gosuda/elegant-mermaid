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

const vennRadiusUnits = 7168

func vennFiles(t *testing.T) []string {
	t.Helper()
	paths, err := filepath.Glob(filepath.Join("..", "..", "..", "corpus", "venn", "*", "*.mmd"))
	require.NoError(t, err)
	require.NotEmpty(t, paths)
	slices.Sort(paths)
	return paths
}

func circles(s scene.Scene) []*scene.Ellipse {
	var out []*scene.Ellipse
	for _, g := range s.Groups {
		for _, item := range g.Items {
			if e, ok := item.(*scene.Ellipse); ok {
				out = append(out, e)
			}
		}
	}
	return out
}

func TestVennCorpusScenesAreValid(t *testing.T) {
	for _, path := range vennFiles(t) {
		data, err := os.ReadFile(path)
		require.NoError(t, err)
		d := layout.ParseDiagram(data)
		if len(d.Diagnostics) != 0 {
			continue
		}
		t.Run(strings.ReplaceAll(path, string(filepath.Separator), "/"), func(t *testing.T) {
			s := sceneOf(t, string(data), scene.ProfileVector)
			clause, failed, err := s.Validate()
			require.NoError(t, err)
			require.False(t, failed, clause.Message)
			_, err = cells.Render(s, cells.Options{})
			require.NoError(t, err)
		})
	}
}

func TestVennRoomyLabelsAreNotRefused(t *testing.T) {
	s := sceneOf(t, "venn-beta\n  title Skills\n  set A[\"Frontend\"]:10\n    text one\n  set B[\"Backend\"]:10\n    text two\n  union A,B[\"Both\"]:2\n", scene.ProfileVector)
	result, err := cells.Render(s, cells.Options{})
	require.NoError(t, err)
	require.Zero(t, result.RefusedClusters)
}

func TestVennBothProfilesGiveTheVectorScene(t *testing.T) {
	const src = "venn-beta\n  title T\n  set A:10\n    text one\n  set B:6\n  union A,B:3\n"
	vector := sceneOf(t, src, scene.ProfileVector)
	cell := sceneOf(t, src, scene.ProfileCell)
	require.Equal(t, scene.ProfileVector, cell.Options.Profile)
	require.Equal(t, vector.Dump, cell.Dump)
}

func TestVennSeriesLabels(t *testing.T) {
	for _, path := range vennFiles(t) {
		data, err := os.ReadFile(path)
		require.NoError(t, err)
		if len(layout.ParseDiagram(data).Diagnostics) != 0 {
			continue
		}
		s := sceneOf(t, string(data), scene.ProfileVector)
		texts := textContents(s)
		for i, c := range circles(s) {
			require.Equal(t, uint8(i%12), c.Series, path)
			require.Equal(t, "series-tint", c.Style, path)
		}
		for _, label := range s.Labels {
			if strings.HasPrefix(label.ID, "set") && strings.HasSuffix(label.ID, ".label") {
				require.True(t, texts[strings.Join(label.Lines, "\n")], "%s %s", path, label.ID)
			}
		}
	}
}

func TestVennSingleSetIsOneCentredCircle(t *testing.T) {
	s := sceneOf(t, "venn-beta\n  set A:7\n", scene.ProfileVector)
	cs := circles(s)
	require.Len(t, cs, 1)
	require.Equal(t, int32(2*vennRadiusUnits), cs[0].CX)
	require.Equal(t, int32(2*vennRadiusUnits), cs[0].CY)
	require.Equal(t, int32(vennRadiusUnits), cs[0].RX)
	require.Equal(t, int32(4*vennRadiusUnits), s.Canvas.W)
	require.Equal(t, int32(4*vennRadiusUnits), s.Canvas.H)
}

func TestVennTitleAddsABandAboveTheCircles(t *testing.T) {
	plain := sceneOf(t, "venn-beta\n  set A\n", scene.ProfileVector)
	titled := sceneOf(t, "venn-beta\n  title Hello\n  set A\n", scene.ProfileVector)
	band := titled.Canvas.H - plain.Canvas.H
	require.Positive(t, band)
	require.Equal(t, circles(plain)[0].CY+band, circles(titled)[0].CY)
}

func TestVennTwoSetDistanceFollowsTheOverlap(t *testing.T) {
	distance := func(overlap string) int32 {
		s := sceneOf(t, "venn-beta\n  set A:10\n  set B:10\n  union A,B:"+overlap+"\n", scene.ProfileVector)
		cs := circles(s)
		require.Len(t, cs, 2)
		return cs[1].CX - cs[0].CX
	}
	require.Equal(t, int32(2*vennRadiusUnits), distance("0"))
	require.Zero(t, distance("10"))
	disjoint, half, nearly := distance("1"), distance("5"), distance("9")
	require.Less(t, half, disjoint)
	require.Less(t, nearly, half)
	require.Positive(t, nearly)
}

func TestVennThreeSetsUseTheFixedArrangement(t *testing.T) {
	s := sceneOf(t, "venn-beta\n  set A:10\n  set B:10\n  set C:10\n", scene.ProfileVector)
	cs := circles(s)
	require.Len(t, cs, 3)
	require.Equal(t, [2]int32{2 * vennRadiusUnits, vennRadiusUnits}, [2]int32{cs[0].CX, cs[0].CY})
	require.Equal(t, [2]int32{2*vennRadiusUnits + 6207, 2*vennRadiusUnits + 3584}, [2]int32{cs[1].CX, cs[1].CY})
	require.Equal(t, [2]int32{2*vennRadiusUnits - 6207, 2*vennRadiusUnits + 3584}, [2]int32{cs[2].CX, cs[2].CY})
}

func TestVennRadiiFollowTheSquareRootOfTheSizes(t *testing.T) {
	s := sceneOf(t, "venn-beta\n  set A:4\n  set B:1\n", scene.ProfileVector)
	cs := circles(s)
	require.Equal(t, int32(vennRadiusUnits), cs[0].RX)
	require.Equal(t, int32(vennRadiusUnits/2), cs[1].RX)
}

func TestVennCanvasSizeComesFromTheConfig(t *testing.T) {
	s := sceneOf(t, "---\nconfig:\n  venn:\n    width: 400\n    height: 400\n---\nvenn-beta\n  set A\n", scene.ProfileVector)
	require.Equal(t, int32(4*64*100), s.Canvas.W)
}

func TestVennOverflowIsRefused(t *testing.T) {
	d := layout.ParseDiagram([]byte("venn-beta\n  set A:99999999999\n"))
	require.Empty(t, d.Diagnostics)
	_, err := d.Input(scene.ProfileVector, scene.Options{})
	require.Error(t, err)
}
