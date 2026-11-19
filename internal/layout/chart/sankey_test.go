package chart_test

import (
	"errors"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/cells"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/layout"
	"github.com/gosuda/elegant-mermaid/internal/layout/chart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func sankeyFiles(t *testing.T) []string {
	t.Helper()
	paths, err := filepath.Glob(filepath.Join("..", "..", "..", "corpus", "sankey", "*", "*.mmd"))
	require.NoError(t, err)
	require.NotEmpty(t, paths)
	slices.Sort(paths)
	return paths
}

func sankeyScene(t *testing.T, source string) scene.Scene {
	t.Helper()
	s, err := sankeyLayout(source)
	require.NoError(t, err)
	return s
}

func sankeyLayout(source string) (scene.Scene, error) {
	d := layout.ParseDiagram([]byte(source))
	if len(d.Diagnostics) != 0 {
		return scene.Scene{}, errors.New(d.Diagnostics[0].Message)
	}
	return inputAndLayout(d)
}

func sankeyBoxByID(s scene.Scene, id string) geom.Rect {
	for _, b := range s.Boxes {
		if b.ID == id {
			return b.Rect
		}
	}
	return geom.Rect{}
}

func TestSankeySingleLinkMatchesHandArithmetic(t *testing.T) {
	s := sankeyScene(t, "sankey\na,b,10\n")
	require.Equal(t, geom.Size{W: 38400, H: 25600}, s.Canvas)
	require.Equal(t, geom.Rect{X: 0, Y: 0, W: 640, H: 25599}, sankeyBoxByID(s, "n0"))
	require.Equal(t, geom.Rect{X: 37760, Y: 0, W: 640, H: 25599}, sankeyBoxByID(s, "n1"))
	require.Equal(t, []geom.Point{{X: 640, Y: 12799}, {X: 37760, Y: 12799}}, s.Routes[0].Points)
	require.Equal(t, []string{"a", "10"}, s.Labels[0].Lines)
	require.Equal(t, "a<br>10", s.Labels[0].Text)
}

func TestSankeyValuesAndPaddingFollowShowValues(t *testing.T) {
	plain := sankeyScene(t, "---\nconfig:\n  sankey:\n    showValues: false\n---\nsankey\na,b,1.234\na,c,2\n")
	require.Equal(t, "a", plain.Labels[0].Text)
	shown := sankeyScene(t, "sankey\na,b,1.234\na,c,2\n")
	require.Equal(t, "a<br>3.23", shown.Labels[0].Text)
	require.Equal(t, "b<br>1.23", shown.Labels[1].Text)
	gap := func(s scene.Scene) int32 {
		return sankeyBoxByID(s, "n2").Y - (sankeyBoxByID(s, "n1").Y + sankeyBoxByID(s, "n1").H)
	}
	require.Equal(t, int32(768), gap(plain))
	require.Equal(t, int32(1728), gap(shown))
}

func TestSankeyConfiguredCanvas(t *testing.T) {
	s := sankeyScene(t, "---\nconfig:\n  sankey:\n    width: 410\n    height: 200\n---\nsankey\na,b,1\n")
	require.Equal(t, geom.Size{W: 410 * 64, H: 200 * 64}, s.Canvas)
}

func TestSankeyAlignmentPlacesSourcesLikeD3(t *testing.T) {
	body := "sankey\na,b,1\nb,c,1\nx,c,1\n"
	layerOfX := func(config string) int32 {
		text := body
		if config != "" {
			text = "---\nconfig:\n  sankey:\n    nodeAlignment: " + config + "\n---\n" + body
		}
		s := sankeyScene(t, text)
		return sankeyBoxByID(s, "n3").X
	}
	first := layerOfX("")
	require.Equal(t, int32(0), first)
	require.Equal(t, int32(0), layerOfX("left"))
	middle := layerOfX("right")
	require.Greater(t, middle, int32(0))
	require.Equal(t, middle, layerOfX("center"))
}

func TestSankeyRejectsValuesTheLayoutCannotPlace(t *testing.T) {
	for source, want := range map[string]string{
		"sankey\na,b,x\n":      "no finite value",
		"sankey\na,b,-1\n":     "negative value",
		"sankey\na,b,1\nb,a,1": "circular link",
		"sankey\na,a,1\n":      "circular link",
	} {
		_, err := sankeyLayout(source)
		require.Error(t, err, source)
		require.Contains(t, err.Error(), want, source)
	}
	_, err := sankeyLayout("sankey\na,b,3000000\n")
	require.ErrorIs(t, err, chart.ErrOverflow)
}

func TestSankeyZeroValuesLayOutWithoutHeight(t *testing.T) {
	s := sankeyScene(t, "sankey\na,b,0\n")
	require.Equal(t, int32(0), sankeyBoxByID(s, "n0").H)
	clause, failed, err := s.Validate()
	require.NoError(t, err)
	require.False(t, failed, clause.Message)
}

func TestSankeyNarrowCanvasTranslatesCompleteScene(t *testing.T) {
	s := sankeyScene(t, "---\nconfig:\n  sankey:\n    width: 1\n---\nsankey\na,b,10\n")
	require.Equal(t, int32(576), sankeyBoxByID(s, "n0").X)
	require.Equal(t, int32(0), sankeyBoxByID(s, "n1").X)
	require.Equal(t, int32(1216), s.Routes[0].Points[0].X)
	require.Equal(t, int32(0), s.Routes[0].Points[1].X)
	clause, failed, err := s.Validate()
	require.NoError(t, err)
	require.False(t, failed, clause.Message)
	assertNonNegative(t, "width: 1", s)
	for _, group := range s.Groups {
		if group.Role != scene.GroupRoleNode {
			continue
		}
		item, ok := group.Items[0].(*scene.Rect)
		require.True(t, ok)
		require.Equal(t, sankeyBoxByID(s, group.Owner), item.Rect)
	}
	path, ok := s.Groups[0].Items[0].(*scene.Path)
	require.True(t, ok)
	start, ok := path.Commands[0].(*scene.MoveTo)
	require.True(t, ok)
	end, ok := path.Commands[1].(*scene.CubicTo)
	require.True(t, ok)
	require.Equal(t, s.Routes[0].Points[0], start.P)
	require.Equal(t, s.Routes[0].Points[1], end.P)
}

func TestSankeyCorpusInvariants(t *testing.T) {
	for _, path := range sankeyFiles(t) {
		data, err := os.ReadFile(path)
		require.NoError(t, err)
		s := sankeyScene(t, string(data))
		clause, failed, err := s.Validate()
		require.NoError(t, err, path)
		require.False(t, failed, "%s: %s", path, clause.Message)
		assertNonNegative(t, path, s)
		assertColumnsSeparated(t, path, s)
		assertLinkWidthsFit(t, path, s)
	}
}

func assertNonNegative(t *testing.T, path string, s scene.Scene) {
	t.Helper()
	for _, b := range s.Boxes {
		require.GreaterOrEqual(t, b.Rect.X, int32(0), path)
		require.GreaterOrEqual(t, b.Rect.Y, int32(0), path)
	}
	for _, l := range s.Labels {
		require.GreaterOrEqual(t, l.Rect.X, int32(0), path)
		require.GreaterOrEqual(t, l.Rect.Y, int32(0), path)
		require.LessOrEqual(t, l.Rect.X+l.Rect.W, s.Canvas.W, path)
		require.LessOrEqual(t, l.Rect.Y+l.Rect.H, s.Canvas.H, path)
	}
}

func assertColumnsSeparated(t *testing.T, path string, s scene.Scene) {
	t.Helper()
	columns := map[int32][]geom.Rect{}
	for _, b := range s.Boxes {
		columns[b.Rect.X] = append(columns[b.Rect.X], b.Rect)
	}
	for x, column := range columns {
		slices.SortFunc(column, func(a, b geom.Rect) int { return int(a.Y - b.Y) })
		for i := 1; i < len(column); i++ {
			prev := column[i-1]
			require.GreaterOrEqual(t, column[i].Y-(prev.Y+prev.H), int32(0), "%s column %d", path, x)
		}
	}
}

func assertLinkWidthsFit(t *testing.T, path string, s scene.Scene) {
	t.Helper()
	out, in := map[string]int64{}, map[string]int64{}
	for _, g := range s.Groups {
		if g.Role != scene.GroupRoleEdge {
			continue
		}
		route := routeByID(s, g.Owner)
		width := int64(g.Items[0].(*scene.Path).Width.Units)
		out[route.From] += width
		in[route.To] += width
	}
	for _, b := range s.Boxes {
		require.LessOrEqual(t, out[b.ID], int64(b.Rect.H), "%s %s outgoing", path, b.ID)
		require.LessOrEqual(t, in[b.ID], int64(b.Rect.H), "%s %s incoming", path, b.ID)
	}
}

func routeByID(s scene.Scene, id string) scene.Route {
	for _, r := range s.Routes {
		if r.ID == id {
			return r
		}
	}
	return scene.Route{}
}

func TestSankeyCorpusRendersEveryLabel(t *testing.T) {
	for _, path := range sankeyFiles(t) {
		data, err := os.ReadFile(path)
		require.NoError(t, err)
		result, err := cells.Render(sankeyScene(t, string(data)), cells.Options{})
		require.NoError(t, err, path)
		require.Zero(t, result.RefusedClusters, path)
	}
}

func TestSankeyEveryNodeHasASeriesAndLabel(t *testing.T) {
	for _, path := range sankeyFiles(t) {
		data, err := os.ReadFile(path)
		require.NoError(t, err)
		s := sankeyScene(t, string(data))
		used := usedSeries(s)
		texts := textContents(s)
		for i, l := range s.Labels {
			require.True(t, used[uint8(i%12)], "%s node %d has no series fill", path, i)
			require.True(t, texts[strings.ReplaceAll(l.Text, "<br>", "\n")], "%s node %d has no label", path, i)
		}
	}
}
