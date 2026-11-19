package chart_test

import (
	"os"
	"path/filepath"
	"slices"
	"strconv"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/cells"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func treemapCorpusFiles(t *testing.T) []string {
	t.Helper()
	paths, err := filepath.Glob(filepath.Join("..", "..", "..", "corpus", "treemap", "*", "*.mmd"))
	require.NoError(t, err)
	require.NotEmpty(t, paths)
	slices.Sort(paths)
	return paths
}

func treemapScene(t *testing.T, source string, profile scene.Profile) scene.Scene {
	t.Helper()
	return sceneOf(t, source, profile)
}

const treemapTwoSections = "treemap-beta\ntitle Sales\n\"A\"\n  \"B\": 10\n  \"C\": 30\n\"D\"\n  \"E\": 20\n"

func TestTreemapCorpusScenesAreValid(t *testing.T) {
	for _, path := range treemapCorpusFiles(t) {
		data, err := os.ReadFile(path)
		require.NoError(t, err)
		for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
			t.Run(strings.ReplaceAll(path, string(filepath.Separator), "/")+"/"+profile.String(), func(t *testing.T) {
				s := treemapScene(t, string(data), profile)
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

func TestTreemapCanvasIsTheConfiguredSize(t *testing.T) {
	s := treemapScene(t, "treemap-beta\n\"A\"\n  \"B\": 1\n", scene.ProfileVector)
	require.Equal(t, geom.Size{W: 960 * 64, H: 500 * 64}, s.Canvas)
	s = treemapScene(t, "treemap-beta\ntitle T\n\"A\"\n  \"B\": 1\n", scene.ProfileVector)
	require.Equal(t, geom.Size{W: 960 * 64, H: 530 * 64}, s.Canvas)
	require.Equal(t, int32(30*64), box(t, s, "root").Rect.Y)
	s = treemapScene(t, "---\nconfig:\n  treemap:\n    nodeWidth: 50\n    nodeHeight: 40\n---\ntreemap-beta\n\"A\"\n  \"B\": 1\n", scene.ProfileVector)
	require.Equal(t, geom.Size{W: 500 * 64, H: 400 * 64}, s.Canvas)
	s = treemapScene(t, "treemap-beta\n\"A\"\n  \"B\": 1\n", scene.ProfileCell)
	require.Equal(t, geom.Size{W: 120, H: 32}, s.Canvas)
}

func TestTreemapBoxesFollowThePreorder(t *testing.T) {
	s := treemapScene(t, treemapTwoSections, scene.ProfileVector)
	var ids, roles, parents []string
	for _, b := range s.Boxes {
		ids = append(ids, b.ID)
		roles = append(roles, b.Role.String())
		parents = append(parents, b.Parent)
	}
	require.Equal(t, []string{"root", "n0", "n1", "n2", "n3", "n4"}, ids)
	require.Equal(t, []string{"group", "group", "node", "node", "group", "node"}, roles)
	require.Equal(t, []string{"", "root", "n0", "n0", "root", "n3"}, parents)
	for _, b := range s.Boxes {
		require.False(t, b.Exclusive, b.ID)
	}
}

func TestTreemapChildrenAreSortedByValueThenDeclaration(t *testing.T) {
	s := treemapScene(t, "treemap-beta\n\"A\"\n  \"B\": 5\n  \"C\": 5\n  \"D\": 9\n", scene.ProfileVector)
	d, b, c := box(t, s, "n3").Rect, box(t, s, "n1").Rect, box(t, s, "n2").Rect
	require.Greater(t, d.W*d.H, b.W*b.H)
	require.True(t, d.X < b.X || d.Y < b.Y)
	require.True(t, b.X < c.X || b.Y < c.Y)
}

func TestTreemapAreasAreProportionalToValues(t *testing.T) {
	s := treemapScene(t, "---\nconfig:\n  treemap:\n    padding: 0\n---\ntreemap-beta\n\"A\"\n  \"B\": 75\n  \"C\": 25\n", scene.ProfileVector)
	b, c := box(t, s, "n1").Rect, box(t, s, "n2").Rect
	ratio := float64(int64(b.W)*int64(b.H)) / float64(int64(c.W)*int64(c.H))
	require.InDelta(t, 3.0, ratio, 0.01)
}

func TestTreemapLeafOfASectionHeaderLabels(t *testing.T) {
	s := treemapScene(t, treemapTwoSections, scene.ProfileVector)
	name, value := label(t, s, "n0.name"), label(t, s, "n0.value")
	require.Equal(t, []string{"A"}, name.Lines)
	require.Equal(t, []string{"40"}, value.Lines)
	group := box(t, s, "n0").Rect
	require.Less(t, name.Rect.X, value.Rect.X)
	require.GreaterOrEqual(t, name.Rect.Y, group.Y)
	require.LessOrEqual(t, value.Rect.X+value.Rect.W, group.X+group.W)
	title := label(t, s, "title")
	require.Equal(t, []string{"Sales"}, title.Lines)
	require.Equal(t, s.Canvas.W/2, title.Rect.X+title.Rect.W/2+(title.Rect.W%2)*0)
}

func TestTreemapLabelsCarryTheFormattedValue(t *testing.T) {
	s := treemapScene(t, "treemap-beta\n\"A\"\n  \"B\": 1234567.5\n  \"C\": 2\n", scene.ProfileVector)
	require.Equal(t, "1,234,567.5", label(t, s, "n1.value").Text)
	require.Equal(t, "1,234,569.5", label(t, s, "n0.value").Text)
}

func TestTreemapHugeValuesStillLayOut(t *testing.T) {
	s := treemapScene(t, "treemap-beta\n\"A\"\n  \"B\": 7654321\n  \"C\": 1000000000\n", scene.ProfileVector)
	clause, failed, err := s.Validate()
	require.NoError(t, err)
	require.False(t, failed, clause.Message)
	b, c := box(t, s, "n1").Rect, box(t, s, "n2").Rect
	require.Greater(t, int64(c.W)*int64(c.H), 100*int64(b.W)*int64(b.H))
}

func TestTreemapTinyLeavesHideTheirLabels(t *testing.T) {
	var b strings.Builder
	b.WriteString("treemap-beta\n\"A\"\n  \"Big\": 100000\n")
	for i := range 5 {
		b.WriteString("  \"tiny" + strconv.Itoa(i) + "\": 1\n")
	}
	s := treemapScene(t, b.String(), scene.ProfileVector)
	require.True(t, shown(label(t, s, "n1.name")))
	require.False(t, shown(label(t, s, "n2.name")))
	require.Empty(t, label(t, s, "n2.name").Lines)
}

func TestTreemapLongNamesAreEllipsized(t *testing.T) {
	s := treemapScene(t, "treemap-beta\n\"A\"\n  \"A very long leaf name that cannot fit its box\": 1\n  \"Second\": 40\n", scene.ProfileCell)
	l := label(t, s, "n1.name")
	if shown(l) {
		require.True(t, strings.HasSuffix(l.Lines[0], "..."), l.Lines[0])
	}
}

func TestTreemapSeriesFollowTheTopLevelNodes(t *testing.T) {
	s := treemapScene(t, treemapTwoSections, scene.ProfileVector)
	series := map[string]uint8{}
	for _, g := range s.Groups {
		for _, item := range g.Items {
			if r, ok := item.(*scene.Rect); ok && strings.HasPrefix(r.Style, "series") {
				series[g.Owner] = r.Series
			}
		}
	}
	require.Equal(t, map[string]uint8{"n1": 0, "n2": 0, "n4": 1}, series)
}

func TestTreemapEmptyDiagramLaysOut(t *testing.T) {
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		s := treemapScene(t, "treemap-beta\n", profile)
		clause, failed, err := s.Validate()
		require.NoError(t, err)
		require.False(t, failed, clause.Message)
		require.Len(t, s.Boxes, 1)
	}
}

func TestTreemapSeriesLabelsAreShown(t *testing.T) {
	for _, path := range treemapCorpusFiles(t) {
		data, err := os.ReadFile(path)
		require.NoError(t, err)
		s := treemapScene(t, string(data), scene.ProfileVector)
		texts := textContents(s)
		for _, b := range s.Boxes {
			if b.Parent != "root" {
				continue
			}
			l := label(t, s, b.ID+".name")
			if l.Text == "" || int64(b.Rect.W) < 8*64 {
				continue
			}
			require.True(t, texts[l.Lines[0]] || !shown(l), path+" "+l.Text)
		}
	}
}

func TestTreemapExhaustedInsetsStayInsideParents(t *testing.T) {
	for _, source := range []string{
		"treemap-beta\n\"A\"\n  \"B\"\n    \"C\": 0\n",
		"---\nconfig:\n  treemap:\n    nodeWidth: 1\n    nodeHeight: 1\n---\ntreemap-beta\n\"A\"\n  \"B\"\n    \"C\": 1\n",
	} {
		for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
			s := treemapScene(t, source, profile)
			require.Len(t, s.Boxes, 4)
			for _, child := range s.Boxes[1:] {
				at := slices.IndexFunc(s.Boxes, func(parent scene.Box) bool {
					return parent.ID == child.Parent
				})
				require.NotEqual(t, -1, at)
				contained, err := geom.Contains(s.Boxes[at].Rect, child.Rect)
				require.NoError(t, err)
				require.True(t, contained, child.ID)
			}
			clause, failed, err := s.Validate()
			require.NoError(t, err)
			require.False(t, failed, clause.Message)
		}
	}
}
