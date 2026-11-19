package layout

import (
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const ishikawaDemo = "ishikawa-beta\n  Blurry Photo\n    Process\n      Out of focus\n      Shaky\n    User\n"

func ishikawaLayoutOf(t *testing.T, src string, profile scene.Profile) scene.Scene {
	t.Helper()
	d := ParseDiagram([]byte(src))
	require.Empty(t, d.Diagnostics)
	in, err := d.Input(profile, scene.Options{})
	require.NoError(t, err)
	s, _, err := Layout(in)
	require.NoError(t, err)
	clause, failed, err := s.Validate()
	require.NoError(t, err)
	require.False(t, failed, clause)
	return s
}

func TestIshikawaModelDumpNamesBoxesAnchorsAndRoutes(t *testing.T) {
	dump := diagramModelDump(t, ishikawaDemo)
	require.Contains(t, dump, `{"id":"n0","role":"node","parent":"","exclusive":true,"shape":"effect"}`)
	require.Contains(t, dump, `{"id":"n3","role":"node","parent":"","exclusive":true,"shape":"cause:2"}`)
	require.Contains(t, dump, `{"id":"a0","role":"node","parent":"","exclusive":false,"shape":"anchor"}`)
	require.Contains(t, dump, `{"id":"e0","from":"a0","to":"n0","orthogonal":true,"marker_end":"none"}`)
	require.Contains(t, dump, `{"id":"e1","from":"a1","to":"n1","orthogonal":false,"marker_start":"point","marker_end":"none"}`)
	require.Contains(t, dump, `{"id":"e3","from":"a3","to":"n3","orthogonal":true,"marker_start":"point","marker_end":"none"}`)
	require.Contains(t, dump, `{"id":"n2.label","owner":"n2","text":"Out of focus","lines":[]}`)
	require.Equal(t, 10, strings.Count(dump, `"role":"node"`))
}

func TestIshikawaLayoutKeepsAnchorsOnRouteStarts(t *testing.T) {
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		s := ishikawaLayoutOf(t, ishikawaDemo, profile)
		require.Len(t, s.Boxes, 10)
		for k, route := range s.Routes {
			anchor := s.Boxes[5+k]
			require.Equal(t, route.From, anchor.ID)
			require.Equal(t, geom.Rect{X: route.Points[0].X, Y: route.Points[0].Y}, anchor.Rect)
			require.False(t, anchor.Exclusive)
			require.Equal(t, s.Boxes[k].ID, route.To)
		}
	}
}

func TestIshikawaSpineEndsOnTheHeadAndRibsMeetTheSpine(t *testing.T) {
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		s := ishikawaLayoutOf(t, ishikawaDemo, profile)
		spine := s.Routes[0].Points
		head := s.Boxes[0].Rect
		require.Equal(t, head.X, spine[1].X)
		require.Equal(t, spine[0].Y, spine[1].Y)
		require.InDelta(t, float64(head.Y)+float64(head.H)/2, float64(spine[1].Y), 1)
		require.Equal(t, spine[0].Y, s.Routes[1].Points[0].Y)
		require.Equal(t, spine[0].Y, s.Routes[4].Points[0].Y)
		require.Less(t, s.Routes[1].Points[1].Y, spine[0].Y)
		require.Greater(t, s.Routes[4].Points[1].Y, spine[0].Y)
	}
}

func TestIshikawaProfilesShareIdentities(t *testing.T) {
	vector := ishikawaLayoutOf(t, ishikawaDemo, scene.ProfileVector)
	cell := ishikawaLayoutOf(t, ishikawaDemo, scene.ProfileCell)
	require.Len(t, cell.Boxes, len(vector.Boxes))
	for i := range vector.Boxes {
		require.Equal(t, vector.Boxes[i].ID, cell.Boxes[i].ID)
	}
	for i := range vector.Routes {
		require.Equal(t, vector.Routes[i].ID, cell.Routes[i].ID)
		require.Equal(t, vector.Routes[i].From, cell.Routes[i].From)
		require.Equal(t, vector.Routes[i].Orthogonal, cell.Routes[i].Orthogonal)
	}
}

func TestIshikawaEffectOnlyHasNoRoutes(t *testing.T) {
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		s := ishikawaLayoutOf(t, "ishikawa-beta\n  Problem\n", profile)
		require.Len(t, s.Boxes, 1)
		require.Empty(t, s.Routes)
		require.Len(t, s.Groups, 1)
	}
}

func TestIshikawaHeaderOnlyIsAnEmptyCanvas(t *testing.T) {
	s := ishikawaLayoutOf(t, "ishikawa-beta\n", scene.ProfileCell)
	require.Empty(t, s.Boxes)
	require.Equal(t, geom.Size{W: 2, H: 2}, s.Canvas)
}

func TestIshikawaSceneDrawsArrowsTowardTheSpine(t *testing.T) {
	s := ishikawaLayoutOf(t, ishikawaDemo, scene.ProfileCell)
	var edge *scene.Group
	for _, g := range s.Groups {
		if g.Owner == "e1" {
			edge = g
		}
	}
	require.NotNil(t, edge)
	require.Len(t, edge.Items, 2)
	marker, ok := edge.Items[1].(*scene.MarkerRef)
	require.True(t, ok)
	require.Equal(t, "point", marker.Marker)
	require.Equal(t, s.Routes[1].Points[0], marker.At)
	require.Equal(t, scene.AxisPlusY, marker.Axis)
	for _, g := range s.Groups {
		if g.Owner == "e0" {
			require.Len(t, g.Items, 1)
		}
	}
}

func TestIshikawaOnlyHeadAndCausesAreOutlined(t *testing.T) {
	s := ishikawaLayoutOf(t, ishikawaDemo, scene.ProfileVector)
	items := map[string]int{}
	for _, g := range s.Groups {
		if g.Role == scene.GroupRoleNode {
			items[g.Owner] = len(g.Items)
		}
	}
	require.Equal(t, map[string]int{"n0": 2, "n1": 2, "n2": 1, "n3": 1, "n4": 2}, items)
}

func TestIshikawaWrapsLongLabelsWithoutBreakingClearance(t *testing.T) {
	src := "ishikawa-beta\n  A problem with a rather long effect statement that wraps\n    Category with a long caption " + strings.Repeat("word ", 20) + "\n      sub cause " + strings.Repeat("longer ", 15) + "\n      second\n"
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		s := ishikawaLayoutOf(t, src, profile)
		require.Greater(t, s.Boxes[2].Rect.H, s.Boxes[3].Rect.H)
	}
}

func TestIshikawaLimits(t *testing.T) {
	var b strings.Builder
	b.WriteString("ishikawa-beta\n  e\n")
	for i := range 5 {
		b.WriteString("    c" + strconv.Itoa(i) + "\n")
	}
	d := ParseDiagram([]byte(b.String()))
	require.Empty(t, d.Diagnostics)
	options := scene.Options{Limits: scene.Limits{MaxNodes: 3, MaxEdges: 5000, MaxTextBytes: 1 << 20}}
	in, err := d.Input(scene.ProfileVector, options)
	require.NoError(t, err)
	_, _, err = Layout(in)
	require.Error(t, err)
}

func TestIshikawaRejectsInputsItDidNotBuild(t *testing.T) {
	for name, in := range map[string]Input{
		"no effect":    {Kind: ishikawaKind, Boxes: []Box{{ID: "n0", Shape: "cause:1"}}},
		"bad depth":    {Kind: ishikawaKind, Boxes: []Box{{ID: "n0", Shape: "effect"}, {ID: "n1", Shape: "cause:x"}}},
		"depth gap":    {Kind: ishikawaKind, Boxes: []Box{{ID: "n0", Shape: "effect"}, {ID: "n1", Shape: "cause:2"}}},
		"stray route":  {Kind: ishikawaKind, Boxes: []Box{{ID: "n0", Shape: "effect"}}, Routes: []Route{{ID: "e0", From: "a0", To: "n0"}}},
		"label last":   {Kind: ishikawaKind, Boxes: []Box{{ID: "a0", Shape: "anchor"}, {ID: "n0", Shape: "effect"}}},
		"wrong anchor": {Kind: ishikawaKind, Boxes: []Box{{ID: "n0", Shape: "effect"}, {ID: "n1", Shape: "cause:1"}, {ID: "x", Shape: "anchor"}, {ID: "a1", Shape: "anchor"}}, Routes: []Route{{ID: "e0", From: "a1", To: "n0"}}},
	} {
		in.Options = scene.DefaultOptions()
		_, _, err := Layout(in)
		require.ErrorIs(t, err, errIshikawaInput, name)
	}
}

func TestIshikawaCorpusLaysOutAndValidates(t *testing.T) {
	paths, err := filepath.Glob(filepath.Join("..", "..", "corpus", "ishikawa", "*", "*.mmd"))
	require.NoError(t, err)
	require.NotEmpty(t, paths)
	for _, path := range paths {
		src, err := os.ReadFile(path)
		require.NoError(t, err)
		for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
			ishikawaLayoutOf(t, string(src), profile)
		}
	}
}

type fishWords struct{ state uint32 }

func (w *fishWords) draw(n int) int {
	w.state ^= w.state << 13
	w.state ^= w.state >> 17
	w.state ^= w.state << 5
	return int(w.state % uint32(n))
}

func randomIshikawa(seed uint32) string {
	words := []string{"amber", "birch", "cedar", "delta", "ember", "fjord", "garnet", "harbor", "iris", "juniper", "kelp", "lumen"}
	w := &fishWords{state: seed}
	var b strings.Builder
	b.WriteString("ishikawa-beta\n  effect " + words[w.draw(len(words))] + "\n")
	depth := 1
	for range 1 + w.draw(30) {
		depth = 1 + w.draw(min(depth+1, 6))
		b.WriteString(strings.Repeat(" ", 2+2*depth))
		for range 1 + w.draw(5) {
			b.WriteString(words[w.draw(len(words))] + " ")
		}
		b.WriteString("\n")
	}
	return b.String()
}

func TestIshikawaRandomDiagramsValidate(t *testing.T) {
	for seed := uint32(1); seed <= 150; seed++ {
		src := randomIshikawa(seed)
		for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
			ishikawaLayoutOf(t, src, profile)
		}
	}
}
