package layout

import (
	"strconv"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const mindmapDemo = "mindmap\n  root((Root))\n    A\n      A1\n    B[Square]\n    C\n"

func mindmapLayoutOf(t *testing.T, src string, profile scene.Profile) scene.Scene {
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

func rects(s scene.Scene) []geom.Rect {
	out := make([]geom.Rect, len(s.Boxes))
	for i, b := range s.Boxes {
		out[i] = b.Rect
	}
	return out
}

func points(s scene.Scene) [][]geom.Point {
	out := make([][]geom.Point, len(s.Routes))
	for i, r := range s.Routes {
		out[i] = r.Points
	}
	return out
}

func TestMindmapCellGeometry(t *testing.T) {
	s := mindmapLayoutOf(t, mindmapDemo, scene.ProfileCell)
	require.Equal(t, geom.Size{W: 35, H: 9}, s.Canvas)
	require.Equal(t, []geom.Rect{{X: 13, Y: 3, W: 6, H: 3}, {X: 23, Y: 1, W: 3, H: 3}, {X: 30, Y: 1, W: 4, H: 3}, {X: 1, Y: 3, W: 8, H: 3}, {X: 23, Y: 5, W: 3, H: 3}}, rects(s))
	require.Equal(t, [][]geom.Point{
		{{X: 19, Y: 4}, {X: 21, Y: 4}, {X: 21, Y: 2}, {X: 23, Y: 2}},
		{{X: 26, Y: 2}, {X: 30, Y: 2}},
		{{X: 13, Y: 4}, {X: 9, Y: 4}},
		{{X: 19, Y: 4}, {X: 21, Y: 4}, {X: 21, Y: 6}, {X: 23, Y: 6}},
	}, points(s))
}

func TestMindmapVectorGeometry(t *testing.T) {
	s := mindmapLayoutOf(t, mindmapDemo, scene.ProfileVector)
	require.Equal(t, geom.Size{W: 21614, H: 8448}, s.Canvas)
	require.Equal(t, []geom.Rect{{X: 7955, Y: 2944, W: 3272, H: 2560}, {X: 13787, Y: 1024, W: 1932, H: 2560}, {X: 18279, Y: 1024, W: 2311, H: 2560}, {X: 1024, Y: 2944, W: 4371, H: 2560}, {X: 13787, Y: 4864, W: 1941, H: 2560}}, rects(s))
	require.Equal(t, [][]geom.Point{
		{{X: 11227, Y: 4224}, {X: 12507, Y: 4224}, {X: 12507, Y: 2304}, {X: 13787, Y: 2304}},
		{{X: 15719, Y: 2304}, {X: 18279, Y: 2304}},
		{{X: 7955, Y: 4224}, {X: 5395, Y: 4224}},
		{{X: 11227, Y: 4224}, {X: 12507, Y: 4224}, {X: 12507, Y: 6144}, {X: 13787, Y: 6144}},
	}, points(s))
}

func TestMindmapModelDumpNamesBoxesRoutesAndLabels(t *testing.T) {
	dump := diagramModelDump(t, mindmapDemo)
	require.Contains(t, dump, `{"id":"n0","role":"node","parent":"","exclusive":true,"shape":"mindmapCircle"}`)
	require.Contains(t, dump, `{"id":"n3","role":"node","parent":"","exclusive":true}`)
	require.Contains(t, dump, `{"id":"e2","from":"n0","to":"n3","orthogonal":true,"marker_end":"none"}`)
	require.Contains(t, dump, `{"id":"n3.label","owner":"n3","text":"Square","lines":[]}`)
	require.Equal(t, 5, strings.Count(dump, `"role":"node"`))
}

func TestMindmapProfilesShareIdentities(t *testing.T) {
	vector := mindmapLayoutOf(t, mindmapDemo, scene.ProfileVector)
	cell := mindmapLayoutOf(t, mindmapDemo, scene.ProfileCell)
	require.Len(t, cell.Boxes, len(vector.Boxes))
	for i := range vector.Boxes {
		require.Equal(t, vector.Boxes[i].ID, cell.Boxes[i].ID)
	}
	for i := range vector.Routes {
		require.Equal(t, vector.Routes[i].ID, cell.Routes[i].ID)
		require.Equal(t, vector.Routes[i].From, cell.Routes[i].From)
	}
}

func TestMindmapConfigOverridesApplyToTheVectorProfileOnly(t *testing.T) {
	src := "---\nconfig:\n  mindmap:\n    padding: 20\n    maxNodeWidth: 100\n---\nmindmap\n  root\n    a long label that wraps past the maximum width of the node\n"
	vector := mindmapLayoutOf(t, src, scene.ProfileVector)
	require.LessOrEqual(t, vector.Boxes[1].Rect.W, int32(100*64))
	require.Equal(t, int32(2*20*64)+int32(1280), vector.Boxes[0].Rect.H)
	plain := mindmapLayoutOf(t, "mindmap\n  root\n    a long label that wraps past the maximum width of the node\n", scene.ProfileVector)
	require.NotEqual(t, plain.Boxes[0].Rect.H, vector.Boxes[0].Rect.H)
	cell := mindmapLayoutOf(t, src, scene.ProfileCell)
	require.Equal(t, mindmapLayoutOf(t, "mindmap\n  root\n    a long label that wraps past the maximum width of the node\n", scene.ProfileCell).Canvas, cell.Canvas)
}

func TestMindmapLimits(t *testing.T) {
	var b strings.Builder
	b.WriteString("mindmap\n  root\n")
	for i := range 5 {
		b.WriteString("    n" + strconv.Itoa(i) + "\n")
	}
	d := ParseDiagram([]byte(b.String()))
	require.Empty(t, d.Diagnostics)
	options := scene.Options{Limits: scene.Limits{MaxNodes: 3, MaxEdges: 5000, MaxTextBytes: 1 << 20}}
	in, err := d.Input(scene.ProfileVector, options)
	require.NoError(t, err)
	_, _, err = Layout(in)
	require.Error(t, err)
}

func TestMindmapRoutesStayOffForeignBoxesOnRandomShapes(t *testing.T) {
	var b strings.Builder
	b.WriteString("mindmap\n  root\n")
	for i := range 4 {
		b.WriteString("    wide branch number " + strconv.Itoa(i) + " with a long caption\n")
		b.WriteString("      x\n        y\n      zz\n")
		b.WriteString("    s\n      t\n")
	}
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		s := mindmapLayoutOf(t, b.String(), profile)
		for i, route := range s.Routes {
			for _, box := range s.Boxes {
				if box.ID == route.From || box.ID == route.To {
					continue
				}
				hit, err := geom.PolylineHitsRect(route.Points, box.Rect)
				require.NoError(t, err)
				require.False(t, hit, "route %d crosses %s", i, box.ID)
			}
		}
	}
}
