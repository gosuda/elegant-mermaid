package layout

import (
	"bytes"
	"os"
	"path/filepath"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

var blockProfiles = []scene.Profile{scene.ProfileVector, scene.ProfileCell}

func blockInput(t *testing.T, src string, profile scene.Profile) Input {
	t.Helper()
	d := ParseDiagram([]byte(src))
	for _, diagnostic := range d.Diagnostics {
		require.NotEqual(t, diag.SeverityError, diagnostic.Severity, diagnostic.Message)
	}
	in, err := d.Input(profile, scene.Options{})
	require.NoError(t, err)
	return in
}

func blockScene(t *testing.T, src string, profile scene.Profile) scene.Scene {
	t.Helper()
	s, _, err := Layout(blockInput(t, src, profile))
	require.NoError(t, err)
	clause, failed, err := s.Validate()
	require.NoError(t, err)
	require.False(t, failed, clause)
	return s
}

func requireNodeGroup(t *testing.T, s scene.Scene, owner string) *scene.Group {
	t.Helper()
	group := nodeGroup(&s, owner)
	require.NotNil(t, group, "no node group for %s", owner)
	return group
}

func TestBlockCorpusLaysOutValidly(t *testing.T) {
	paths, err := filepath.Glob(filepath.Join("..", "..", "corpus", "block", "*", "*.mmd"))
	require.NoError(t, err)
	require.NotEmpty(t, paths)
	for _, path := range paths {
		src := readFile(t, path)
		for _, profile := range blockProfiles {
			blockScene(t, src, profile)
		}
	}
}

func readFile(t *testing.T, path string) string {
	t.Helper()
	data, err := os.ReadFile(path)
	require.NoError(t, err)
	return string(data)
}

func TestBlockInputEncodesTheTreeInDeclarationOrder(t *testing.T) {
	in := blockInput(t, "block-beta\ncolumns 3\ne0 b:2\nblock:g\ncolumns 2\nx y\nend\ne0 --> b\nb -- \"t\" --> g\nspace\n", scene.ProfileVector)
	var ids, shapes, parents []string
	for _, box := range in.Boxes {
		ids, shapes, parents = append(ids, box.ID), append(shapes, box.Shape), append(parents, box.Parent)
	}
	require.Equal(t, []string{"root0", "e0", "b", "g", "x", "y", "space0-0"}, ids)
	require.Equal(t, []string{"composite;columns=3", "rect", "rect;span=2", "composite;columns=2", "rect", "rect", "space"}, shapes)
	require.Equal(t, []string{"", "root0", "root0", "root0", "g", "g", "root0"}, parents)
	require.Equal(t, []string{"e1", "e2"}, []string{in.Routes[0].ID, in.Routes[1].ID})
	require.Equal(t, "e2.label", in.Labels[0].ID)
}

func TestBlockInputMapsEdgeStyles(t *testing.T) {
	in := blockInput(t, "block-beta\nA --> B\nB --x C\nC ==> D\nD -.-> E\nE --- F\nF <--> G\n", scene.ProfileVector)
	type style struct{ start, end, line string }
	var got []style
	for _, route := range in.Routes {
		got = append(got, style{route.MarkerStart, route.MarkerEnd, route.Line})
	}
	require.Equal(t, []style{
		{"", "point", "normal"}, {"", "cross", "normal"}, {"", "point", "thick"},
		{"", "point", "dotted"}, {"", "", "normal"}, {"point", "point", "normal"},
	}, got)
}

func TestBlockShapePrimitives(t *testing.T) {
	src := "block-beta\na[\"x\"] b(\"x\") c((\"x\")) d{\"x\"} e{{\"x\"}} f([\"x\"]) g[[\"x\"]] h[(\"x\")] i(((\"x\"))) j>\"x\"] k[/\"x\"/] l[\\\"x\"\\] m[/\"x\"\\] n[\\\"x\"/] o<[\"x\"]>(right)\n"
	vector := map[string]string{"a": "Rect", "b": "RoundRect", "c": "Ellipse", "d": "Polygon", "e": "Polygon", "f": "RoundRect", "g": "Rect", "i": "Ellipse", "j": "Polygon", "k": "Polygon", "l": "Polygon", "m": "Polygon", "n": "Polygon", "o": "Polygon"}
	s := blockScene(t, src, scene.ProfileVector)
	for id, want := range vector {
		require.Equal(t, want, primitiveName(requireNodeGroup(t, s, id).Items[0]), id)
	}
	require.Len(t, requireNodeGroup(t, s, "g").Items, 4)
	require.Len(t, requireNodeGroup(t, s, "i").Items, 3)
}

func primitiveName(item scene.Primitive) string {
	switch item.(type) {
	case *scene.Rect:
		return "Rect"
	case *scene.RoundRect:
		return "RoundRect"
	case *scene.Ellipse:
		return "Ellipse"
	case *scene.Polygon:
		return "Polygon"
	case *scene.Polyline:
		return "Polyline"
	case *scene.Path:
		return "Path"
	}
	return "other"
}

func TestBlockCellShapes(t *testing.T) {
	s := blockScene(t, "block-beta\na[\"x\"] b(\"x\") c((\"x\")) i(((\"x\"))) o<[\"x\"]>(right, down)\n", scene.ProfileCell)
	require.Equal(t, "Rect", primitiveName(requireNodeGroup(t, s, "a").Items[0]))
	require.Equal(t, "RoundRect", primitiveName(requireNodeGroup(t, s, "b").Items[0]))
	require.Equal(t, "RoundRect", primitiveName(requireNodeGroup(t, s, "c").Items[0]))
	ring, ok := requireNodeGroup(t, s, "i").Items[0].(*scene.Rect)
	require.True(t, ok)
	require.Equal(t, scene.LineDouble, ring.Line)
	arrow := requireNodeGroup(t, s, "o")
	var markers []scene.Axis
	for _, item := range arrow.Items {
		if marker, ok := item.(*scene.MarkerRef); ok {
			markers = append(markers, marker.Axis)
		}
	}
	require.Equal(t, []scene.Axis{scene.AxisPlusX, scene.AxisPlusY}, markers)
}

func TestBlockArrowHeadsFollowDirections(t *testing.T) {
	s := blockScene(t, "block-beta\na<[\"x\"]>(right) b<[\"x\"]>(x) c<[\"x\"]>(up, down, left, right) d<[\"x\"]>(y)\n", scene.ProfileVector)
	counts := map[string]int{}
	for _, id := range []string{"a", "b", "c", "d"} {
		polygon, ok := requireNodeGroup(t, s, id).Items[0].(*scene.Polygon)
		require.True(t, ok, id)
		counts[id] = len(polygon.Points)
	}
	require.Equal(t, map[string]int{"a": 5, "b": 6, "c": 8, "d": 6}, counts)
}

func TestBlockEdgePaint(t *testing.T) {
	s := blockScene(t, "block-beta\nA --> B\nB ==> C\nC -.-x D\n", scene.ProfileVector)
	var edges []*scene.Group
	for _, group := range s.Groups {
		if group.Role == scene.GroupRoleEdge {
			edges = append(edges, group)
		}
	}
	require.Len(t, edges, 3)
	plain, thick, dotted := edges[0].Items[0].(*scene.Polyline), edges[1].Items[0].(*scene.Polyline), edges[2].Items[0].(*scene.Polyline)
	require.Equal(t, scene.WidthNormal, plain.Width.Kind)
	require.Equal(t, scene.WidthEmphasis, thick.Width.Kind)
	require.Equal(t, scene.LineDotted, dotted.Line)
	require.Equal(t, "point", edges[0].Items[1].(*scene.MarkerRef).Marker)
	require.Equal(t, "cross", edges[2].Items[1].(*scene.MarkerRef).Marker)
}

func TestBlockSpacesAreBoxesButNeverDrawn(t *testing.T) {
	s := blockScene(t, "block-beta\ncolumns 2\nspace A\n", scene.ProfileVector)
	var space scene.Box
	for _, box := range s.Boxes {
		if box.ID == "space0-0" {
			space = box
		}
	}
	require.False(t, space.Exclusive)
	for _, group := range s.Groups {
		require.NotEqual(t, "space0-0", group.Owner)
	}
}

func TestBlockPaddingConfigWidensTheGrid(t *testing.T) {
	plain := blockScene(t, "block-beta\nA B\n", scene.ProfileVector)
	wide := blockScene(t, "---\nconfig:\n  block:\n    padding: 24\n---\nblock-beta\nA B\n", scene.ProfileVector)
	require.Equal(t, int32(7*(24*64-512)), wide.Canvas.W-plain.Canvas.W)
	cell := blockScene(t, "---\nconfig:\n  block:\n    padding: 0\n---\nblock-beta\nA B\n", scene.ProfileCell)
	require.Equal(t, int32(1), cell.Boxes[1].Rect.X)
}

func TestBlockModelDumpCarriesColumnsAndSpans(t *testing.T) {
	in := blockInput(t, "block-beta\ncolumns 2\nA:2 B\nA --> B\nB --- A\n", scene.ProfileVector)
	var out bytes.Buffer
	require.NoError(t, WriteModelDump(&out, in))
	for _, want := range []string{`"kind":"block"`, `"shape":"composite;columns=2"`, `"shape":"rect;span=2"`, `"marker_end":"none"`} {
		require.Contains(t, out.String(), want)
	}
}

func TestBlockZeroPaddingRouteBetweenTouchingBlocksDrawsNothing(t *testing.T) {
	s := blockScene(t, "%%{init: {\"block\": {\"padding\": 0}}}%%\nblock-beta\ncolumns 2\nA B\nA --> B\n", scene.ProfileVector)
	require.Len(t, s.Routes[0].Points, 1)
	for _, group := range s.Groups {
		if group.Role == scene.GroupRoleEdge {
			require.Empty(t, group.Items)
		}
	}
}

func TestBlockLabelsStayStrictlyInsideTheFrames(t *testing.T) {
	for _, profile := range blockProfiles {
		blockScene(t, "block-beta\nA --> A\nB -- \"loop label\" --> B\nA --> B\nB --> A\n", profile)
		blockScene(t, "block-beta\ncolumns 3\na b c\na --> c\na -- \"x\" --> c\na -- \"y\" --> c\nb --> b\n", profile)
	}
}

func TestBlockEmptyDiagramHasOnlyMargins(t *testing.T) {
	s := blockScene(t, "block-beta\ncolumns 2\n", scene.ProfileVector)
	require.Equal(t, int32(512), s.Canvas.W)
	require.Equal(t, int32(512), s.Canvas.H)
	require.Len(t, s.Boxes, 1)
}

func TestBlockRoutesNeverCrossTheOtherBlocks(t *testing.T) {
	for _, profile := range blockProfiles {
		s := blockScene(t, "block-beta\ncolumns 3\nA B C\nD E F\nA --> C\nA --> F\nD --> B\nE --> E\n", profile)
		require.Len(t, s.Routes, 4)
	}
}
