package grid

import (
	"slices"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/geom"
)

func archParams() ArchParams {
	return ArchParams{
		PitchX: 7680, PitchY: 7680, LabelWrap: 7168, IconW: 5120, IconH: 5120,
		Padding: 2560, LineHeight: 1280, Badge: 1536, Inset: 768, LabelGap: 256,
		Margin: 1024, Fuel: 2000, RingCap: 4,
	}
}

func archNode(parent int) ArchNode {
	return ArchNode{Parent: parent, Icon: geom.Size{W: 5120, H: 5120}}
}

func archEdge(from, to int, fromSide, toSide geom.Side) ArchEdge {
	return ArchEdge{From: from, To: to, FromSide: fromSide, ToSide: toSide}
}

func TestArchitectureChainFollowsEdgeSides(t *testing.T) {
	in := ArchInput{
		Nodes: []ArchNode{archNode(-1), archNode(-1), archNode(-1)},
		Edges: []ArchEdge{archEdge(0, 1, geom.SideRight, geom.SideLeft), archEdge(1, 2, geom.SideBottom, geom.SideTop)},
	}
	out, err := Architecture(in, archParams())
	require.NoError(t, err)
	a, b, c := out.Boxes[0], out.Boxes[1], out.Boxes[2]
	require.Equal(t, a.Y, b.Y)
	require.Equal(t, int32(7680), b.X-a.X)
	require.Equal(t, b.X, c.X)
	require.Equal(t, int32(7680), c.Y-b.Y)
}

func TestArchitectureRoutesUseGutterLines(t *testing.T) {
	in := ArchInput{
		Nodes: []ArchNode{archNode(-1), archNode(-1)},
		Edges: []ArchEdge{archEdge(0, 1, geom.SideRight, geom.SideLeft)},
	}
	out, err := Architecture(in, archParams())
	require.NoError(t, err)
	route := out.Routes[0]
	require.Len(t, route, 3)
	a, b := out.Boxes[0], out.Boxes[1]
	require.Equal(t, geom.Point{X: a.X + a.W, Y: a.Y + a.H/2}, route[0])
	require.Equal(t, geom.Point{X: b.X, Y: b.Y + b.H/2}, route[2])
	require.Equal(t, route[1].Y, route[0].Y)
	require.Equal(t, route[1].Y, route[2].Y)
}

func TestArchitecturePerpendicularRouteHasOneElbow(t *testing.T) {
	in := ArchInput{
		Nodes: []ArchNode{archNode(-1), archNode(-1)},
		Edges: []ArchEdge{archEdge(0, 1, geom.SideRight, geom.SideTop)},
	}
	out, err := Architecture(in, archParams())
	require.NoError(t, err)
	require.Len(t, out.Routes[0], 5)
	for i := 0; i+1 < len(out.Routes[0]); i++ {
		p, q := out.Routes[0][i], out.Routes[0][i+1]
		require.True(t, p.X == q.X || p.Y == q.Y)
	}
}

func TestArchitecturePortsSpreadAlongOneSide(t *testing.T) {
	in := ArchInput{
		Nodes: []ArchNode{archNode(-1), archNode(-1), archNode(-1)},
		Edges: []ArchEdge{archEdge(0, 1, geom.SideRight, geom.SideLeft), archEdge(0, 2, geom.SideRight, geom.SideLeft)},
	}
	out, err := Architecture(in, archParams())
	require.NoError(t, err)
	first, second := out.Routes[0][0], out.Routes[1][0]
	icon := out.Icons[0]
	require.Equal(t, first.X, second.X)
	require.Equal(t, icon.Y+icon.H/3, first.Y)
	require.Equal(t, icon.Y+2*icon.H/3, second.Y)
}

func TestArchitectureGroupFramesAreDisjointAndContainMembers(t *testing.T) {
	in := ArchInput{
		Groups: []ArchGroup{{Parent: -1, Title: geom.Size{W: 2560, H: 1280}, Icon: true}, {Parent: -1}, {Parent: 0}},
		Nodes:  []ArchNode{archNode(0), archNode(1), archNode(2), archNode(-1)},
		Edges:  []ArchEdge{archEdge(0, 1, geom.SideRight, geom.SideLeft), archEdge(1, 2, geom.SideRight, geom.SideLeft), archEdge(2, 3, geom.SideBottom, geom.SideTop)},
	}
	out, err := Architecture(in, archParams())
	require.NoError(t, err)
	frames := out.Frames
	require.False(t, rectsOverlap(frames[0], frames[1]))
	require.True(t, strictContains(frames[0], frames[2]))
	require.True(t, strictContains(frames[0], out.Boxes[0]))
	require.True(t, strictContains(frames[1], out.Boxes[1]))
	require.True(t, strictContains(frames[2], out.Boxes[2]))
	require.False(t, rectsOverlap(frames[0], out.Boxes[3]))
	require.False(t, rectsOverlap(frames[1], out.Boxes[3]))
	title := out.Titles[0]
	require.True(t, strictContains(frames[0], title))
	require.Equal(t, int32(1536), out.GroupIcons[0].W)
}

func TestArchitectureEmptyGroupKeepsAFrame(t *testing.T) {
	in := ArchInput{Groups: []ArchGroup{{Parent: -1}}, Nodes: []ArchNode{archNode(-1)}}
	out, err := Architecture(in, archParams())
	require.NoError(t, err)
	require.Greater(t, out.Frames[0].W, int32(0))
	require.False(t, rectsOverlap(out.Frames[0], out.Boxes[0]))
}

func TestArchitectureAlignForcesOneRow(t *testing.T) {
	in := ArchInput{
		Nodes:  []ArchNode{archNode(-1), archNode(-1), archNode(-1)},
		Edges:  []ArchEdge{archEdge(0, 1, geom.SideRight, geom.SideLeft), archEdge(1, 2, geom.SideBottom, geom.SideTop)},
		Aligns: []ArchAlign{{Members: []int{0, 2}}},
	}
	out, err := Architecture(in, archParams())
	require.NoError(t, err)
	require.Equal(t, out.Boxes[0].Y, out.Boxes[2].Y)
	free := in
	free.Aligns = nil
	loose, err := Architecture(free, archParams())
	require.NoError(t, err)
	require.NotEqual(t, loose.Boxes[0].Y, loose.Boxes[2].Y)
}

func TestArchitectureDisconnectedComponentsSitRightOfTheFirst(t *testing.T) {
	in := ArchInput{Nodes: []ArchNode{archNode(-1), archNode(-1)}}
	out, err := Architecture(in, archParams())
	require.NoError(t, err)
	require.Equal(t, out.Boxes[0].Y, out.Boxes[1].Y)
	require.Equal(t, int32(2*7680), out.Boxes[1].X-out.Boxes[0].X)
}

func TestArchitectureLabelsWidenThePitch(t *testing.T) {
	in := ArchInput{Nodes: []ArchNode{archNode(-1), archNode(-1), archNode(-1)}}
	in.Nodes[0].Label = geom.Size{W: 9000, H: 2560}
	out, err := Architecture(in, archParams())
	require.NoError(t, err)
	require.GreaterOrEqual(t, out.Boxes[1].X-out.Boxes[0].X, int32(9000+7680-7168))
	label := out.Labels[0]
	require.Equal(t, out.Icons[0].Y+out.Icons[0].H, label.Y)
	require.Equal(t, out.Boxes[0].H, out.Icons[0].H+label.H)
}

func TestArchitectureEdgeLabelsStayOffNodes(t *testing.T) {
	in := ArchInput{
		Nodes: []ArchNode{archNode(-1), archNode(-1)},
		Edges: []ArchEdge{{From: 0, To: 1, FromSide: geom.SideRight, ToSide: geom.SideLeft, Label: geom.Size{W: 2560, H: 1280}}},
	}
	out, err := Architecture(in, archParams())
	require.NoError(t, err)
	label := out.EdgeLabels[0]
	require.Equal(t, int32(2560), label.W)
	for _, box := range out.Boxes {
		require.False(t, rectsOverlap(label, box))
	}
}

func TestArchitectureFuelStopsTheQueueAndSeedsTheRest(t *testing.T) {
	in := ArchInput{
		Nodes: []ArchNode{archNode(-1), archNode(-1), archNode(-1)},
		Edges: []ArchEdge{archEdge(0, 1, geom.SideRight, geom.SideLeft), archEdge(1, 2, geom.SideRight, geom.SideLeft)},
	}
	p := archParams()
	p.Fuel = 1
	out, err := Architecture(in, p)
	require.NoError(t, err)
	require.True(t, out.Budget)
	require.Len(t, out.Boxes, 3)
	for i := range out.Boxes {
		for j := i + 1; j < len(out.Boxes); j++ {
			require.False(t, rectsOverlap(out.Boxes[i], out.Boxes[j]))
		}
	}
}

func TestArchitectureRejectsInvalidInput(t *testing.T) {
	good := ArchInput{Nodes: []ArchNode{archNode(-1), archNode(-1)}, Edges: []ArchEdge{archEdge(0, 1, geom.SideRight, geom.SideLeft)}}
	cases := map[string]func(in *ArchInput, p *ArchParams){
		"node parent":  func(in *ArchInput, _ *ArchParams) { in.Nodes[0].Parent = 3 },
		"group parent": func(in *ArchInput, _ *ArchParams) { in.Groups = []ArchGroup{{Parent: 0}} },
		"edge end":     func(in *ArchInput, _ *ArchParams) { in.Edges[0].To = 9 },
		"edge side":    func(in *ArchInput, _ *ArchParams) { in.Edges[0].FromSide = geom.SideNone },
		"align member": func(in *ArchInput, _ *ArchParams) { in.Aligns = []ArchAlign{{Members: []int{0, 7}}} },
		"pitch":        func(_ *ArchInput, p *ArchParams) { p.PitchX = 0 },
		"gutter":       func(_ *ArchInput, p *ArchParams) { p.Gutter = 2 },
	}
	for name, mutate := range cases {
		in, p := good, archParams()
		in.Nodes, in.Edges = slices.Clone(good.Nodes), slices.Clone(good.Edges)
		mutate(&in, &p)
		_, err := Architecture(in, p)
		require.ErrorIs(t, err, geom.ErrDomain, name)
	}
}

func TestArchitectureOverflowIsReported(t *testing.T) {
	in := ArchInput{Nodes: []ArchNode{archNode(-1)}}
	in.Nodes[0].Label = geom.Size{W: int32(geom.CoordLimit), H: 1280}
	_, err := Architecture(in, archParams())
	require.ErrorIs(t, err, geom.ErrOverflow)
}

func rectsOverlap(a, b geom.Rect) bool {
	return a.X < b.X+b.W && b.X < a.X+a.W && a.Y < b.Y+b.H && b.Y < a.Y+a.H
}

func strictContains(outer, inner geom.Rect) bool {
	return outer.X < inner.X && inner.X+inner.W < outer.X+outer.W && outer.Y < inner.Y && inner.Y+inner.H < outer.Y+outer.H
}
