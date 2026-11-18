package lanes

import (
	"slices"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func sized(w, h int32) Text {
	return Text{Lines: []measure.StyledLine{{Text: "t", Width: w}}, W: w, H: h, Role: scene.TextRoleLabel}
}

func eventLanes(indices ...int) []EventLane {
	out := make([]EventLane, len(indices))
	for i, index := range indices {
		out[i] = EventLane{ID: "lane", Index: index}
	}
	return out
}

func planEvents(t *testing.T, in EventModelingInput, profile scene.Profile) EventModelingResult {
	t.Helper()
	res, err := EventModeling(in, Params{Profile: profile})
	require.NoError(t, err)
	return res
}

func frameLanes(lanes ...int) []EventFrame {
	out := make([]EventFrame, len(lanes))
	for i, lane := range lanes {
		out[i] = EventFrame{Lane: lane}
	}
	return out
}

func TestEventColumnsKeepSameLaneBoxesDisjoint(t *testing.T) {
	res := planEvents(t, EventModelingInput{Lanes: eventLanes(0, 100, 200), Frames: frameLanes(0, 1, 2, 0, 1)}, scene.ProfileVector)
	x := make([]int32, len(res.Frames))
	y := make([]int32, len(res.Frames))
	for i, rect := range res.Frames {
		x[i], y[i] = rect.X, rect.Y
	}
	require.Equal(t, []int32{17024, 18944, 20864, 24064, 25984}, x)
	require.Equal(t, []int32{1984, 10944, 19904, 1984, 10944}, y)
	require.LessOrEqual(t, x[0]+res.Frames[0].W, x[3])
	require.LessOrEqual(t, x[1]+res.Frames[1].W, x[4])
}

func TestEventLanesStackWithGapsAndGrowToTheirTallestBox(t *testing.T) {
	tall := frameLanes(0, 1)
	tall[1].Name = sized(100, 100000)
	res := planEvents(t, EventModelingInput{Lanes: eventLanes(0, 100), Frames: tall}, scene.ProfileVector)
	require.Equal(t, int32(8320), res.Lanes[0].H)
	require.Equal(t, int32(48000+1280+1920), res.Lanes[1].H)
	require.Equal(t, res.Lanes[0].Y+res.Lanes[0].H+640, res.Lanes[1].Y)
	require.Equal(t, int32(48000+1280), res.Frames[1].H)
	require.Equal(t, res.Lanes[1].Y+960, res.Frames[1].Y)
	require.Equal(t, res.Lanes[0].W, res.Lanes[1].W)
}

func TestEventLaneOrderFollowsIndexThenPosition(t *testing.T) {
	in := EventModelingInput{Lanes: eventLanes(200, 0, 0), Frames: frameLanes(0, 1, 2)}
	res := planEvents(t, in, scene.ProfileCell)
	require.Less(t, res.Lanes[1].Y, res.Lanes[2].Y)
	require.Less(t, res.Lanes[2].Y, res.Lanes[0].Y)
}

func TestEventFrameSizeClampsAndAddsDataBlock(t *testing.T) {
	data := sized(50000, 2*1280)
	in := EventModelingInput{Lanes: eventLanes(0), Frames: []EventFrame{{Name: sized(100, 1280)}, {Name: sized(6000, 1280), Data: &data}}}
	res := planEvents(t, in, scene.ProfileVector)
	require.Equal(t, int32(5120+1280), res.Frames[0].W)
	require.Equal(t, int32(5120+1280), res.Frames[0].H)
	require.Equal(t, int32(28800+1280), res.Frames[1].W)
	require.Equal(t, int32(5120+1280), res.Frames[1].H)
}

func TestEventGutterWidensForLongLaneLabels(t *testing.T) {
	label := sized(20000, 1280)
	lanes := eventLanes(0)
	lanes[0].Label = &label
	res := planEvents(t, EventModelingInput{Lanes: lanes, Frames: frameLanes(0)}, scene.ProfileVector)
	require.Equal(t, int32(23840+1024), res.Frames[0].X)
	require.Equal(t, int32(1920+1024), res.LaneLabels[0].X)
	require.LessOrEqual(t, res.LaneLabels[0].X+res.LaneLabels[0].W, res.Frames[0].X-1920)
}

func TestEventAdjacentLanesDrawOneStraightSegmentInVectorAndACorridorInCells(t *testing.T) {
	in := EventModelingInput{Lanes: eventLanes(0, 100), Frames: frameLanes(0, 1), Relations: []EventRelation{{From: 0, To: 1}}}
	vector := planEvents(t, in, scene.ProfileVector)
	require.Equal(t, []geom.Point{{X: 21290, Y: 8384}, {X: 21077, Y: 10944}}, vector.Routes[0])
	cell := planEvents(t, in, scene.ProfileCell)
	require.Equal(t, []geom.Point{{X: 34, Y: 9}, {X: 34, Y: 10}, {X: 35, Y: 10}, {X: 35, Y: 12}}, cell.Routes[0])
}

func TestEventUpwardRelationStartsAtTheSourceTopAndEndsAtTheTargetBottom(t *testing.T) {
	in := EventModelingInput{Lanes: eventLanes(0, 100), Frames: frameLanes(1, 0), Relations: []EventRelation{{From: 0, To: 1}}}
	res := planEvents(t, in, scene.ProfileVector)
	route := res.Routes[0]
	require.Equal(t, res.Frames[0].Y, route[0].Y)
	require.Equal(t, res.Frames[1].Y+res.Frames[1].H, route[len(route)-1].Y)
}

func TestEventRelationAroundABoxInTheWayStaysOrthogonalAndClear(t *testing.T) {
	in := EventModelingInput{Lanes: eventLanes(0, 100, 200), Frames: frameLanes(0, 1, 2), Relations: []EventRelation{{From: 0, To: 2}}}
	res := planEvents(t, in, scene.ProfileVector)
	want := []geom.Point{{X: 21290, Y: 8384}, {X: 21290, Y: 9664}, {X: 27904, Y: 9664}, {X: 27904, Y: 18624}, {X: 22997, Y: 18624}, {X: 22997, Y: 19904}}
	require.Equal(t, want, res.Routes[0])
	require.True(t, geom.IsOrthogonal(res.Routes[0]))
	hit, err := geom.PolylineHitsRect(res.Routes[0], res.Frames[1])
	require.NoError(t, err)
	require.False(t, hit)
}

func TestEventSameLaneRelationLoopsAboveTheLane(t *testing.T) {
	in := EventModelingInput{Lanes: eventLanes(0), Frames: frameLanes(0, 0), Relations: []EventRelation{{From: 0, To: 1}}}
	res := planEvents(t, in, scene.ProfileVector)
	want := []geom.Point{{X: 21290, Y: 1984}, {X: 21290, Y: 1504}, {X: 26197, Y: 1504}, {X: 26197, Y: 1984}}
	require.Equal(t, want, res.Routes[0])
}

func TestEventSelfRelationIsAClosedLoopOnTheTopEdge(t *testing.T) {
	in := EventModelingInput{Lanes: eventLanes(0), Frames: frameLanes(0), Relations: []EventRelation{{From: 0, To: 0}}}
	res := planEvents(t, in, scene.ProfileCell)
	route := res.Routes[0]
	require.Len(t, route, 4)
	require.Equal(t, res.Frames[0].Y, route[0].Y)
	require.Equal(t, res.Frames[0].Y, route[3].Y)
	require.Less(t, route[1].Y, route[0].Y)
}

func TestEventEndpointsLieOnTheirBoxBoundaries(t *testing.T) {
	in := EventModelingInput{Lanes: eventLanes(0, 100, 200), Frames: frameLanes(0, 1, 2, 1, 0), Relations: []EventRelation{{From: 0, To: 1}, {From: 2, To: 0}, {From: 4, To: 3}, {From: 3, To: 3}}}
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		res := planEvents(t, in, profile)
		for i, relation := range in.Relations {
			route := res.Routes[i]
			require.True(t, onBoundary(route[0], res.Frames[relation.From]), "%v %d start", profile, i)
			require.True(t, onBoundary(route[len(route)-1], res.Frames[relation.To]), "%v %d end", profile, i)
		}
	}
}

func onBoundary(p geom.Point, r geom.Rect) bool {
	inside := p.X >= r.X && p.X <= r.X+r.W && p.Y >= r.Y && p.Y <= r.Y+r.H
	return inside && (p.X == r.X || p.X == r.X+r.W || p.Y == r.Y || p.Y == r.Y+r.H)
}

func TestEventCanvasContainsEveryRect(t *testing.T) {
	label := sized(3000, 2560)
	lanes := eventLanes(0, 100)
	lanes[1].Label = &label
	res := planEvents(t, EventModelingInput{Lanes: lanes, Frames: frameLanes(0, 1, 0), Relations: []EventRelation{{From: 0, To: 1}}}, scene.ProfileVector)
	for _, rect := range slices.Concat(res.Lanes, res.Frames, res.LaneLabels) {
		require.GreaterOrEqual(t, rect.X, int32(0))
		require.GreaterOrEqual(t, rect.Y, int32(0))
		require.LessOrEqual(t, rect.X+rect.W, res.Canvas.W)
		require.LessOrEqual(t, rect.Y+rect.H, res.Canvas.H)
	}
}

func TestEventInputIndicesAreChecked(t *testing.T) {
	_, err := EventModeling(EventModelingInput{Lanes: eventLanes(0), Frames: frameLanes(1)}, Params{Profile: scene.ProfileCell})
	require.ErrorIs(t, err, geom.ErrDomain)
	_, err = EventModeling(EventModelingInput{Lanes: eventLanes(0), Frames: frameLanes(0), Relations: []EventRelation{{From: 0, To: 1}}}, Params{Profile: scene.ProfileCell})
	require.ErrorIs(t, err, geom.ErrDomain)
}

func TestEventEmptyInputHasAMarginOnlyCanvas(t *testing.T) {
	res := planEvents(t, EventModelingInput{}, scene.ProfileCell)
	require.Equal(t, geom.Size{W: 2, H: 2}, res.Canvas)
}

func TestEventPaintOrderAndStyles(t *testing.T) {
	lanes := eventLanes(0, 100)
	lanes[1].ID = ""
	in := EventModelingInput{Lanes: lanes, Frames: []EventFrame{{ID: "a", Category: "ui"}, {ID: "b", Lane: 1, Category: "command"}}, Relations: []EventRelation{{ID: "e0", From: 0, To: 1}}}
	res := planEvents(t, in, scene.ProfileVector)
	roles := make([]scene.GroupRole, len(res.Groups))
	for i, group := range res.Groups {
		roles[i] = group.Role
	}
	require.Equal(t, []scene.GroupRole{scene.GroupRoleGroup, scene.GroupRoleEdge, scene.GroupRoleNode, scene.GroupRoleNode}, roles)
	require.Equal(t, "lane", res.Groups[0].Owner)
	require.Equal(t, "e0", res.Groups[1].Owner)
	require.Equal(t, "node", res.Groups[2].Items[0].(*scene.RoundRect).Style)
	require.Equal(t, "note", res.Groups[3].Items[0].(*scene.RoundRect).Style)
	marker := res.Groups[1].Items[1].(*scene.MarkerRef)
	require.Equal(t, "point", marker.Marker)
	require.Equal(t, res.Routes[0][len(res.Routes[0])-1], marker.At)
}
