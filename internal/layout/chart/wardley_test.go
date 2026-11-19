package chart_test

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/layout/chart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func wardleyOptions(profile scene.Profile) scene.Options {
	o := scene.DefaultOptions()
	o.Profile = profile
	return o
}

func layoutWardleyMap(t *testing.T, w *chart.Wardley, profile scene.Profile) scene.Scene {
	t.Helper()
	s, _, err := chart.LayoutWardley(t.Context(), w, wardleyOptions(profile))
	require.NoError(t, err)
	clause, failed, err := s.Validate()
	require.NoError(t, err)
	require.False(t, failed, clause.Message)
	return s
}

func richWardley() *chart.Wardley {
	return &chart.Wardley{
		Title:      "Tea",
		Stages:     []string{"Genesis", "Custom", "Product", "Commodity"},
		Boundaries: []int64{250, 500, 750, 1000},
		Nodes: []chart.WardleyNode{
			{Label: "Customer", X: 50000, Y: 90000, Anchor: true},
			{Label: "Cup", X: 40000, Y: 70000, Strategy: chart.WardleyBuild, Inertia: true},
			{Label: "Tea", X: 60000, Y: 50000, HasOffset: true, OffsetX: -16, OffsetY: 32, Strategy: chart.WardleyMarket},
			{Label: "Kettle", X: 45000, Y: 30000, PipelineParent: true},
			{Label: "Fire", X: 20000, Y: 30000},
			{Label: "Electric", X: 70000, Y: 30000},
		},
		Pipelines: []chart.WardleyPipeline{{Parent: 3, Children: []int{4, 5}}},
		Links: []chart.WardleyLink{
			{From: 0, To: 1, Flow: chart.WardleyForward},
			{From: 1, To: 2, Dashed: true, Label: "uses", Flow: chart.WardleyBackward},
			{From: 2, To: 4, Flow: chart.WardleyBidirectional},
		},
		Trends:         []chart.WardleyTrend{{Node: 1, TargetX: 85000, TargetY: 70000}},
		Notes:          []chart.WardleyNote{{Text: "note", X: 10000, Y: 10000}},
		Accelerators:   []chart.WardleyForce{{Name: "Cloud", X: 20000, Y: 20000}},
		Deaccelerators: []chart.WardleyForce{{Name: "Legacy", X: 60000, Y: 20000}},
		Annotations: []chart.WardleyAnnotation{
			{Number: 2, X: 40000, Y: 60000, Text: "second"},
			{Number: 1, X: 50000, Y: 40000, Text: "first"},
			{Number: 3, X: 70000, Y: 40000},
		},
		Box: &chart.WardleyPoint{X: 5000, Y: 95000},
	}
}

func TestWardleyDumpRoundTripsEveryFeature(t *testing.T) {
	want := richWardley()
	sk := want.Skeleton()
	dump := chart.WardleyDump{Routes: sk.Routes, Labels: sk.Labels, Regions: want.Regions()}
	got, err := chart.DecodeWardley(dump)
	require.NoError(t, err)
	require.Equal(t, want, got)
}

func TestWardleyDecodeRejectsMalformedDumps(t *testing.T) {
	good := richWardley()
	sk := good.Skeleton()
	cases := map[string]chart.WardleyDump{
		"unknown tag":       {Regions: [][]int{{99}}},
		"truncated node":    {Regions: [][]int{{1, 0, 0}}},
		"pipeline length":   {Regions: [][]int{{2, 0, 3, 1}}},
		"map stage count":   {Regions: [][]int{{0, 1, 2, 1000}}},
		"unknown strategy":  {Regions: [][]int{{1, 0, 9, 0, 0, 0, 0}}},
		"link beyond nodes": {Regions: good.Regions()[:1], Routes: sk.Routes[len(sk.Routes)-3:]},
	}
	for name, dump := range cases {
		_, err := chart.DecodeWardley(dump)
		require.Error(t, err, name)
	}
}

func TestWardleyProjectionPlacesNodesInTheInsetPlot(t *testing.T) {
	w := &chart.Wardley{Stages: []string{"A"}, Nodes: []chart.WardleyNode{{Label: "N", X: 25000, Y: 50000}, {Label: "Low", X: 0, Y: 0}, {Label: "High", X: 100000, Y: 100000}}}
	s := layoutWardleyMap(t, w, scene.ProfileVector)
	require.Equal(t, geom.Size{W: 57600, H: 38400}, s.Canvas)
	require.Equal(t, geom.Rect{X: 3072 + 12864, Y: 38400 - 3072 - 16128}, box(t, s, "n0").Rect)
	require.Equal(t, geom.Rect{X: 3072, Y: 38400 - 3072}, box(t, s, "n1").Rect)
	require.Equal(t, geom.Rect{X: 57600 - 3072, Y: 3072}, box(t, s, "n2").Rect)
	require.Equal(t, geom.Rect{X: 3072, Y: 3072, W: 57600 - 6144, H: 38400 - 6144}, box(t, s, "plot").Rect)
}

func TestWardleyCoordinatesBeyondTheMapAreClamped(t *testing.T) {
	w := &chart.Wardley{Stages: []string{"A"}, Nodes: []chart.WardleyNode{{Label: "Far", X: 250000, Y: 400000}}}
	s := layoutWardleyMap(t, w, scene.ProfileVector)
	require.Equal(t, geom.Rect{X: 57600 - 3072, Y: 3072}, box(t, s, "n0").Rect)
}

func TestWardleyConfigSizesTheCanvasPerProfile(t *testing.T) {
	w := &chart.Wardley{Stages: []string{"A"}}
	o := wardleyOptions(scene.ProfileVector)
	o.Config = []scene.Config{{Key: "height", Value: "300"}, {Key: "width", Value: "400"}}
	s, _, err := chart.LayoutWardley(t.Context(), w, o)
	require.NoError(t, err)
	require.Equal(t, geom.Size{W: 400 * 64, H: 300 * 64}, s.Canvas)
	o.Profile = scene.ProfileCell
	s, _, err = chart.LayoutWardley(t.Context(), w, o)
	require.NoError(t, err)
	require.Equal(t, geom.Size{W: 50, H: 19}, s.Canvas)
}

func TestWardleyConfigPaddingInsetsBothAxes(t *testing.T) {
	w := &chart.Wardley{Stages: []string{"A"}}
	o := wardleyOptions(scene.ProfileVector)
	o.Config = []scene.Config{{Key: "padding", Value: "20"}}
	s, _, err := chart.LayoutWardley(t.Context(), w, o)
	require.NoError(t, err)
	require.Equal(t, geom.Rect{X: 1280, Y: 1280, W: 57600 - 2560, H: 38400 - 2560}, box(t, s, "plot").Rect)
}

func TestWardleyTinyCanvasStillHoldsEveryBox(t *testing.T) {
	w := richWardley()
	o := wardleyOptions(scene.ProfileVector)
	o.Config = []scene.Config{{Key: "height", Value: "1"}, {Key: "width", Value: "1"}}
	s, _, err := chart.LayoutWardley(t.Context(), w, o)
	require.NoError(t, err)
	clause, failed, err := s.Validate()
	require.NoError(t, err)
	require.False(t, failed, clause.Message)
}

func TestWardleyPipelineFrameEnclosesChildrenAndParentSitsOnItsTopEdge(t *testing.T) {
	s := layoutWardleyMap(t, richWardley(), scene.ProfileVector)
	frame, parent := box(t, s, "pl0").Rect, box(t, s, "n3").Rect
	for _, id := range []string{"n4", "n5"} {
		at := box(t, s, id).Rect
		require.Equal(t, "pl0", box(t, s, id).Parent)
		require.LessOrEqual(t, frame.X, at.X)
		require.LessOrEqual(t, at.X, frame.X+frame.W)
		require.Less(t, frame.Y, at.Y)
		require.Less(t, at.Y, frame.Y+frame.H)
	}
	require.Equal(t, "plot", box(t, s, "n3").Parent)
	require.Less(t, parent.Y, frame.Y+frame.H/2)
	require.Equal(t, (box(t, s, "n4").Rect.X+box(t, s, "n5").Rect.X)/2, parent.X)
}

func TestWardleyPipelineLinksJoinChildrenInEvolutionOrder(t *testing.T) {
	s := layoutWardleyMap(t, richWardley(), scene.ProfileVector)
	var found bool
	for _, r := range s.Routes {
		if r.ID == "pl0.l0" {
			found = true
			require.Equal(t, "n4", r.From)
			require.Equal(t, "n5", r.To)
			require.Equal(t, "dotted", r.Stroke)
		}
	}
	require.True(t, found)
}

func markerCount(s scene.Scene, owner string) int {
	count := 0
	for _, g := range s.Groups {
		if g.Role != scene.GroupRoleEdge || g.Owner != owner {
			continue
		}
		for _, item := range g.Items {
			if _, ok := item.(*scene.MarkerRef); ok {
				count++
			}
		}
	}
	return count
}

func TestWardleyMarkersFollowFlowDirection(t *testing.T) {
	s := layoutWardleyMap(t, richWardley(), scene.ProfileVector)
	require.Equal(t, 1, markerCount(s, "l0"))
	require.Equal(t, 1, markerCount(s, "l1"))
	require.Equal(t, 2, markerCount(s, "l2"))
	require.Equal(t, 1, markerCount(s, "tr0"))
	require.Zero(t, markerCount(s, "pl0.l0"))
}

func TestWardleyAnnotationBoxStacksTextsByNumber(t *testing.T) {
	s := layoutWardleyMap(t, richWardley(), scene.ProfileVector)
	ab := box(t, s, "ab").Rect
	first, second := label(t, s, "an1.text"), label(t, s, "an0.text")
	require.Equal(t, "1. first", first.Text)
	require.Equal(t, "2. second", second.Text)
	require.Less(t, first.Rect.Y, second.Rect.Y)
	require.Equal(t, first.Rect.X, second.Rect.X)
	for _, l := range []scene.Label{first, second} {
		require.GreaterOrEqual(t, l.Rect.X, ab.X)
		require.LessOrEqual(t, l.Rect.X+l.Rect.W, ab.X+ab.W)
		require.GreaterOrEqual(t, l.Rect.Y, ab.Y)
		require.LessOrEqual(t, l.Rect.Y+l.Rect.H, ab.Y+ab.H)
	}
	require.Empty(t, label(t, s, "an2.text").Lines)
}

func TestWardleyAnnotationsWithoutABoxSitBesideTheirMarkers(t *testing.T) {
	w := richWardley()
	w.Box = nil
	s := layoutWardleyMap(t, w, scene.ProfileVector)
	for _, b := range s.Boxes {
		require.NotEqual(t, "ab", b.ID)
	}
	at, text := box(t, s, "an0").Rect, label(t, s, "an0.text")
	require.Equal(t, "an0", text.Owner)
	require.Greater(t, text.Rect.X, at.X)
}

func stageDividers(s scene.Scene) []int32 {
	var xs []int32
	for _, g := range s.Groups {
		if g.Role != scene.GroupRoleDecor {
			continue
		}
		for _, item := range g.Items {
			if path, ok := item.(*scene.Path); ok && path.Line == scene.LineDotted {
				xs = append(xs, path.Commands[0].(*scene.MoveTo).P.X)
			}
		}
	}
	return xs
}

func TestWardleyStageDividersFollowBoundaries(t *testing.T) {
	w := &chart.Wardley{Stages: []string{"a", "b", "c"}, Boundaries: []int64{100, 400, 1000}}
	s := layoutWardleyMap(t, w, scene.ProfileVector)
	plot := box(t, s, "plot").Rect
	require.Equal(t, []int32{plot.X + plot.W/10, plot.X + plot.W*4/10}, stageDividers(s))
	even := &chart.Wardley{Stages: []string{"a", "b", "c"}}
	s = layoutWardleyMap(t, even, scene.ProfileVector)
	require.Equal(t, int32(plot.X)+int32(int64(plot.W)/3), stageDividers(s)[0])
}

func symbolNames(s scene.Scene, owner string) []string {
	var names []string
	for _, g := range s.Groups {
		if g.Owner != owner {
			continue
		}
		for _, item := range g.Items {
			if sym, ok := item.(*scene.SymbolRef); ok {
				names = append(names, sym.Symbol)
			}
		}
	}
	return names
}

func TestWardleyCellProfileDrawsStrategySymbols(t *testing.T) {
	var nodes []chart.WardleyNode
	for i, strategy := range []chart.WardleyStrategy{chart.WardleyNoStrategy, chart.WardleyBuild, chart.WardleyBuy, chart.WardleyOutsource, chart.WardleyMarket} {
		nodes = append(nodes, chart.WardleyNode{Label: "n", X: int64(10000 + 15000*i), Y: 50000, Strategy: strategy})
	}
	nodes = append(nodes, chart.WardleyNode{Label: "anchor", X: 5000, Y: 80000, Anchor: true}, chart.WardleyNode{Label: "parent", X: 5000, Y: 20000, PipelineParent: true})
	s := layoutWardleyMap(t, &chart.Wardley{Stages: []string{"A"}, Nodes: nodes}, scene.ProfileCell)
	want := [][]string{{"ring"}, {"diamond-hollow"}, {"diamond"}, {"disc"}, {"bullseye"}, nil, {"box-hollow"}}
	for i, names := range want {
		require.Equal(t, names, symbolNames(s, "n"+string(rune('0'+i))), i)
	}
}

func TestWardleyVectorNodesAreCirclesWithStrategyHalos(t *testing.T) {
	nodes := []chart.WardleyNode{{Label: "plain", X: 10000, Y: 50000}, {Label: "bought", X: 30000, Y: 50000, Strategy: chart.WardleyBuy}, {Label: "bar", X: 50000, Y: 50000, Inertia: true}}
	s := layoutWardleyMap(t, &chart.Wardley{Stages: []string{"A"}, Nodes: nodes}, scene.ProfileVector)
	count := func(owner string, match func(scene.Primitive) bool) int {
		total := 0
		for _, g := range s.Groups {
			if g.Owner != owner {
				continue
			}
			for _, item := range g.Items {
				if match(item) {
					total++
				}
			}
		}
		return total
	}
	circles := func(p scene.Primitive) bool { _, ok := p.(*scene.Ellipse); return ok }
	bars := func(p scene.Primitive) bool { _, ok := p.(*scene.Polyline); return ok }
	require.Equal(t, 1, count("n0", circles))
	require.Equal(t, 2, count("n1", circles))
	require.Equal(t, 1, count("n2", bars))
	require.Zero(t, count("n0", bars))
}

func TestWardleyEmptyLabelsAreHiddenAndKeepNoLines(t *testing.T) {
	w := &chart.Wardley{Stages: []string{"A"}, Nodes: []chart.WardleyNode{{Label: "", X: 1000, Y: 1000}}}
	s := layoutWardleyMap(t, w, scene.ProfileVector)
	require.Empty(t, label(t, s, "n0.label").Lines)
	require.Equal(t, geom.Rect{}, label(t, s, "n0.label").Rect)
}

func TestWardleyEmptyMapStillLaysOut(t *testing.T) {
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		s := layoutWardleyMap(t, &chart.Wardley{}, profile)
		require.Len(t, s.Boxes, 1)
		require.Equal(t, "plot", s.Boxes[0].ID)
	}
}

func TestWardleyNodeLabelsFollowOffsetsAndAnchors(t *testing.T) {
	s := layoutWardleyMap(t, richWardley(), scene.ProfileVector)
	tea, at := label(t, s, "n2.label"), box(t, s, "n2").Rect
	require.Equal(t, at.X-16*64, tea.Rect.X+tea.Rect.W/2)
	require.Equal(t, at.Y+32*64, tea.Rect.Y+tea.Rect.H/2)
	customer, anchor := label(t, s, "n0.label"), box(t, s, "n0").Rect
	require.Equal(t, anchor.X, customer.Rect.X+customer.Rect.W/2)
	cup, cupAt := label(t, s, "n1.label"), box(t, s, "n1").Rect
	require.Greater(t, cup.Rect.X, cupAt.X)
	require.Equal(t, cupAt.Y, cup.Rect.Y+cup.Rect.H)
}
