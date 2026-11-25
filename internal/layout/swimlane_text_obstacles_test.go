package layout

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/stretchr/testify/require"
)

func swimlaneTextObstacleScene(rect geom.Rect, align scene.Align, text string) scene.Scene {
	options := scene.DefaultOptions()
	options.Profile = scene.ProfileCell
	return scene.Scene{
		Dump: scene.Dump{Kind: "swimlane", Options: options, Canvas: geom.Size{W: 60, H: 20}},
		Groups: []*scene.Group{{
			Role: scene.GroupRoleEdge, Owner: "edge",
			Items: []scene.Primitive{&scene.Text{
				Rect: rect, Align: align, Role: scene.TextRoleLabel,
				Lines: [][]scene.Run{{{Text: text}}},
			}},
		}},
	}
}

func TestSwimlaneTextObstaclesReservePositionedGlyphs(t *testing.T) {
	s := swimlaneTextObstacleScene(geom.Rect{X: 10, Y: 5, W: 20, H: 1}, scene.AlignMiddle, "A")
	router := bandRouter{scene: &s, axis: laneAxisX}
	obstacles, err := router.obstacles("A", "B")
	require.NoError(t, err)
	require.Equal(t, []obstacle{{cross0: 18, cross1: 21, rank0: 4, rank1: 7}}, obstacles)
	grid := routeGrid{obstacles: obstacles}
	require.True(t, grid.free(gridPoint{cross: 30, rank: 5}, gridPoint{cross: 31, rank: 5}),
		"unused text alignment space must not block a legitimate side-port stub")
}

func TestSwimlaneRejectsTextCrossingEndpointStubs(t *testing.T) {
	cases := []struct {
		name    string
		x       int32
		owner   string
		profile scene.Profile
	}{
		{"source/owned", 29, "edge", scene.ProfileCell},
		{"target/owned", 39, "edge", scene.ProfileCell},
		{"source/unrelated", 29, "other", scene.ProfileCell},
		{"target/unrelated", 39, "other", scene.ProfileCell},
		{"source/vector", 29, "edge", scene.ProfileVector},
		{"target/vector", 39, "edge", scene.ProfileVector},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			s := swimlaneTextObstacleScene(geom.Rect{X: tc.x, Y: 5, W: 1, H: 1}, scene.AlignStart, "X")
			s.Options.Profile = tc.profile
			s.Groups[0].Owner = tc.owner
			s.Boxes = []scene.Box{
				{ID: "A", Exclusive: true, Rect: geom.Rect{X: 25, Y: 2, W: 4, H: 6}},
				{ID: "B", Exclusive: true, Rect: geom.Rect{X: 40, Y: 2, W: 4, H: 6}},
			}
			s.Routes = []scene.Route{{
				ID: "edge", From: "A", To: "B", Orthogonal: true,
				Points: []geom.Point{{X: 29, Y: 5}, {X: 40, Y: 5}},
			}}
			router := bandRouter{scene: &s, axis: laneAxisY, slot: 2, bend: 4}
			err := router.route(&s.Routes[0], s.Routes[0].Points, 0, 0)
			if tc.profile == scene.ProfileCell {
				require.ErrorIs(t, err, geom.ErrDomain, "occupied cell at x=%d lies on an endpoint stub", tc.x)
			} else {
				require.NoError(t, err, "vector routing retains its boxes-only contract")
			}
		})
	}
}

func TestSwimlaneSidePortsPreserveAlignedNodeText(t *testing.T) {
	for _, direction := range []string{"LR", "RL"} {
		source := "swimlane-beta " + direction + "\nsubgraph Left[Left]\nA[Alpha]\nend\nsubgraph Right[Right]\nB[Beta]\nend\nA --> B\n"
		text := renderDecorationCells(t, source)
		require.Contains(t, text, "Alpha")
		require.Contains(t, text, "Beta")
	}
}
