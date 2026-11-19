package layered

import (
	"fmt"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/stretchr/testify/require"
)

func exactFootprintInput(side int32, loops int, labelled bool) Input {
	ids := []string{"unrelated", "fixed", "a", "b", "c", "d"}
	in := Input{Kind: "state", Exact: make([]bool, len(ids)), Sizes: make([]geom.Size, len(ids))}
	for _, id := range ids {
		in.Boxes = append(in.Boxes, scene.Box{ID: id, Role: scene.RoleNode, Exclusive: true})
		in.Text = append(in.Text, "")
	}
	in.Exact[1], in.Sizes[1] = true, geom.Size{W: side, H: side}
	add := func(to string, label bool) {
		id := fmt.Sprintf("e%d", len(in.Routes))
		if label {
			in.Labels = append(in.Labels, scene.Label{ID: id + ".label", Owner: id, Text: "loop label"})
		}
		in.Routes = append(in.Routes, scene.Route{ID: id, From: "fixed", To: to, Orthogonal: true})
		in.Edges = append(in.Edges, EdgeOptions{MinLength: 1})
	}
	for _, to := range []string{"a", "b", "c", "d"} {
		add(to, false)
	}
	for range loops {
		add("fixed", labelled)
	}
	return in
}

type exactCase struct {
	profile  scene.Profile
	dir      scene.Direction
	loops    int
	labelled bool
}

func (c exactCase) side() int32 {
	if c.profile == scene.ProfileCell {
		return 1
	}
	return 896
}

func (c exactCase) name() string {
	return fmt.Sprintf("%v/%v/%d/%v", c.profile, c.dir, c.loops, c.labelled)
}

func exactCases() []exactCase {
	var cases []exactCase
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		for _, d := range []scene.Direction{scene.DirectionTB, scene.DirectionBT, scene.DirectionLR, scene.DirectionRL} {
			cases = append(cases, exactLoopCases(profile, d)...)
		}
	}
	return cases
}

func exactLoopCases(profile scene.Profile, d scene.Direction) []exactCase {
	var cases []exactCase
	for _, loops := range []int{0, 1, 3} {
		for _, labelled := range []bool{false, true} {
			cases = append(cases, exactCase{profile: profile, dir: d, loops: loops, labelled: labelled})
		}
	}
	return cases
}

func fixedBox(boxes []scene.Box) scene.Box {
	var fixed scene.Box
	for _, b := range boxes {
		if b.ID == "fixed" {
			fixed = b
		}
	}
	return fixed
}

func (c exactCase) requireBoundaryStarts(t *testing.T, routes []scene.Route, fixed scene.Box) {
	t.Helper()
	side := c.side()
	for _, r := range routes {
		if r.From != "fixed" {
			continue
		}
		first := r.Points[0]
		onX := first.X == fixed.Rect.X || first.X == fixed.Rect.X+side
		onY := first.Y == fixed.Rect.Y || first.Y == fixed.Rect.Y+side
		require.True(t, onX || onY, "%s route %s starts off the boundary: %v", c.name(), r.ID, first)
	}
}

func (c exactCase) check(t *testing.T) {
	t.Helper()
	side, name := c.side(), c.name()
	o := scene.DefaultOptions()
	o.Profile, o.Direction, o.Thoroughness = c.profile, c.dir, 1
	s, err := LayoutFamily(exactFootprintInput(side, c.loops, c.labelled), Options{Scene: o})
	require.NoError(t, err, name)
	fixed := fixedBox(s.Boxes)
	require.Equal(t, geom.Size{W: side, H: side}, geom.Size{W: fixed.Rect.W, H: fixed.Rect.H}, name)
	ok, err := s.Check()
	require.NoError(t, err, name)
	require.True(t, ok, name)
	c.requireBoundaryStarts(t, s.Routes, fixed)
}

func TestExactFootprintSurvivesPortsLoopsAndOrientation(t *testing.T) {
	for _, c := range exactCases() {
		c.check(t)
	}
}
