package layout

import (
	"slices"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func sequenceScene(t *testing.T, src string, profile scene.Profile) scene.Scene {
	t.Helper()
	d := ParseDiagram([]byte(src))
	require.Empty(t, d.Diagnostics)
	in, err := d.Input(profile, scene.Options{})
	require.NoError(t, err)
	s, _, err := Layout(in)
	require.NoError(t, err)
	return s
}

var sequenceProfiles = []scene.Profile{scene.ProfileVector, scene.ProfileCell}

func decorBars(s scene.Scene) []geom.Rect {
	var rects []geom.Rect
	for _, group := range s.Groups {
		if group.Role != scene.GroupRoleDecor {
			continue
		}
		for _, item := range group.Items {
			switch item := item.(type) {
			case *scene.Rect:
				rects = append(rects, item.Rect)
			case *scene.Polyline:
				first, last := item.Points[0], item.Points[len(item.Points)-1]
				rects = append(rects, geom.Rect{X: first.X, Y: first.Y, W: 1, H: last.Y - first.Y + 1})
			}
		}
	}
	slices.SortFunc(rects, func(a, b geom.Rect) int {
		if a.X != b.X {
			return int(a.X - b.X)
		}
		return int(a.Y - b.Y)
	})
	return rects
}

func TestSequenceWideningSplitsWithFloorDivisionAndLeadingRemainder(t *testing.T) {
	for _, c := range []struct {
		gaps        []int32
		from, to    int
		need        int32
		want        []int32
		description string
	}{
		{[]int32{10, 10}, 0, 2, 35, []int32{18, 17}, "odd remainder goes to the first gap"},
		{[]int32{10, 10}, 0, 2, 36, []int32{18, 18}, "even split"},
		{[]int32{5}, 0, 1, 40, []int32{40}, "single gap takes the whole shortfall"},
		{[]int32{10}, 0, 1, 5, []int32{10}, "a wide enough gap is unchanged"},
	} {
		gaps := slices.Clone(c.gaps)
		widen(gaps, c.from, c.to, c.need)
		require.Equal(t, c.want, gaps, c.description)
	}
}

func TestSequenceCentresKeepDeclarationOrder(t *testing.T) {
	require.Equal(t, []int32{15, 40}, lifelineCentres([]int32{30, 20}, []int32{25}))
}

func TestSequenceActivationOffsetMovesByHalfWidthPerDepth(t *testing.T) {
	src := "sequenceDiagram\nparticipant A\nparticipant B\nA->>+B: one\nA->>+B: two\nB-->>-A: three\nB-->>-A: four\n"
	bars := decorBars(sequenceScene(t, src, scene.ProfileVector))
	require.Len(t, bars, 2)
	require.Equal(t, int32(320), bars[1].X-bars[0].X)
	require.Less(t, bars[0].Y, bars[1].Y)
	require.Less(t, bars[1].Y+bars[1].H, bars[0].Y+bars[0].H)
}

func TestSequenceUnclosedActivationExtendsToTheLastRow(t *testing.T) {
	src := "sequenceDiagram\nloop L\nA->>+B: one\nend\nA->>B: two\n"
	for _, profile := range sequenceProfiles {
		s := sequenceScene(t, src, profile)
		bars := decorBars(s)
		require.Len(t, bars, 1)
		require.Positive(t, bars[0].H)
		ok, err := s.Check()
		require.NoError(t, err)
		require.True(t, ok, profile.String())
	}
}

func TestSequenceDestroyedActorKeepsItsHeaderAndEndsItsLifeline(t *testing.T) {
	src := "sequenceDiagram\nA->>B: one\ndestroy B\nA-xB: two\nA->>A: three\n"
	for _, profile := range sequenceProfiles {
		s := sequenceScene(t, src, profile)
		rects := map[string]geom.Rect{}
		for _, box := range s.Boxes {
			rects[box.ID] = box.Rect
		}
		require.Equal(t, rects["A"].Y, rects["B"].Y, "both headers share the top band")
		crosses := 0
		for _, group := range s.Groups {
			for _, item := range group.Items {
				if marker, ok := item.(*scene.MarkerRef); ok && marker.Axis == scene.AxisPlusY {
					crosses++
				}
			}
		}
		require.Equal(t, 1, crosses, "one destroy cross")
		ok, err := s.Check()
		require.NoError(t, err)
		require.True(t, ok, profile.String())
	}
}

func TestSequenceParticipantBoxTitleAndElseTitlesGetRects(t *testing.T) {
	src := "sequenceDiagram\nbox Team Name\nparticipant A\nend\nalt first\nA->>A: x\nelse a long second title\nA->>A: y\nend\n"
	for _, profile := range sequenceProfiles {
		s := sequenceScene(t, src, profile)
		var frame geom.Rect
		var section geom.Rect
		for _, box := range s.Boxes {
			if box.ID == "f0" {
				frame = box.Rect
			}
		}
		for _, label := range s.Labels {
			if label.ID == "f0.s0" {
				section = label.Rect
			}
			require.True(t, label.Rect.W > 0 && label.Rect.H > 0, "%s: %s", profile, label.ID)
		}
		require.Greater(t, section.X, frame.X)
		require.Less(t, section.X+section.W, frame.X+frame.W)
		ok, err := s.Check()
		require.NoError(t, err)
		require.True(t, ok, profile.String())
	}
}

func TestSequenceLifelineCentresAreOneGapApart(t *testing.T) {
	s := sequenceScene(t, "sequenceDiagram\nA->>B: x\n", scene.ProfileVector)
	centre := map[string]int32{}
	for _, box := range s.Boxes {
		centre[box.ID] = box.Rect.X + half(box.Rect.W)
	}
	require.Equal(t, int32(9600+3200), centre["B"]-centre["A"])
}

func TestSequenceSceneValidatesUnderBothProfiles(t *testing.T) {
	src := "sequenceDiagram\nparticipant Alice as Alice\nparticipant Bob\nautonumber 5\nAlice->>+Bob: Request\nBob-->>-Alice: Reply\nNote right of Bob: thinking\nloop every day\nAlice->>Bob: ping\nend\nbox Team\nparticipant Carol\nend\n"
	for _, profile := range sequenceProfiles {
		s := sequenceScene(t, src, profile)
		ok, err := s.Check()
		require.NoError(t, err)
		require.True(t, ok, profile.String())
	}
}

func TestSequenceModelDumpCarriesNoCoordinates(t *testing.T) {
	d := ParseDiagram([]byte("sequenceDiagram\nA->>B: hi\n"))
	in, err := d.Input(scene.ProfileVector, scene.Options{})
	require.NoError(t, err)
	require.Equal(t, "sequence", in.Kind)
	require.Len(t, in.RegionSets, 1)
	require.Len(t, in.Routes, 1)
	require.Equal(t, []string{"e0.label"}, []string{in.Labels[0].ID})
}

func centresByID(s scene.Scene) map[string]int32 {
	centres := map[string]int32{}
	for _, box := range s.Boxes {
		centres[box.ID] = box.Rect.X + half(box.Rect.W)
	}
	return centres
}

func TestSequenceMessageLabelsFollowTheirRoutesAfterAnEmptyMessage(t *testing.T) {
	src := "sequenceDiagram\nparticipant A\nparticipant B\nparticipant C\nA->>B:\nB->>C: a deliberately long message label\n"
	for _, profile := range sequenceProfiles {
		s := sequenceScene(t, src, profile)
		c, err := loadSequenceConstants(profile)
		require.NoError(t, err)
		var label scene.Label
		for _, l := range s.Labels {
			if l.Owner == "e1" {
				label = l
			}
		}
		require.Positive(t, label.Rect.W, profile.String())
		centre := centresByID(s)
		base := half(2*sequenceActorWidth(t, profile)) + c.actorMargin
		require.Equal(t, base, centre["B"]-centre["A"], "%s: an empty message widens nothing", profile)
		require.GreaterOrEqual(t, centre["C"]-centre["B"], label.Rect.W+2*c.wrapPadding+c.actorMargin, profile.String())
		require.Equal(t, half(centre["B"]+centre["C"])-half(label.Rect.W), label.Rect.X, profile.String())
		first := s.Routes[0].Points
		require.Equal(t, 2*c.boxMargin+c.messageTop, first[1].Y-first[0].Y, "%s: an empty message row holds no label line", profile)
	}
}

func sequenceActorWidth(t *testing.T, profile scene.Profile) int32 {
	t.Helper()
	width, ok := layoutConstant(profile, "sequence.actor_width")
	require.True(t, ok)
	return width
}

func TestSequenceFragmentIDsCountFragmentsInDeclarationOrder(t *testing.T) {
	src := "sequenceDiagram\nloop a\nA->>B: x\nend\nalt b\nA->>B: y\nloop c\nA->>B: z\nend\nend\nopt d\nA->>B: w\nend\n"
	s := sequenceScene(t, src, scene.ProfileVector)
	var ids []string
	for _, box := range s.Boxes {
		ids = append(ids, box.ID)
	}
	require.Equal(t, []string{"A", "B", "f0", "f1", "f2", "f3"}, ids)
	s = sequenceScene(t, "sequenceDiagram\nparticipant f0\nloop a\nf0->>f0: x\nend\n", scene.ProfileVector)
	ids = ids[:0]
	for _, box := range s.Boxes {
		ids = append(ids, box.ID)
	}
	require.Equal(t, []string{"f0", "f0~1"}, ids, "a source id keeps its name and the fragment takes the next free one")
}

func TestSequenceRoutesTakeTheSharedCornerRadius(t *testing.T) {
	src := "sequenceDiagram\nA->>A: self\nA->>B: out\n"
	for _, profile := range sequenceProfiles {
		want, ok := layoutConstant(profile, "corner_radius")
		require.True(t, ok)
		s := sequenceScene(t, src, profile)
		seen := 0
		for _, group := range s.Groups {
			if group.Role != scene.GroupRoleEdge {
				continue
			}
			for _, item := range group.Items {
				if line, ok := item.(*scene.Polyline); ok {
					require.Equal(t, want, line.Corner, profile.String())
					seen++
				}
			}
		}
		require.Equal(t, 2, seen, profile.String())
		if profile == scene.ProfileVector {
			require.Equal(t, int32(512), want)
		}
	}
}

func TestSequenceFramesStayClearOfForeignBoxesAndLabels(t *testing.T) {
	for _, c := range []struct{ name, src string }{
		{"participant box without a member", "sequenceDiagram\nparticipant A\nbox Group\nend\nparticipant B\n"},
		{"box members split by another actor", "sequenceDiagram\nA->>B: hi\nbox Group\nparticipant A\nparticipant C\nend\n"},
		{"multi-line fragment title", "sequenceDiagram\nparticipant A\nloop first<br>second\nend\n"},
		{"multi-line else title above a nested fragment", "sequenceDiagram\nparticipant A\nalt ok\nA->>A: x\nelse first<br>second<br>third\nopt inner\nA->>A: y\nend\nend\n"},
		{"frame beside an actor of odd width", "sequenceDiagram\nactor A\nactor B as wide wide wide wide\nbox Wide title for the box that is long\nactor C as mid size\nend\nNote over B,B: two<br>lines\nC-->>+B: hi\n"},
	} {
		for _, profile := range sequenceProfiles {
			s := sequenceScene(t, c.src, profile)
			ok, err := s.Check()
			require.NoError(t, err)
			require.True(t, ok, c.name+" "+profile.String())
		}
	}
}

func TestSequenceBoxMembersHaveAdjacentLifelines(t *testing.T) {
	src := "sequenceDiagram\nA->>B: hi\nbox Group\nparticipant A\nparticipant C\nend\n"
	s := sequenceScene(t, src, scene.ProfileVector)
	var actors []string
	for _, box := range s.Boxes {
		if box.Role == scene.RoleNode {
			actors = append(actors, box.ID)
		}
	}
	require.Equal(t, []string{"A", "C", "B"}, actors)
}

func TestSequenceBoxWithoutMemberIsNotADumpBox(t *testing.T) {
	src := "sequenceDiagram\nparticipant A\nbox Group\nend\n"
	s := sequenceScene(t, src, scene.ProfileVector)
	for _, box := range s.Boxes {
		require.NotEqual(t, scene.RoleGroup, box.Role, box.ID)
	}
}
