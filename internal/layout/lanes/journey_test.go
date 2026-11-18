package lanes

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

var journeyProfiles = []scene.Profile{scene.ProfileVector, scene.ProfileCell}

func journeyLine(profile scene.Profile) int32 {
	if profile == scene.ProfileCell {
		return 1
	}
	return 1280
}

func journeyText(profile scene.Profile, w int32, lines int32) Text {
	return Text{Lines: []measure.StyledLine{{Text: "t", Width: w}}, W: w, H: lines * journeyLine(profile), Role: scene.TextRoleLabel}
}

func journeyConst(t *testing.T, profile scene.Profile, name string) int32 {
	t.Helper()
	value, ok := constant(profile, name)
	require.True(t, ok, name)
	return int32(value)
}

func journeyFixture(profile scene.Profile) JourneyInput {
	label := journeyText(profile, 4, 1)
	return JourneyInput{
		Title:    &JourneyTitle{ID: "title", Label: journeyText(profile, 9, 1)},
		Sections: []JourneySection{{ID: "s0", Label: label}, {ID: "s1", Label: label}},
		Tasks: []JourneyTask{
			{ID: "t0", Band: NoBand, Score: 2, Label: label},
			{ID: "t1", Band: 0, Score: 5, Label: label},
			{ID: "t2", Band: 0, Score: 1, Label: label},
			{ID: "t3", Band: 0, Score: 3, Label: label},
			{ID: "t4", Band: 1, Score: 4, Label: label},
		},
	}
}

func runJourney(t *testing.T, in JourneyInput, profile scene.Profile) JourneyResult {
	t.Helper()
	res, err := Journey(in, Params{Profile: profile})
	require.NoError(t, err)
	return res
}

func TestJourneyTaskColumnsStepByWidthPlusGap(t *testing.T) {
	for _, profile := range journeyProfiles {
		res := runJourney(t, journeyFixture(profile), profile)
		width := journeyConst(t, profile, "journey.task_width")
		pitch := width + journeyConst(t, profile, "journey.column_gap")
		for k := 1; k < len(res.Tasks); k++ {
			require.Equal(t, pitch, res.Tasks[k].X-res.Tasks[k-1].X, "%s task %d", profile, k)
			require.Equal(t, res.Tasks[0].Y, res.Tasks[k].Y)
			require.Equal(t, width, res.Tasks[k].W)
		}
	}
}

func TestJourneyBandsSpanTheirTasksAtTheTop(t *testing.T) {
	for _, profile := range journeyProfiles {
		res := runJourney(t, journeyFixture(profile), profile)
		width, gap := journeyConst(t, profile, "journey.task_width"), journeyConst(t, profile, "journey.column_gap")
		require.Equal(t, res.Tasks[1].X, res.Bands[0].X)
		require.Equal(t, 3*width+2*gap, res.Bands[0].W)
		require.Equal(t, res.Tasks[4].X, res.Bands[1].X)
		require.Equal(t, width, res.Bands[1].W)
		require.Equal(t, journeyConst(t, profile, "journey.band_height"), res.Bands[0].H)
		require.Equal(t, res.Bands[0].Y, res.Bands[1].Y)
		require.Equal(t, res.Title.Y+res.Title.H+journeyConst(t, profile, "journey.score_step"), res.Bands[0].Y)
	}
}

func TestJourneyFacesSitAtScoreHeights(t *testing.T) {
	for _, profile := range journeyProfiles {
		in := journeyFixture(profile)
		res := runJourney(t, in, profile)
		step := journeyConst(t, profile, "journey.score_step")
		top := res.Bands[0].Y + res.Bands[0].H
		for k, task := range in.Tasks {
			want := top + (5-int32(task.Score))*step + step
			require.Equal(t, want, res.Faces[k].Y, "%s task %d", profile, k)
			require.Equal(t, res.Tasks[k].X+res.Tasks[k].W/2, res.Faces[k].X)
		}
		require.Less(t, res.Faces[1].Y, res.Faces[3].Y)
		require.Less(t, res.Faces[3].Y, res.Faces[2].Y)
		require.Equal(t, top+(5-1+2)*step, res.Tasks[0].Y, "task top sits below the lowest face")
	}
}

func TestJourneyFramesEncloseBandAndTasksAndNeverOverlap(t *testing.T) {
	for _, profile := range journeyProfiles {
		res := runJourney(t, journeyFixture(profile), profile)
		for b, members := range [][]int{{1, 2, 3}, {4}} {
			frame := res.Frames[b]
			contains, err := geom.Contains(frame, res.Bands[b])
			require.NoError(t, err)
			require.True(t, contains)
			for _, k := range members {
				contains, err := geom.Contains(frame, res.Tasks[k])
				require.NoError(t, err)
				require.True(t, contains, "%s frame %d task %d", profile, b, k)
			}
		}
		meets, err := geom.Intersects(res.Frames[0], res.Frames[1])
		require.NoError(t, err)
		require.False(t, meets)
	}
}

func TestJourneyTaskWithoutBandHasNoFrame(t *testing.T) {
	label := journeyText(scene.ProfileCell, 4, 1)
	res := runJourney(t, JourneyInput{Tasks: []JourneyTask{{ID: "t", Band: NoBand, Score: 3, Label: label}}}, scene.ProfileCell)
	require.Empty(t, res.Frames)
	require.Len(t, res.Groups, 1)
	require.Equal(t, scene.GroupRoleNode, res.Groups[0].Role)
}

func TestJourneyRejectsMalformedInput(t *testing.T) {
	label := journeyText(scene.ProfileVector, 4, 1)
	cases := map[string]JourneyInput{
		"score above":   {Tasks: []JourneyTask{{ID: "t", Band: NoBand, Score: 6, Label: label}}},
		"score below":   {Tasks: []JourneyTask{{ID: "t", Band: NoBand, Score: 0, Label: label}}},
		"unknown band":  {Tasks: []JourneyTask{{ID: "t", Band: 0, Score: 3, Label: label}}},
		"empty section": {Sections: []JourneySection{{ID: "s", Label: label}}},
		"split section": {
			Sections: []JourneySection{{ID: "s", Label: label}},
			Tasks:    []JourneyTask{{ID: "a", Band: 0, Score: 3}, {ID: "b", Band: NoBand, Score: 3}, {ID: "c", Band: 0, Score: 3}},
		},
	}
	for name, in := range cases {
		_, err := Journey(in, Params{Profile: scene.ProfileVector})
		require.ErrorIs(t, err, ErrJourneyInput, name)
	}
}

func TestJourneyTallTextGrowsBandAndCards(t *testing.T) {
	profile := scene.ProfileVector
	in := journeyFixture(profile)
	base := runJourney(t, in, profile)
	people := journeyText(profile, 6, 1)
	in.Tasks[1].People = &people
	in.Sections[0].Label = journeyText(profile, 4, 5)
	grown := runJourney(t, in, profile)
	require.Greater(t, grown.Bands[0].H, base.Bands[0].H)
	require.Greater(t, grown.Tasks[0].H, base.Tasks[0].H)
	require.Equal(t, grown.Bands[0].H, grown.Bands[1].H)
	require.Equal(t, grown.Tasks[0].H, grown.Tasks[4].H)
	pad := journeyConst(t, profile, "node_pad_y") + journeyConst(t, profile, "node_border")
	require.Equal(t, 5*journeyLine(profile)+2*pad, grown.Bands[0].H)
	require.Equal(t, 2*journeyLine(profile)+2*pad, grown.Tasks[1].H)
}

func TestJourneyCanvasIsExtentPlusMarginOnEachSide(t *testing.T) {
	for _, profile := range journeyProfiles {
		res := runJourney(t, journeyFixture(profile), profile)
		margin := journeyConst(t, profile, "canvas_margin")
		require.Equal(t, margin, res.Title.X)
		require.Equal(t, margin, res.Title.Y)
		last := res.Tasks[len(res.Tasks)-1]
		require.Equal(t, last.X+last.W+margin, res.Canvas.W)
		require.Equal(t, last.Y+last.H+margin, res.Canvas.H)
	}
}

func TestJourneyPaintOrderAndStyles(t *testing.T) {
	res := runJourney(t, journeyFixture(scene.ProfileVector), scene.ProfileVector)
	roles := make([]scene.GroupRole, len(res.Groups))
	for i, g := range res.Groups {
		roles[i] = g.Role
	}
	want := []scene.GroupRole{scene.GroupRoleGroup, scene.GroupRoleGroup, scene.GroupRoleNode, scene.GroupRoleNode, scene.GroupRoleNode, scene.GroupRoleNode, scene.GroupRoleNode, scene.GroupRoleNode}
	require.Equal(t, want, roles)
	require.Equal(t, "s1", res.Groups[1].Owner)
	band := res.Groups[1].Items[0].(*scene.RoundRect)
	require.Equal(t, "series-tint", band.Style)
	require.Equal(t, uint8(1), band.Series)
	unbanded := res.Groups[3].Items[0].(*scene.RoundRect)
	require.Equal(t, "node", unbanded.Style)
	banded := res.Groups[4].Items[0].(*scene.RoundRect)
	require.Equal(t, uint8(0), banded.Series)
	require.Equal(t, "series-tint", banded.Style)
}

func TestJourneyFaceExpressionFollowsTheScoreMidpoint(t *testing.T) {
	res := runJourney(t, journeyFixture(scene.ProfileVector), scene.ProfileVector)
	mouth := func(task int) scene.Primitive { return res.Groups[3+task].Items[4] }
	sad, smile, neutral := mouth(0), mouth(1), mouth(3)
	require.IsType(t, &scene.Path{}, sad)
	require.IsType(t, &scene.Path{}, smile)
	require.Equal(t, int32(-32768), sad.(*scene.Path).Commands[1].(*scene.ArcTo).Sweep)
	require.Equal(t, int32(32768), smile.(*scene.Path).Commands[1].(*scene.ArcTo).Sweep)
	require.IsType(t, &scene.Polyline{}, neutral)
}

func TestJourneyCellFaceIsOneRingSymbol(t *testing.T) {
	in := journeyFixture(scene.ProfileCell)
	res := runJourney(t, in, scene.ProfileCell)
	var symbols int
	for _, g := range res.Groups {
		for _, item := range g.Items {
			if ref, ok := item.(*scene.SymbolRef); ok {
				symbols++
				require.Equal(t, "ring", ref.Symbol)
			}
		}
	}
	require.Equal(t, len(in.Tasks), symbols)
}

func TestJourneyOverridesReplaceProfileDefaults(t *testing.T) {
	in := journeyFixture(scene.ProfileVector)
	in.TaskWidth, in.ColumnGap, in.TaskHeight, in.BandHeight = 20000, 1000, 5000, 4000
	res := runJourney(t, in, scene.ProfileVector)
	require.Equal(t, int32(21000), res.Tasks[1].X-res.Tasks[0].X)
	require.Equal(t, int32(20000), res.Tasks[0].W)
	require.Equal(t, int32(5000), res.Tasks[0].H)
	require.Equal(t, int32(4000), res.Bands[0].H)
}
