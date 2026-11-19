package lanes

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func timelineCard(w, h int32) Text {
	return Text{Lines: []measure.StyledLine{{Text: "t", Width: w}}, W: w, H: h}
}

func timelinePeriod(section int, w int32, events ...int32) TimelinePeriod {
	p := TimelinePeriod{ID: "p", Section: section, Label: timelineCard(w, 1280)}
	for _, h := range events {
		p.Events = append(p.Events, TimelineEvent{ID: "e", Link: "r", Label: timelineCard(w, h)})
	}
	return p
}

func timelinePlan(t *testing.T, in TimelineInput, profile scene.Profile) TimelineResult {
	res, err := Timeline(in, Params{Profile: profile})
	require.NoError(t, err)
	return res
}

func TestTimelineHorizontalColumnsStepByTheCardPitch(t *testing.T) {
	res := timelinePlan(t, TimelineInput{Direction: scene.DirectionLR, Periods: []TimelinePeriod{timelinePeriod(NoSection, 100), timelinePeriod(NoSection, 100), timelinePeriod(NoSection, 100)}}, scene.ProfileVector)
	require.Equal(t, int32(9600), res.Periods[0].W)
	for i := 1; i < 3; i++ {
		require.Equal(t, int32(9600+3200), res.Periods[i].X-res.Periods[i-1].X)
		require.Equal(t, res.Periods[0].Y, res.Periods[i].Y)
	}
}

func TestTimelineWideLabelWidensEveryCard(t *testing.T) {
	res := timelinePlan(t, TimelineInput{Direction: scene.DirectionLR, Periods: []TimelinePeriod{timelinePeriod(NoSection, 100), timelinePeriod(NoSection, 12000)}}, scene.ProfileVector)
	require.Equal(t, int32(12000+2*1280), res.Periods[0].W)
	require.Equal(t, res.Periods[0].W, res.Periods[1].W)
}

func TestTimelineSectionBandSpansItsPeriodsAndAnEmptySectionKeepsOneSlot(t *testing.T) {
	in := TimelineInput{
		Direction: scene.DirectionLR,
		Sections:  []TimelineSection{{ID: "s0", Label: timelineCard(100, 1280)}, {ID: "s1", Label: timelineCard(100, 1280)}, {ID: "s2", Label: timelineCard(100, 1280)}},
		Periods:   []TimelinePeriod{timelinePeriod(0, 100), timelinePeriod(0, 100), timelinePeriod(2, 100)},
	}
	res := timelinePlan(t, in, scene.ProfileVector)
	pitch := int32(9600 + 3200)
	require.Equal(t, 2*pitch-3200, res.Sections[0].W)
	require.Equal(t, pitch-3200, res.Sections[1].W)
	require.Equal(t, res.Sections[0].X+2*pitch, res.Sections[1].X)
	require.Equal(t, res.Sections[1].X+pitch, res.Sections[2].X)
	require.Equal(t, res.Sections[2].X, res.Periods[2].X)
	require.Equal(t, res.Sections[0].Y+res.Sections[0].H+3200, res.Periods[0].Y)
}

func TestTimelinePeriodsBeforeTheFirstSectionComeFirst(t *testing.T) {
	in := TimelineInput{
		Direction: scene.DirectionLR,
		Sections:  []TimelineSection{{ID: "s0", Label: timelineCard(100, 1280)}},
		Periods:   []TimelinePeriod{timelinePeriod(0, 100), timelinePeriod(NoSection, 100)},
	}
	res := timelinePlan(t, in, scene.ProfileCell)
	require.Less(t, res.Periods[1].X, res.Periods[0].X)
	require.Equal(t, res.Periods[0].X, res.Sections[0].X)
}

func TestTimelineEventsStackUnderTheirPeriodSeparatedByTheEventGap(t *testing.T) {
	res := timelinePlan(t, TimelineInput{Direction: scene.DirectionLR, Periods: []TimelinePeriod{timelinePeriod(NoSection, 100, 1280, 2560, 1280)}}, scene.ProfileVector)
	events := res.Events[0]
	require.Len(t, events, 3)
	require.Equal(t, res.Periods[0].Y+res.Periods[0].H+3200, events[0].Y)
	for i := 1; i < 3; i++ {
		require.Equal(t, events[i-1].Y+events[i-1].H+640, events[i].Y)
		require.Equal(t, res.Periods[0].X, events[i].X)
	}
	require.Equal(t, int32(2*1280+2560), events[1].H)
	cx := res.Periods[0].X + res.Periods[0].W/2
	require.Equal(t, []geom.Point{{X: cx, Y: res.Periods[0].Y + res.Periods[0].H}, {X: cx, Y: events[0].Y}}, res.Routes[0][0])
	require.Equal(t, []geom.Point{{X: cx, Y: events[0].Y + events[0].H}, {X: cx, Y: events[1].Y}}, res.Routes[0][1])
}

func TestTimelineAxisRunsBetweenThePeriodRowAndTheFirstEvent(t *testing.T) {
	res := timelinePlan(t, TimelineInput{Direction: scene.DirectionLR, Periods: []TimelinePeriod{timelinePeriod(NoSection, 100, 1280)}}, scene.ProfileVector)
	bottom := res.Periods[0].Y + res.Periods[0].H
	axis := res.Groups[0]
	require.Equal(t, scene.GroupRoleDecor, axis.Role)
	require.NotEmpty(t, axis.Items)
	require.Less(t, bottom, res.Events[0][0].Y)
}

func TestTimelineVerticalPutsEventsInASecondColumn(t *testing.T) {
	in := TimelineInput{
		Direction: scene.DirectionTB,
		Sections:  []TimelineSection{{ID: "s0", Label: timelineCard(100, 1280)}},
		Periods:   []TimelinePeriod{timelinePeriod(0, 100, 1280, 1280), timelinePeriod(0, 100, 1280)},
	}
	res := timelinePlan(t, in, scene.ProfileVector)
	require.Equal(t, res.Periods[0].X, res.Periods[1].X)
	require.Equal(t, res.Periods[0].X+res.Periods[0].W+3200, res.Events[0][0].X)
	require.Equal(t, res.Events[0][0].X, res.Events[1][0].X)
	require.Equal(t, res.Periods[0].W, res.Sections[0].W)
	require.Greater(t, res.Periods[1].Y, res.Events[0][1].Y)
	for _, route := range res.Routes[0] {
		require.True(t, geom.IsOrthogonal(route))
		require.Equal(t, res.Periods[0].X+res.Periods[0].W, route[0].X)
	}
}

func TestTimelineVerticalRowKeepsAStraightRouteWhenTheCentresAlign(t *testing.T) {
	res := timelinePlan(t, TimelineInput{Direction: scene.DirectionTB, Periods: []TimelinePeriod{timelinePeriod(NoSection, 100, 1280)}}, scene.ProfileVector)
	require.Len(t, res.Routes[0][0], 2)
}

func TestTimelineTitleIsCentredOverTheContent(t *testing.T) {
	in := TimelineInput{Direction: scene.DirectionLR, Title: &TimelineTitle{ID: "title", Label: timelineCard(2000, 1536)}, Periods: []TimelinePeriod{timelinePeriod(NoSection, 100)}}
	res := timelinePlan(t, in, scene.ProfileVector)
	require.Equal(t, int32(2000), res.Title.W)
	require.Equal(t, res.Periods[0].X+res.Periods[0].W/2, res.Title.X+res.Title.W/2)
	require.Equal(t, res.Title.Y+res.Title.H+640, res.Periods[0].Y)
}

func TestTimelineSeriesFollowSectionsAndPeriodsWithoutSections(t *testing.T) {
	flat := TimelineInput{Direction: scene.DirectionLR}
	for range 14 {
		flat.Periods = append(flat.Periods, timelinePeriod(NoSection, 100))
	}
	pl := &timelinePlanner{in: flat}
	require.Equal(t, uint8(0), pl.series(0))
	require.Equal(t, uint8(13%seriesMax), pl.series(13))
	sectioned := TimelineInput{Sections: []TimelineSection{{}, {}}, Periods: []TimelinePeriod{timelinePeriod(NoSection, 100), timelinePeriod(1, 100)}}
	pl = &timelinePlanner{in: sectioned}
	require.Equal(t, uint8(0), pl.series(0))
	require.Equal(t, uint8(1), pl.series(1))
}

func TestTimelinePeriodWithAnUnknownSectionIsRejected(t *testing.T) {
	for _, section := range []int{1, -2} {
		_, err := Timeline(TimelineInput{Sections: []TimelineSection{{}}, Periods: []TimelinePeriod{timelinePeriod(section, 100)}}, Params{})
		require.ErrorIs(t, err, ErrTimelineInput)
	}
}

func TestTimelineEmptyInputStillHasAnAxisAndACanvas(t *testing.T) {
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		res := timelinePlan(t, TimelineInput{Direction: scene.DirectionLR}, profile)
		require.Positive(t, res.Canvas.W)
		require.Positive(t, res.Canvas.H)
	}
}

func TestTimelineResultCoordinatesAreNeverNegative(t *testing.T) {
	in := TimelineInput{
		Direction: scene.DirectionTB,
		Title:     &TimelineTitle{ID: "title", Label: timelineCard(30, 1)},
		Sections:  []TimelineSection{{ID: "s0", Label: timelineCard(8, 1)}},
		Periods:   []TimelinePeriod{timelinePeriod(0, 8, 1, 2), timelinePeriod(NoSection, 8)},
	}
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		res := timelinePlan(t, in, profile)
		rects := append([]geom.Rect{res.Title}, res.Sections...)
		rects = append(rects, res.Periods...)
		for _, events := range res.Events {
			rects = append(rects, events...)
		}
		for _, r := range rects {
			require.GreaterOrEqual(t, r.X, int32(0))
			require.GreaterOrEqual(t, r.Y, int32(0))
			require.LessOrEqual(t, r.X+r.W, res.Canvas.W)
			require.LessOrEqual(t, r.Y+r.H, res.Canvas.H)
		}
	}
}
