package lanes

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func text(w, h int32) *Text {
	return &Text{Lines: []measure.StyledLine{{Text: "t", Width: w}}, W: w, H: h}
}

func straight(t *testing.T, branches []Branch, commits []Commit, links []Link, direction scene.Direction, profile scene.Profile) GitGraphResult {
	res, err := GitGraph(GitGraphInput{Direction: direction, ShowBranches: true, RotateLabels: true, Branches: branches, Commits: commits, Links: links}, Params{Profile: profile})
	require.NoError(t, err)
	return res
}

func TestLaneOrderKeyIsOrderThenDeclaration(t *testing.T) {
	branches := []Branch{{ID: "main"}, {ID: "test1", Order: 1, HasOrder: true}, {ID: "test2"}, {ID: "test3"}}
	commits := []Commit{{ID: "a", Branch: 0}, {ID: "b", Branch: 1}, {ID: "c", Branch: 2}, {ID: "d", Branch: 3}}
	res := straight(t, branches, commits, nil, scene.DirectionLR, scene.ProfileVector)
	y := func(i int) int32 { return res.Points[i].Y }
	pitch := y(2) - y(0)
	require.Equal(t, int32(5760), pitch)
	require.Equal(t, 2*pitch, y(3)-y(0))
	require.Equal(t, 3*pitch, y(1)-y(0))
}

func TestOrderTiesFallBackToDeclarationIndex(t *testing.T) {
	branches := []Branch{{ID: "m"}, {ID: "a", Order: 0, HasOrder: true}, {ID: "b", Order: 0, HasOrder: true}}
	commits := []Commit{{ID: "x", Branch: 2}, {ID: "y", Branch: 1}, {ID: "z", Branch: 0}}
	res := straight(t, branches, commits, nil, scene.DirectionLR, scene.ProfileVector)
	require.Less(t, res.Points[2].Y, res.Points[1].Y)
	require.Less(t, res.Points[1].Y, res.Points[0].Y)
}

func TestCommitStepsFollowTheLongestParentChain(t *testing.T) {
	branches := []Branch{{ID: "m"}, {ID: "d"}, {ID: "p"}}
	commits := []Commit{{ID: "a"}, {ID: "b"}, {ID: "c", Branch: 1}, {ID: "d", Branch: 1}, {ID: "e"}, {ID: "pick", Branch: 2}}
	links := []Link{{From: 0, To: 1}, {From: 1, To: 2}, {From: 2, To: 3}, {From: 1, To: 4}, {From: 3, To: 4}, {From: 3, To: 5, Pick: true}}
	res := straight(t, branches, commits, links, scene.DirectionLR, scene.ProfileCell)
	x := func(i int) int32 { return res.Points[i].X - res.Points[0].X }
	require.Equal(t, []int32{0, 4, 8, 12, 16, 0}, []int32{x(0), x(1), x(2), x(3), x(4), x(5)})
}

func TestBackwardLinksDoNotMoveCommits(t *testing.T) {
	commits := []Commit{{ID: "a"}, {ID: "b", Branch: 1}}
	res := straight(t, []Branch{{ID: "m"}, {ID: "d"}}, commits, []Link{{From: 1, To: 0}, {From: 0, To: 0}}, scene.DirectionLR, scene.ProfileCell)
	require.Equal(t, res.Points[0].X, res.Points[1].X)
}

func TestCommitWithOnlyABackwardParentStillAdvancesPastItsLanePredecessor(t *testing.T) {
	commits := []Commit{labelled("a", 0, 6), labelled("b", 0, 6), labelled("c", 0, 6)}
	links := []Link{{From: 0, To: 1}, {From: 2, To: 0}}
	res := straight(t, []Branch{{ID: "m"}}, commits, links, scene.DirectionLR, scene.ProfileCell)
	for i := 1; i < len(commits); i++ {
		prev, next := res.CommitLabels[i-1], res.CommitLabels[i]
		require.Greater(t, res.Points[i].X, res.Points[i-1].X, i)
		require.GreaterOrEqual(t, next.X-(prev.X+prev.W), int32(2), i)
	}
}

func TestCommitWithOnlyABackwardParentStillAdvancesVertically(t *testing.T) {
	commits := []Commit{labelled("a", 0, 6), labelled("b", 0, 6), labelled("c", 0, 6)}
	links := []Link{{From: 0, To: 1}, {From: 2, To: 0}}
	for _, direction := range []scene.Direction{scene.DirectionTB, scene.DirectionBT} {
		res := straight(t, []Branch{{ID: "m"}}, commits, links, direction, scene.ProfileCell)
		for i := 1; i < len(commits); i++ {
			require.Equal(t, int32(4), abs32(res.Points[i].Y-res.Points[i-1].Y), direction.String())
		}
		require.Equal(t, int32(8), abs32(res.Points[2].Y-res.Points[0].Y), direction.String())
	}
}

func TestCrossLaneConnectorIsOrthogonalWithAHalfStepTurn(t *testing.T) {
	branches := []Branch{{ID: "m"}, {ID: "d"}}
	commits := []Commit{{ID: "a", Branch: 0}, {ID: "b", Branch: 1}, {ID: "c", Branch: 0}}
	res := straight(t, branches, commits, []Link{{From: 0, To: 1}, {From: 0, To: 2}}, scene.DirectionLR, scene.ProfileVector)
	a, b, c := res.Points[0], res.Points[1], res.Points[2]
	turn := b.X - 1280
	require.Equal(t, []geom.Point{a, {X: turn, Y: a.Y}, {X: turn, Y: b.Y}, b}, res.Routes[0])
	require.Equal(t, []geom.Point{a, c}, res.Routes[1])
	require.Equal(t, a.Y, c.Y)
}

func TestVerticalDirectionsTransposeTheCommitAxis(t *testing.T) {
	branches := []Branch{{ID: "m"}, {ID: "d"}}
	commits := []Commit{{ID: "a", Branch: 0}, {ID: "b", Branch: 1}, {ID: "c", Branch: 1}}
	links := []Link{{From: 0, To: 1}, {From: 1, To: 2}}
	tb := straight(t, branches, commits, links, scene.DirectionTB, scene.ProfileCell)
	bt := straight(t, branches, commits, links, scene.DirectionBT, scene.ProfileCell)
	for _, res := range []GitGraphResult{tb, bt} {
		require.Equal(t, int32(2), res.Points[1].X-res.Points[0].X)
		require.Greater(t, res.Points[1].X, res.Points[0].X)
		require.Equal(t, res.Points[1].X, res.Points[2].X)
	}
	require.Equal(t, int32(4), tb.Points[1].Y-tb.Points[0].Y)
	require.Equal(t, int32(4), tb.Points[2].Y-tb.Points[1].Y)
	require.Equal(t, int32(-4), bt.Points[1].Y-bt.Points[0].Y)
	require.Equal(t, int32(-4), bt.Points[2].Y-bt.Points[1].Y)
	require.Equal(t, tb.Points[1].X, bt.Points[1].X)
}

func TestVerticalLanesWidenForSideText(t *testing.T) {
	branches := []Branch{{ID: "m"}, {ID: "d"}}
	narrow := straight(t, branches, []Commit{{ID: "a", Branch: 0}, {ID: "b", Branch: 1}}, nil, scene.DirectionTB, scene.ProfileCell)
	labelled := []Commit{{ID: "a", Branch: 0, Label: text(6, 1), Tags: []Text{*text(3, 1)}}, {ID: "b", Branch: 1}}
	wide := straight(t, branches, labelled, nil, scene.DirectionTB, scene.ProfileCell)
	gap := func(r GitGraphResult) int32 { return r.Points[1].X - r.Points[0].X }
	require.Equal(t, int32(2), gap(narrow))
	require.Equal(t, int32(2+1+6+1+3), gap(wide))
	require.Equal(t, wide.Points[0].X+1, wide.CommitLabels[0].X)
	require.Equal(t, wide.CommitLabels[0].X+6+1, wide.TagLabels[0][0].X)
}

func TestLaneFramesAreSegmentsThroughTheirCommits(t *testing.T) {
	branches := []Branch{{ID: "m", Label: text(40, 1280)}, {ID: "d"}}
	commits := []Commit{{ID: "a", Branch: 0}, {ID: "b", Branch: 1}}
	for _, direction := range []scene.Direction{scene.DirectionLR, scene.DirectionTB, scene.DirectionBT} {
		res := straight(t, branches, commits, []Link{{From: 0, To: 1}}, direction, scene.ProfileVector)
		for i, lane := range res.Lanes {
			require.True(t, lane.W == 0 || lane.H == 0, direction.String())
			p := res.Points[i]
			require.True(t, lane.X <= p.X && p.X <= lane.X+lane.W && lane.Y <= p.Y && p.Y <= lane.Y+lane.H, direction.String())
		}
	}
}

func TestLabelPlacementLR(t *testing.T) {
	commits := []Commit{{ID: "a", Branch: 0, Label: text(2560, 1280), Tags: []Text{*text(1280, 1280), *text(1280, 1280)}}}
	res := straight(t, []Branch{{ID: "m"}}, commits, nil, scene.DirectionLR, scene.ProfileVector)
	p := res.Points[0]
	require.Equal(t, geom.Rect{X: p.X - 1280, Y: p.Y + 640, W: 2560, H: 1280}, res.CommitLabels[0])
	require.Equal(t, geom.Rect{X: p.X - 640, Y: p.Y - 1024 - 1280, W: 1280, H: 1280}, res.TagLabels[0][0])
	require.Equal(t, res.TagLabels[0][0].Y-(1280+512), res.TagLabels[0][1].Y)
}

func TestCanvasKeepsEverythingInsideTheMargin(t *testing.T) {
	branches := []Branch{{ID: "m", Label: text(500, 1280)}}
	commits := []Commit{{ID: "a", Branch: 0, Label: text(3000, 1280), Tags: []Text{*text(900, 1280)}}}
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		res := straight(t, branches, commits, nil, scene.DirectionLR, profile)
		rects := append(append([]geom.Rect{res.CommitLabels[0], res.BranchLabels[0]}, res.TagLabels[0]...), res.Lanes...)
		for _, r := range rects {
			require.GreaterOrEqual(t, r.X, int32(0))
			require.GreaterOrEqual(t, r.Y, int32(0))
			require.LessOrEqual(t, r.X+r.W, res.Canvas.W)
			require.LessOrEqual(t, r.Y+r.H, res.Canvas.H)
		}
	}
}

func TestSceneGroupOrderAndOwners(t *testing.T) {
	branches := []Branch{{ID: "lane0", Label: text(40, 1280)}}
	commits := []Commit{{ID: "a"}, {ID: "b"}}
	res := straight(t, branches, commits, []Link{{ID: "e0", From: 0, To: 1}}, scene.DirectionLR, scene.ProfileCell)
	roles := []scene.GroupRole{}
	owners := []string{}
	for _, group := range res.Groups {
		roles, owners = append(roles, group.Role), append(owners, group.Owner)
	}
	require.Equal(t, []scene.GroupRole{scene.GroupRoleGroup, scene.GroupRoleEdge, scene.GroupRoleNode, scene.GroupRoleNode}, roles)
	require.Equal(t, []string{"lane0", "e0", "a", "b"}, owners)
}

func TestRotateCommitLabelsAddsLaneRoom(t *testing.T) {
	branches := []Branch{{ID: "m"}, {ID: "d"}}
	commits := []Commit{{ID: "a", Branch: 0}, {ID: "b", Branch: 1}}
	gap := func(rotate bool) int32 {
		res, err := GitGraph(GitGraphInput{Direction: scene.DirectionLR, RotateLabels: rotate, Branches: branches, Commits: commits}, Params{Profile: scene.ProfileVector})
		require.NoError(t, err)
		return res.Points[1].Y - res.Points[0].Y
	}
	require.Equal(t, int32(3200), gap(false))
	require.Equal(t, int32(3200+2560), gap(true))
}

func TestOverflowIsTyped(t *testing.T) {
	n := 300000
	commits := make([]Commit, n)
	links := make([]Link, 0, n)
	for i := 1; i < n; i++ {
		links = append(links, Link{From: i - 1, To: i})
	}
	_, err := GitGraph(GitGraphInput{Direction: scene.DirectionLR, Branches: []Branch{{ID: "m"}}, Commits: commits, Links: links}, Params{Profile: scene.ProfileVector})
	require.ErrorIs(t, err, geom.ErrOverflow)
}

func labelled(id string, branch int, w int32, tags ...int32) Commit {
	c := Commit{ID: id, Branch: branch, Label: text(w, 1)}
	for _, tagW := range tags {
		c.Tags = append(c.Tags, *text(tagW, 1))
	}
	return c
}

func chain(n int) []Link {
	links := make([]Link, 0, n)
	for i := 1; i < n; i++ {
		links = append(links, Link{From: i - 1, To: i})
	}
	return links
}

func TestCommitGapWidensToKeepAdjacentLabelsApart(t *testing.T) {
	branches := []Branch{{ID: "m"}}
	for _, w := range [][2]int32{{6, 6}, {5, 6}, {6, 5}, {1, 1}, {20, 3}} {
		commits := []Commit{labelled("a", 0, w[0]), labelled("b", 0, w[1])}
		res := straight(t, branches, commits, chain(2), scene.DirectionLR, scene.ProfileCell)
		a, b := res.CommitLabels[0], res.CommitLabels[1]
		require.GreaterOrEqual(t, b.X-(a.X+a.W), int32(2), w)
		require.Equal(t, max(int32(4), (w[0]+w[1]+1)/2+2), res.Points[1].X-res.Points[0].X, w)
	}
}

func TestCommitGapUsesVectorUnits(t *testing.T) {
	commits := []Commit{labelled("a", 0, 6400), labelled("b", 0, 3200)}
	res := straight(t, []Branch{{ID: "m"}}, commits, chain(2), scene.DirectionLR, scene.ProfileVector)
	a, b := res.CommitLabels[0], res.CommitLabels[1]
	require.Equal(t, int32(4800+1536), res.Points[1].X-res.Points[0].X)
	require.GreaterOrEqual(t, b.X-(a.X+a.W), int32(1536))
}

func TestTagsWidenTheCommitGap(t *testing.T) {
	commits := []Commit{labelled("a", 0, 1, 21), labelled("b", 0, 1)}
	res := straight(t, []Branch{{ID: "m"}}, commits, chain(2), scene.DirectionLR, scene.ProfileCell)
	require.Equal(t, int32(11+2), res.Points[1].X-res.Points[0].X)
	a, b := res.TagLabels[0][0], res.CommitLabels[1]
	require.GreaterOrEqual(t, b.X-(a.X+a.W), int32(2))
}

func TestCommitGapUsesTheWidestCommitOfEachLevel(t *testing.T) {
	branches := []Branch{{ID: "m"}, {ID: "d"}}
	commits := []Commit{labelled("a", 0, 2), labelled("x", 1, 10), labelled("b", 0, 2)}
	res := straight(t, branches, commits, []Link{{From: 0, To: 2}, {From: 1, To: 2}}, scene.DirectionLR, scene.ProfileCell)
	require.Equal(t, res.Points[0].X, res.Points[1].X)
	require.Equal(t, int32(6+2), res.Points[2].X-res.Points[0].X)
}

func TestUnlabelledCommitsKeepTheCommitStep(t *testing.T) {
	commits := []Commit{{ID: "a"}, {ID: "b"}, {ID: "c"}}
	cell := straight(t, []Branch{{ID: "m"}}, commits, chain(3), scene.DirectionLR, scene.ProfileCell)
	require.Equal(t, int32(8), cell.Points[2].X-cell.Points[0].X)
	vector := straight(t, []Branch{{ID: "m"}}, commits, chain(3), scene.DirectionLR, scene.ProfileVector)
	require.Equal(t, int32(5120), vector.Points[2].X-vector.Points[0].X)
}

func TestVerticalDirectionsIgnoreLabelWidth(t *testing.T) {
	commits := []Commit{labelled("a", 0, 30), labelled("b", 0, 30)}
	for _, direction := range []scene.Direction{scene.DirectionTB, scene.DirectionBT} {
		res := straight(t, []Branch{{ID: "m"}}, commits, chain(2), direction, scene.ProfileCell)
		require.Equal(t, int32(4), abs32(res.Points[1].Y-res.Points[0].Y), direction.String())
	}
}

func abs32(v int32) int32 {
	if v < 0 {
		return -v
	}
	return v
}

func TestLaneGapClearsTheLabelBandAboveTheTagBand(t *testing.T) {
	branches := []Branch{{ID: "m"}, {ID: "d"}}
	for _, tc := range []struct {
		profile        scene.Profile
		height, tagPad int32
	}{{scene.ProfileCell, 1, 0}, {scene.ProfileVector, 1280, 256}} {
		upper := Commit{ID: "a", Branch: 0, Label: text(3, tc.height)}
		lower := Commit{ID: "b", Branch: 1, Label: text(3, tc.height), Tags: []Text{*text(3, tc.height), *text(3, tc.height)}}
		res, err := GitGraph(GitGraphInput{Direction: scene.DirectionLR, Branches: branches, Commits: []Commit{upper, lower}}, Params{Profile: tc.profile})
		require.NoError(t, err)
		label, topTag := res.CommitLabels[0], res.TagLabels[1][1]
		require.LessOrEqual(t, label.Y+label.H, topTag.Y-tc.tagPad, tc.profile.String())
		if tc.profile == scene.ProfileCell {
			require.Equal(t, int32(2+2), res.Points[1].Y-res.Points[0].Y)
		}
	}
}

func TestLaneGapKeepsTheBasePitchWithoutTags(t *testing.T) {
	branches := []Branch{{ID: "m"}, {ID: "d"}}
	commits := []Commit{labelled("a", 0, 3), labelled("b", 1, 3)}
	res := straight(t, branches, commits, nil, scene.DirectionLR, scene.ProfileCell)
	require.Equal(t, int32(2), res.Points[1].Y-res.Points[0].Y)
}

func TestBottomToTopBranchLabelClearsTheLaneEnd(t *testing.T) {
	for _, tc := range []struct {
		profile       scene.Profile
		clearancePlus int32
	}{{scene.ProfileCell, 1}, {scene.ProfileVector, 512}} {
		res := straight(t, []Branch{{ID: "m", Label: text(40, 1280)}}, []Commit{{ID: "a"}}, nil, scene.DirectionBT, tc.profile)
		lane, label := res.Lanes[0], res.BranchLabels[0]
		require.Equal(t, lane.Y+lane.H+tc.clearancePlus, label.Y, tc.profile.String())
	}
}

func TestVerticalPitchClearsBranchLabelPlates(t *testing.T) {
	branches := []Branch{{ID: "m", Label: text(10, 1)}, {ID: "d", Label: text(10, 1)}}
	res := straight(t, branches, []Commit{{ID: "a", Branch: 0}, {ID: "b", Branch: 1}}, nil, scene.DirectionTB, scene.ProfileCell)
	require.Equal(t, int32(10+2), res.Points[1].X-res.Points[0].X)
	require.LessOrEqual(t, res.BranchLabels[0].X+res.BranchLabels[0].W, res.BranchLabels[1].X)
}
