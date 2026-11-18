package lanes

import (
	"cmp"
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type Text struct {
	Lines []measure.StyledLine
	W, H  int32
	Role  scene.TextRole
}

type Branch struct {
	ID       string
	Order    int64
	HasOrder bool
	Label    *Text
}

type Commit struct {
	ID     string
	Branch int
	Kind   string
	Label  *Text
	Tags   []Text
}

type Link struct {
	ID       string
	From, To int
	Pick     bool
}

type GitGraphInput struct {
	Direction    scene.Direction
	ShowBranches bool
	RotateLabels bool
	Branches     []Branch
	Commits      []Commit
	Links        []Link
}

type Params struct {
	Profile scene.Profile
}

type GitGraphResult struct {
	Canvas       geom.Size
	Lanes        []geom.Rect
	Points       []geom.Point
	Routes       [][]geom.Point
	BranchLabels []geom.Rect
	CommitLabels []geom.Rect
	TagLabels    [][]geom.Rect
	Groups       []*scene.Group
}

type vec struct{ x, y int64 }

type box struct{ x, y, w, h int64 }

func (b box) right() int64  { return b.x + b.w }
func (b box) bottom() int64 { return b.y + b.h }

func half(v int64) int64 { return geom.FloorDiv(v, 2) }

func abs(v int64) int64 {
	if v < 0 {
		return -v
	}
	return v
}

func union(a, b box) box {
	x, y := min(a.x, b.x), min(a.y, b.y)
	return box{x: x, y: y, w: max(a.right(), b.right()) - x, h: max(a.bottom(), b.bottom()) - y}
}

type planner struct {
	in       GitGraphInput
	c        gitgraphConstants
	profile  scene.Profile
	rank     []int
	byRank   []int
	laneAt   []int64
	level    []int
	reach    []int64
	step     []int64
	maxStep  int64
	pitch    int64
	points   []vec
	routes   [][]vec
	lanes    []box
	branches []box
	labels   []box
	tags     [][]box
	starts   []vec
	ends     []vec
}

func GitGraph(in GitGraphInput, p Params) (GitGraphResult, error) {
	if in.Direction == scene.DirectionRL {
		return GitGraphResult{}, geom.ErrDomain
	}
	c, err := loadGitgraphConstants(p.Profile)
	if err != nil {
		return GitGraphResult{}, err
	}
	pl := &planner{in: in, c: c, profile: p.Profile}
	pl.rankLanes()
	pl.advance()
	pl.measurePitch()
	pl.measureLanes()
	pl.placeCommits()
	pl.placeLanes()
	pl.placeRoutes()
	return pl.result()
}

func (pl *planner) rankLanes() {
	order := make([]int, len(pl.in.Branches))
	for i := range order {
		order[i] = i
	}
	slices.SortFunc(order, func(a, b int) int {
		return cmp.Or(cmp.Compare(pl.in.Branches[a].Order, pl.in.Branches[b].Order), cmp.Compare(a, b))
	})
	pl.byRank = order
	pl.rank = make([]int, len(order))
	for position, branch := range order {
		pl.rank[branch] = position
	}
}

func (pl *planner) advance() {
	n := len(pl.in.Commits)
	parents := make([][]int, n)
	for _, link := range pl.in.Links {
		if !link.Pick && link.From < link.To {
			parents[link.To] = append(parents[link.To], link.From)
		}
	}
	pl.level = make([]int, n)
	lastOnLane := make([]int, len(pl.in.Branches))
	for b := range lastOnLane {
		lastOnLane[b] = -1
	}
	levels := 0
	for i, from := range parents {
		b := pl.in.Commits[i].Branch
		pl.level[i] = lastOnLane[b] + 1
		for _, parent := range from {
			pl.level[i] = max(pl.level[i], pl.level[parent]+1)
		}
		lastOnLane[b] = pl.level[i]
		levels = max(levels, pl.level[i]+1)
	}
	pl.reach = pl.levelReach(levels)
	axis := pl.levelAxis(levels)
	pl.step = make([]int64, n)
	for i, level := range pl.level {
		pl.step[i] = axis[level]
	}
	if levels > 0 {
		pl.maxStep = axis[levels-1]
	}
}

func (pl *planner) levelReach(levels int) []int64 {
	reach := make([]int64, levels)
	if pl.vertical() {
		return reach
	}
	for i, commit := range pl.in.Commits {
		reach[pl.level[i]] = max(reach[pl.level[i]], pl.textWidth(commit))
	}
	return reach
}

func (pl *planner) levelAxis(levels int) []int64 {
	axis := make([]int64, levels)
	for l := 1; l < levels; l++ {
		axis[l] = axis[l-1] + pl.levelGap(pl.reach[l-1], pl.reach[l])
	}
	return axis
}

func (pl *planner) levelGap(before, after int64) int64 {
	if pl.vertical() {
		return pl.c.commitStep
	}
	return max(pl.c.commitStep, half(before+after+1)+pl.c.labelGap)
}

func (pl *planner) textWidth(commit Commit) int64 {
	var widest int64
	if commit.Label != nil {
		widest = int64(commit.Label.W)
	}
	for _, tag := range commit.Tags {
		widest = max(widest, int64(tag.W)+2*pl.c.tagPad)
	}
	return widest
}

func (pl *planner) turnBack(commit int) int64 {
	back := half(pl.c.commitStep)
	if pl.vertical() {
		return back
	}
	return max(back, half(pl.reach[pl.level[commit]])+half(pl.c.labelGap+1))
}

func (pl *planner) vertical() bool { return pl.in.Direction != scene.DirectionLR }

func (pl *planner) at(commitAxis, laneAxis int64) vec {
	switch pl.in.Direction {
	case scene.DirectionTB:
		return vec{laneAxis, commitAxis}
	case scene.DirectionBT:
		return vec{laneAxis, pl.maxStep - commitAxis}
	}
	return vec{commitAxis, laneAxis}
}

func (pl *planner) laneAxis(branch int) int64 { return pl.laneAt[branch] }

func (pl *planner) measurePitch() {
	pl.pitch = pl.c.lanePitch
	if pl.in.RotateLabels {
		pl.pitch += pl.c.rotationExtra
	}
	if !pl.vertical() {
		return
	}
	var widest int64
	for _, commit := range pl.in.Commits {
		widest = max(widest, pl.sideExtent(commit))
	}
	pl.pitch = max(pl.pitch+widest, pl.widestPlate()+pl.c.labelGap)
}

func (pl *planner) widestPlate() int64 {
	var widest int64
	for b := range pl.in.Branches {
		if label := pl.shownLabel(b); label != nil {
			widest = max(widest, int64(label.W)+2*pl.c.branchPadX)
		}
	}
	return widest
}

func (pl *planner) measureLanes() {
	pl.laneAt = make([]int64, len(pl.byRank))
	for position := 1; position < len(pl.byRank); position++ {
		upper, lower := pl.byRank[position-1], pl.byRank[position]
		pl.laneAt[lower] = pl.laneAt[upper] + pl.laneGap(upper, lower)
	}
}

func (pl *planner) laneGap(upper, lower int) int64 {
	if pl.vertical() {
		return pl.pitch
	}
	return max(pl.pitch, pl.labelBand(upper)+pl.tagBand(lower))
}

func (pl *planner) labelBand(branch int) int64 {
	var band int64
	for _, commit := range pl.in.Commits {
		if commit.Branch == branch && commit.Label != nil {
			band = max(band, pl.c.labelOffset+int64(commit.Label.H))
		}
	}
	return band
}

func (pl *planner) tagBand(branch int) int64 {
	var band int64
	for _, commit := range pl.in.Commits {
		if commit.Branch == branch && len(commit.Tags) > 0 {
			band = max(band, pl.c.tagOffset+pl.c.tagPad+pl.tagStack(commit.Tags))
		}
	}
	return band
}

func (pl *planner) tagStack(tags []Text) int64 {
	stack := 2 * pl.c.tagPad * int64(len(tags)-1)
	for _, tag := range tags {
		stack += int64(tag.H)
	}
	return stack
}

func (pl *planner) sideExtent(commit Commit) int64 {
	label, tags := pl.placeBeside(commit, vec{})
	var extent int64
	if commit.Label != nil {
		extent = label.right()
	}
	for _, tag := range tags {
		extent = max(extent, tag.right())
	}
	return extent
}

func (pl *planner) placeCommits() {
	n := len(pl.in.Commits)
	pl.points = make([]vec, n)
	pl.labels = make([]box, n)
	pl.tags = make([][]box, n)
	for i, commit := range pl.in.Commits {
		at := pl.at(pl.step[i], pl.laneAxis(commit.Branch))
		pl.points[i] = at
		pl.labels[i], pl.tags[i] = pl.placeTexts(commit, at)
	}
}

func (pl *planner) placeTexts(commit Commit, at vec) (box, []box) {
	if pl.vertical() {
		return pl.placeBeside(commit, at)
	}
	var label box
	if commit.Label != nil {
		w, h := int64(commit.Label.W), int64(commit.Label.H)
		label = box{x: at.x - half(w), y: at.y + pl.c.labelOffset, w: w, h: h}
	}
	tags := make([]box, len(commit.Tags))
	var raised int64
	for k, tag := range commit.Tags {
		w, h := int64(tag.W), int64(tag.H)
		tags[k] = box{x: at.x - half(w), y: at.y - pl.c.tagOffset - raised - h, w: w, h: h}
		raised += h + 2*pl.c.tagPad
	}
	return label, tags
}

func (pl *planner) placeBeside(commit Commit, at vec) (box, []box) {
	cursor := pl.c.labelOffset
	var label box
	if commit.Label != nil {
		w, h := int64(commit.Label.W), int64(commit.Label.H)
		label = box{x: at.x + cursor, y: at.y - half(h), w: w, h: h}
		cursor += w + pl.c.labelOffset
	}
	tags := make([]box, len(commit.Tags))
	for k, tag := range commit.Tags {
		w, h := int64(tag.W), int64(tag.H)
		tags[k] = box{x: at.x + cursor, y: at.y - half(h), w: w, h: h}
		cursor += w + pl.c.labelOffset
	}
	return label, tags
}

func (pl *planner) shownLabel(b int) *Text {
	if !pl.in.ShowBranches {
		return nil
	}
	return pl.in.Branches[b].Label
}

func (pl *planner) placeLanes() {
	n := len(pl.in.Branches)
	pl.lanes = make([]box, n)
	pl.branches = make([]box, n)
	pl.starts = make([]vec, n)
	pl.ends = make([]vec, n)
	start, end := -pl.c.labelGap, pl.maxStep+half(pl.c.commitStep)
	for b := range pl.in.Branches {
		l := pl.laneAxis(b)
		from, to := pl.at(start, l), pl.at(end, l)
		pl.starts[b], pl.ends[b] = from, to
		pl.lanes[b] = pl.laneBand(from, to)
		if label := pl.shownLabel(b); label != nil {
			pl.branches[b] = pl.anchorLabel(from, int64(label.W)+2*pl.c.branchPadX, int64(label.H)+2*pl.c.branchPadY)
		}
	}
}

func (pl *planner) anchorLabel(from vec, w, h int64) box {
	switch pl.in.Direction {
	case scene.DirectionTB:
		return box{x: from.x - half(w), y: from.y - h, w: w, h: h}
	case scene.DirectionBT:
		return box{x: from.x - half(w), y: from.y + pl.laneEndClearance(), w: w, h: h}
	}
	return box{x: from.x - w, y: from.y - half(h), w: w, h: h}
}

func (pl *planner) laneEndClearance() int64 {
	if pl.isCell() {
		return 1
	}
	return 0
}

func (pl *planner) laneBand(from, to vec) box {
	return box{x: min(from.x, to.x), y: min(from.y, to.y), w: abs(to.x - from.x), h: abs(to.y - from.y)}
}

func (pl *planner) placeRoutes() {
	pl.routes = make([][]vec, len(pl.in.Links))
	for i, link := range pl.in.Links {
		pl.routes[i] = pl.route(link)
	}
}

func (pl *planner) route(link Link) []vec {
	from, to := pl.in.Commits[link.From], pl.in.Commits[link.To]
	fromLane, toLane := pl.laneAxis(from.Branch), pl.laneAxis(to.Branch)
	start, end := pl.step[link.From], pl.step[link.To]
	if from.Branch == to.Branch {
		return []vec{pl.at(start, fromLane), pl.at(end, toLane)}
	}
	turn := end - pl.turnBack(link.To)
	return []vec{pl.at(start, fromLane), pl.at(turn, fromLane), pl.at(turn, toLane), pl.at(end, toLane)}
}
