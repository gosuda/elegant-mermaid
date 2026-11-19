package lanes

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

var cellSymbols = map[string]string{
	"commit": "disc", "reverse": "ring", "highlight": "diamond",
	"merge": "bullseye", "merge-reverse": "bullseye", "merge-highlight": "bullseye",
	"cherry-pick": "diamond-hollow",
}

func plain(style string) scene.Shape { return scene.Shape{Style: style} }

func runs(lines []measure.StyledLine) [][]scene.Run {
	out := make([][]scene.Run, len(lines))
	for i, line := range lines {
		out[i] = make([]scene.Run, len(line.Runs))
		for j, run := range line.Runs {
			out[i][j] = scene.Run{Text: run.Text, Bold: run.Bold, Italic: run.Italic}
		}
	}
	return out
}

func (pl *planner) textItem(label *Text, rect geom.Rect, align scene.Align) scene.Primitive {
	return &scene.Text{Rect: rect, Role: label.Role, Size: 14, Align: align, Style: "text", Lines: runs(label.Lines)}
}

func (pl *planner) commitAlign() scene.Align {
	if pl.vertical() {
		return scene.AlignStart
	}
	return scene.AlignMiddle
}

func (pl *planner) paint(f *frame, res GitGraphResult) []*scene.Group {
	groups := make([]*scene.Group, 0, len(pl.in.Branches)+len(pl.in.Links)+len(pl.in.Commits))
	for b := range pl.in.Branches {
		groups = append(groups, &scene.Group{Role: scene.GroupRoleGroup, Owner: pl.in.Branches[b].ID, Items: pl.laneItems(f, res, b)})
	}
	for i, link := range pl.in.Links {
		groups = append(groups, &scene.Group{Role: scene.GroupRoleEdge, Owner: link.ID, Items: pl.edgeItems(res, i)})
	}
	for i := range pl.in.Commits {
		groups = append(groups, &scene.Group{Role: scene.GroupRoleNode, Owner: pl.in.Commits[i].ID, Items: pl.commitItems(res, i)})
	}
	return groups
}

func (pl *planner) laneItems(f *frame, res GitGraphResult, b int) []scene.Primitive {
	if !pl.in.ShowBranches {
		return nil
	}
	series := uint8(pl.rank[b] % 12)
	line := plain("series-line")
	line.Series = series
	line.Line = []scene.LineStyle{scene.LineSolid, scene.LineDashed, scene.LineDotted}[pl.rank[b]%3]
	if !pl.isCell() {
		line.Width = scene.Width{Kind: scene.WidthEmphasis}
	}
	items := []scene.Primitive{&scene.Polyline{Shape: line, Points: []geom.Point{f.point(pl.starts[b]), f.point(pl.ends[b])}}}
	label := pl.shownLabel(b)
	if label == nil {
		return items
	}
	if !pl.isCell() {
		tint := plain("series-tint")
		tint.Series = series
		items = append(items, &scene.RoundRect{Shape: tint, Rect: f.rect(pl.branches[b]), R: int32(pl.c.cornerRadius)})
	}
	return append(items, pl.textItem(label, res.BranchLabels[b], scene.AlignMiddle))
}

func (pl *planner) edgeItems(res GitGraphResult, i int) []scene.Primitive {
	shape := plain("edge")
	if pl.in.Links[i].Pick {
		shape.Line = scene.LineDotted
	}
	return []scene.Primitive{&scene.Polyline{Shape: shape, Corner: int32(pl.c.cornerRadius), Points: res.Routes[i]}}
}

func (pl *planner) commitItems(res GitGraphResult, i int) []scene.Primitive {
	commit := pl.in.Commits[i]
	items := pl.marker(res, i)
	if commit.Label != nil {
		items = append(items, pl.textItem(commit.Label, res.CommitLabels[i], pl.commitAlign()))
	}
	for k := range commit.Tags {
		items = append(items, pl.textItem(&commit.Tags[k], res.TagLabels[i][k], pl.commitAlign()))
	}
	return items
}

func (pl *planner) marker(res GitGraphResult, i int) []scene.Primitive {
	commit := pl.in.Commits[i]
	if pl.isCell() {
		return []scene.Primitive{&scene.SymbolRef{Symbol: cellSymbols[commit.Kind], At: res.Points[i], Style: "mark"}}
	}
	items := pl.glyph(commit.Kind, res.Points[i], uint8(pl.rank[commit.Branch]%12))
	for k := range commit.Tags {
		items = append(items, pl.tagBox(res.TagLabels[i][k]))
	}
	return items
}

func (pl *planner) tagBox(text geom.Rect) scene.Primitive {
	pad := int32(pl.c.tagPad)
	rect := geom.Rect{X: text.X - pad, Y: text.Y - pad, W: text.W + 2*pad, H: text.H + 2*pad}
	return &scene.RoundRect{Shape: plain("note"), Rect: rect, R: int32(pl.c.tagPad)}
}

func (pl *planner) glyph(kind string, at geom.Point, series uint8) []scene.Primitive {
	r := int32(pl.c.commitRadius)
	body := plain("series")
	body.Series = series
	var items []scene.Primitive
	switch kind {
	case "highlight", "merge-highlight":
		items = []scene.Primitive{&scene.Rect{Shape: body, Rect: geom.Rect{X: at.X - r, Y: at.Y - r, W: 2 * r, H: 2 * r}}}
	default:
		items = []scene.Primitive{&scene.Ellipse{Shape: body, CX: at.X, CY: at.Y, RX: r, RY: r}}
	}
	return append(items, pl.decoration(kind, at, r)...)
}

func (pl *planner) decoration(kind string, at geom.Point, r int32) []scene.Primitive {
	d := int32(geom.FloorDiv(int64(r), 2))
	var items []scene.Primitive
	switch kind {
	case "reverse", "merge-reverse":
		items = append(items, cross(at, d)...)
	case "highlight", "merge-highlight":
		items = append(items, &scene.Rect{Shape: plain("mark-hollow"), Rect: geom.Rect{X: at.X - d, Y: at.Y - d, W: 2 * d, H: 2 * d}})
	case "cherry-pick":
		return cherry(at, d)
	}
	if kind == "merge" || kind == "merge-reverse" || kind == "merge-highlight" {
		items = append(items, &scene.Ellipse{Shape: plain("mark-hollow"), CX: at.X, CY: at.Y, RX: d, RY: d})
	}
	return items
}

func cross(at geom.Point, d int32) []scene.Primitive {
	return []scene.Primitive{
		&scene.Polyline{Shape: plain("ink-line"), Points: []geom.Point{{X: at.X - d, Y: at.Y - d}, {X: at.X + d, Y: at.Y + d}}},
		&scene.Polyline{Shape: plain("ink-line"), Points: []geom.Point{{X: at.X - d, Y: at.Y + d}, {X: at.X + d, Y: at.Y - d}}},
	}
}

func cherry(at geom.Point, d int32) []scene.Primitive {
	dot := int32(geom.FloorDiv(int64(d), 2))
	left, right := geom.Point{X: at.X - d, Y: at.Y - dot}, geom.Point{X: at.X + d, Y: at.Y - dot}
	stem := geom.Point{X: at.X, Y: at.Y + d}
	return []scene.Primitive{
		&scene.Polyline{Shape: plain("ink-line"), Points: []geom.Point{left, stem}},
		&scene.Polyline{Shape: plain("ink-line"), Points: []geom.Point{right, stem}},
		&scene.Ellipse{Shape: plain("ink"), CX: left.X, CY: left.Y, RX: dot, RY: dot},
		&scene.Ellipse{Shape: plain("ink"), CX: right.X, CY: right.Y, RX: dot, RY: dot},
	}
}
