package layout

import (
	"cmp"
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func layoutSequence(in Input) (scene.Scene, []diag.Diagnostic, error) {
	pl, err := newSequencePlanner(in)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	pl.widenGaps()
	walk := walkSequenceRows(pl)
	if walk.err != nil {
		return scene.Scene{}, nil, walk.err
	}
	pl.bottom = walk.bottom
	pl.destroyedY = walk.destroyedY
	pl.routeRuns = walk.routeRuns
	pl.closed = walk.closed
	pl.bars = walk.bars
	pl.dump.Canvas = pl.fill(walk)
	return scene.Scene{Dump: pl.dump, Groups: pl.assemble()}, nil, nil
}

func (p *sequencePlanner) fill(w *sequenceWalk) geom.Size {
	c := p.c
	minX, maxX, maxY := p.extent(w)
	p.shiftX, p.shiftY = c.diagramMarginX-minX, c.diagramMarginY
	for i, rect := range w.boxRects {
		p.dump.Boxes[i].Rect = p.shifted(rect)
	}
	for i, run := range w.routeRuns {
		p.dump.Routes[i].Points = p.routePoints(p.in.Routes[i], run, w)
	}
	for i, rect := range w.labelRects {
		p.dump.Labels[i].Rect = p.shifted(rect)
		for _, line := range p.labelLines[i] {
			p.dump.Labels[i].Lines = append(p.dump.Labels[i].Lines, line.Text)
		}
	}
	return geom.Size{W: maxX - minX + 2*c.diagramMarginX, H: maxY + 2*c.diagramMarginY}
}

func (p *sequencePlanner) extent(w *sequenceWalk) (minX, maxX, maxY int32) {
	maxY = w.bottom
	extend := func(rect geom.Rect) {
		minX, maxX, maxY = min(minX, rect.X), max(maxX, rect.X+rect.W), max(maxY, rect.Y+rect.H)
	}
	for _, rect := range w.boxRects {
		extend(rect)
	}
	for _, run := range w.routeRuns {
		for _, point := range run.points {
			minX, maxX, maxY = min(minX, point.X), max(maxX, point.X), max(maxY, point.Y)
		}
	}
	for _, rect := range w.bars {
		extend(rect)
	}
	for _, rect := range w.labelRects {
		if rect.W != 0 || rect.H != 0 {
			extend(rect)
		}
	}
	return minX, maxX, maxY
}

func (p *sequencePlanner) shifted(rect geom.Rect) geom.Rect {
	return geom.Rect{X: rect.X + p.shiftX, Y: rect.Y + p.shiftY, W: rect.W, H: rect.H}
}

func (p *sequencePlanner) shiftedPoint(point geom.Point) geom.Point {
	return geom.Point{X: point.X + p.shiftX, Y: point.Y + p.shiftY}
}

func (p *sequencePlanner) routePoints(route Route, run sequenceRouteRun, w *sequenceWalk) []geom.Point {
	points := make([]geom.Point, len(run.points))
	for i, point := range run.points {
		points[i] = p.shiftedPoint(point)
	}
	port := func(id string) (int32, bool) {
		at := slices.IndexFunc(p.in.Boxes, func(b Box) bool { return b.ID == id })
		if at < 0 || at >= len(w.boxRects) {
			return 0, false
		}
		return w.boxRects[at].Y + w.boxRects[at].H + p.shiftY, true
	}
	if y, ok := port(route.From); ok && len(points) > 0 {
		points[0].Y = y
	}
	if y, ok := port(route.To); ok && len(points) > 0 {
		points[len(points)-1].Y = y
	}
	return points
}

func (p *sequencePlanner) assemble() []*scene.Group {
	var groups []*scene.Group
	if group := p.barGroup(); group != nil {
		groups = append(groups, group)
	}
	groups = append(groups, p.groupFrames()...)
	groups = append(groups, p.edgeGroups()...)
	return append(groups, p.nodeGroups()...)
}

func plainShape(style string) scene.Shape { return scene.Shape{Style: style} }

func (p *sequencePlanner) isCell() bool { return p.profile == scene.ProfileCell }

func (p *sequencePlanner) barGroup() *scene.Group {
	if len(p.bars) == 0 {
		return nil
	}
	var items []scene.Primitive
	for _, bar := range p.bars {
		rect := p.shifted(bar)
		if !p.isCell() {
			items = append(items, &scene.Rect{Shape: plainShape("node"), Rect: rect})
			continue
		}
		heavy := plainShape("node")
		heavy.Width = scene.Width{Kind: scene.WidthEmphasis}
		for _, run := range p.freeRuns(rect.X, rect.Y, rect.Y+rect.H-1) {
			if run.to > run.from {
				items = append(items, &scene.Polyline{Shape: heavy, Points: []geom.Point{{X: rect.X, Y: run.from}, {X: rect.X, Y: run.to}}})
			}
		}
	}
	return &scene.Group{Role: scene.GroupRoleDecor, Items: items}
}

func (p *sequencePlanner) groupFrames() []*scene.Group {
	var groups []*scene.Group
	for index, box := range p.in.Boxes {
		if box.Role != scene.RoleGroup {
			continue
		}
		rect := p.dump.Boxes[index].Rect
		var items []scene.Primitive
		switch {
		case box.Shape == "rect":
			items = append(items, &scene.Rect{Shape: plainShape("band"), Rect: rect})
		case isFragmentShape(box.Shape):
			items = append(items, &scene.Rect{Shape: plainShape("group"), Rect: rect})
			items = p.appendKindBox(items, box.Shape, rect, index)
		default:
			items = append(items, &scene.Rect{Shape: plainShape("group"), Rect: rect})
		}
		if position := p.titlePosition(index); position >= 0 {
			items = append(items, p.labelItem(position))
		}
		groups = append(groups, &scene.Group{Role: scene.GroupRoleGroup, Owner: box.ID, Items: items})
	}
	return groups
}

func (p *sequencePlanner) kindLabelRect(frame geom.Rect) geom.Rect {
	var inset int32
	if p.isCell() {
		inset = 1
	}
	return geom.Rect{X: frame.X + inset, Y: frame.Y + inset, W: p.c.labelBoxWidth, H: p.c.labelBoxHeight}
}

type freeRun struct{ from, to int32 }

func (p *sequencePlanner) freeRuns(column, first, last int32) []freeRun {
	if !p.isCell() {
		return []freeRun{{first, last}}
	}
	blocked := p.blockedRuns(column)
	var runs []freeRun
	from := first
	for _, b := range blocked {
		if b.from > from {
			runs = append(runs, freeRun{from, b.from - 1})
		}
		from = max(from, b.to+1)
	}
	if last >= from {
		runs = append(runs, freeRun{from, last})
	}
	return runs
}

func (p *sequencePlanner) blockedRuns(column int32) []freeRun {
	var blocked []freeRun
	block := func(rect geom.Rect) {
		if rect.W > 0 && rect.H > 0 && rect.X <= column && column < rect.X+rect.W {
			blocked = append(blocked, freeRun{rect.Y, rect.Y + rect.H - 1})
		}
	}
	for _, label := range p.dump.Labels {
		block(label.Rect)
	}
	for i, box := range p.in.Boxes {
		if box.Role == scene.RoleGroup && isFragmentShape(box.Shape) && box.Shape != "rect" {
			block(p.kindLabelRect(p.dump.Boxes[i].Rect))
		}
	}
	slices.SortFunc(blocked, func(a, b freeRun) int { return cmp.Or(cmp.Compare(a.from, b.from), cmp.Compare(a.to, b.to)) })
	return blocked
}

func (p *sequencePlanner) lifelineSegments(centre, top, end int32) [][]geom.Point {
	var segments [][]geom.Point
	for _, run := range p.freeRuns(centre, top, end) {
		if run.to > run.from {
			segments = append(segments, []geom.Point{{X: centre, Y: run.from}, {X: centre, Y: run.to}})
		}
	}
	return segments
}

func (p *sequencePlanner) appendKindBox(items []scene.Primitive, shape string, rect geom.Rect, index int) []scene.Primitive {
	position := p.kindLabelRect(rect)
	style := "text-inverse"
	if p.isCell() {
		style = "text"
	} else {
		items = append(items, &scene.Rect{Shape: plainShape("ink"), Rect: position})
	}
	items = append(items, &scene.Text{Rect: position, Role: scene.TextRoleLabel, Size: 14, Align: scene.AlignMiddle, Style: style, Lines: [][]scene.Run{{{Text: shape}}}})
	right := rect.X + rect.W
	if p.isCell() {
		right--
	}
	for _, divider := range p.dividers(index) {
		y := divider.row + p.shiftY
		dotted := plainShape("rule")
		dotted.Line = scene.LineDotted
		items = append(items, &scene.Polyline{Shape: dotted, Points: []geom.Point{{X: rect.X, Y: y}, {X: right, Y: y}}})
		if divider.label >= 0 {
			items = append(items, p.labelItem(divider.label))
		}
	}
	return items
}

func (p *sequencePlanner) dividers(index int) []sequenceDivider {
	for _, frame := range p.closed {
		if frame.box == index {
			return frame.dividers
		}
	}
	return nil
}

func (p *sequencePlanner) labelItem(position int) scene.Primitive {
	role := scene.TextRoleLabel
	if p.in.Labels[position].Role == scene.TextRoleBody {
		role = scene.TextRoleBody
	}
	return &scene.Text{Rect: p.dump.Labels[position].Rect, Role: role, Size: 14, Align: scene.AlignMiddle, Style: "text", Lines: sequenceRuns(p.labelLines[position])}
}

func sequenceRuns(lines []measure.StyledLine) [][]scene.Run {
	out := make([][]scene.Run, len(lines))
	for i, line := range lines {
		out[i] = make([]scene.Run, len(line.Runs))
		for j, run := range line.Runs {
			out[i][j] = scene.Run{Text: run.Text, Bold: run.Bold, Italic: run.Italic}
		}
	}
	return out
}

func (p *sequencePlanner) edgeGroups() []*scene.Group {
	var groups []*scene.Group
	for index, route := range p.in.Routes {
		if index >= len(p.routeRuns) {
			continue
		}
		groups = append(groups, &scene.Group{Role: scene.GroupRoleEdge, Owner: route.ID, Items: p.edgeItems(index, route)})
	}
	return groups
}

func (p *sequencePlanner) edgeItems(index int, route Route) []scene.Primitive {
	run := p.routeRuns[index]
	shape := plainShape("edge")
	if route.Line == "dotted" {
		shape.Line = scene.LineDotted
	}
	drawn := p.dump.Routes[index].Points
	if len(drawn) > 2 {
		drawn = drawn[1 : len(drawn)-1]
	}
	items := []scene.Primitive{&scene.Polyline{Shape: shape, Corner: p.c.cornerRadius, Points: slices.Clone(drawn)}}
	radius := p.c.autonumberRadius
	for _, point := range run.central {
		items = append(items, p.badge("mark", point, radius))
	}
	if run.badge != nil {
		items = append(items, p.badge("ink", *run.badge, radius))
	}
	for _, marker := range []*sequenceMarker{run.startMarker, run.endMarker} {
		if marker != nil {
			items = append(items, &scene.MarkerRef{Marker: marker.name, At: p.shiftedPoint(marker.at), Axis: marker.axis})
		}
	}
	if position := slices.IndexFunc(p.in.Labels, func(l Label) bool { return l.Owner == route.ID }); position >= 0 {
		items = append(items, p.labelItem(position))
	}
	return items
}

func (p *sequencePlanner) badge(style string, point geom.Point, radius int32) scene.Primitive {
	at := p.shiftedPoint(point)
	return &scene.Ellipse{Shape: plainShape(style), CX: at.X, CY: at.Y, RX: radius, RY: radius}
}

func (p *sequencePlanner) nodeGroups() []*scene.Group {
	var groups []*scene.Group
	for index, box := range p.in.Boxes {
		if box.Role != scene.RoleNode {
			continue
		}
		rect := p.dump.Boxes[index].Rect
		var items []scene.Primitive
		if box.Shape == "note" {
			items = append(items, &scene.Rect{Shape: plainShape("note"), Rect: rect})
		} else {
			items = p.appendActor(items, index, rect)
		}
		if position := p.titlePosition(index); position >= 0 {
			items = append(items, p.labelItem(position))
		}
		groups = append(groups, &scene.Group{Role: scene.GroupRoleNode, Owner: box.ID, Items: items})
	}
	return groups
}

func (p *sequencePlanner) appendActor(items []scene.Primitive, index int, rect geom.Rect) []scene.Primitive {
	ordinal := max(slices.Index(p.actorBoxes, index), 0)
	centre := rect.X + half(rect.W)
	if ordinal < len(p.centres) {
		centre = p.centres[ordinal]
	}
	centre += p.shiftX
	end := p.bottom + p.shiftY
	destroyed := ordinal < len(p.destroyedY) && p.destroyedY[ordinal].set
	if destroyed {
		end = p.destroyedY[ordinal].value + p.shiftY
	}
	items = append(items, &scene.RoundRect{Shape: plainShape("node"), Rect: rect, R: p.c.ruleRadiusUnits})
	for _, points := range p.lifelineSegments(centre, rect.Y+rect.H, end) {
		items = append(items, &scene.Polyline{Shape: plainShape("rule"), Points: points})
	}
	if destroyed {
		items = append(items, &scene.MarkerRef{Marker: "crosshead", At: geom.Point{X: centre, Y: end}, Axis: scene.AxisPlusY})
	}
	if ordinal < len(p.actorLines) && len(p.actorLines[ordinal]) > 0 {
		lines := p.actorLines[ordinal]
		textH := int32(len(lines)) * p.c.lineHeight
		items = append(items, &scene.Text{
			Rect: geom.Rect{X: rect.X, Y: rect.Y + half(rect.H-textH), W: rect.W, H: textH},
			Role: scene.TextRoleLabel, Size: 14, Align: scene.AlignMiddle, Style: "text", Lines: sequenceRuns(lines),
		})
	}
	return items
}
