package layout

import (
	"slices"
	"strconv"

	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type sequenceMarker struct {
	at   geom.Point
	name string
	axis scene.Axis
}

type sequenceRouteRun struct {
	points      []geom.Point
	startMarker *sequenceMarker
	endMarker   *sequenceMarker
	central     []geom.Point
	badge       *geom.Point
}

type sequenceDivider struct {
	row   int32
	label int
}

type closedFrame struct {
	box      int
	dividers []sequenceDivider
}

type fragmentRun struct {
	boxIndex int
	kind     int
	top      int32
	members  []geom.Rect
	dividers []sequenceDivider
}

type barRun struct {
	actor int
	top   int32
	x     int32
	depth int32
}

type sequenceWalk struct {
	pl         *sequencePlanner
	cursor     int32
	boxRects   []geom.Rect
	labelRects []geom.Rect
	routeRuns  []sequenceRouteRun
	fragments  []fragmentRun
	closed     []closedFrame
	openBars   []barRun
	bars       []geom.Rect
	barDepths  []int32
	destroyedY []optionalCoord
	bottom     int32
	err        error
}

func walkSequenceRows(pl *sequencePlanner) *sequenceWalk {
	actors := len(pl.widths)
	w := &sequenceWalk{
		pl:         pl,
		boxRects:   make([]geom.Rect, len(pl.in.Boxes)),
		labelRects: make([]geom.Rect, len(pl.in.Labels)),
		barDepths:  make([]int32, actors),
		destroyedY: make([]optionalCoord, actors),
	}
	w.placeHeaders()
	w.cursor = pl.bandTop + pl.bandHeight + 2*pl.c.boxMargin
	w.bottom = w.cursor
	for _, step := range decodeSequenceSteps(pl.in) {
		w.step(step)
	}
	for len(w.fragments) > 0 {
		w.closeFragment(w.popFragment())
	}
	for len(w.openBars) > 0 {
		bar := w.openBars[len(w.openBars)-1]
		w.openBars = w.openBars[:len(w.openBars)-1]
		w.bars = append(w.bars, geom.Rect{X: bar.x, Y: bar.top, W: pl.c.activationWidth, H: max(w.cursor-bar.top, 0)})
	}
	w.bottom = w.cursor
	return w
}

func (w *sequenceWalk) popFragment() fragmentRun {
	run := w.fragments[len(w.fragments)-1]
	w.fragments = w.fragments[:len(w.fragments)-1]
	return run
}

func (w *sequenceWalk) placeHeaders() {
	pl := w.pl
	c := pl.c
	for ordinal, index := range pl.actorBoxes {
		w.boxRects[index] = geom.Rect{X: pl.centres[ordinal] - half(pl.widths[ordinal]), Y: pl.bandTop, W: pl.widths[ordinal], H: pl.heights[ordinal]}
	}
	for index, box := range pl.in.Boxes {
		if !isParticipantBox(box) {
			continue
		}
		var left, right int32
		first := true
		for candidate, other := range pl.in.Boxes {
			if other.Parent != box.ID {
				continue
			}
			rect := w.boxRects[candidate]
			if first {
				left, right, first = rect.X, rect.X+rect.W, false
				continue
			}
			left, right = min(left, rect.X), max(right, rect.X+rect.W)
		}
		lines := pl.titleLines(index)
		inner := (right - left) + 2*c.boxTextMargin
		extra := max(widestLine(lines)+2*c.wrapPadding-inner, 0)
		header := int32(len(lines))*c.lineHeight + c.boxMargin
		rect := geom.Rect{X: left - c.boxTextMargin - half(extra), Y: pl.bandTop - header, W: inner + extra, H: header + pl.bandHeight + c.boxMargin}
		w.boxRects[index] = rect
		w.centreLabel(pl.labelByID(box.ID+".label"), rect, rect.Y+c.boxTextMargin)
	}
}

func (w *sequenceWalk) sectionHeight(label int) int32 {
	c := w.pl.c
	return max(c.boxMargin+c.boxTextMargin+c.labelBoxHeight, w.labelBottom(label, c.boxMargin+c.boxTextMargin))
}

func (w *sequenceWalk) step(step sequenceStep) {
	switch step.kind {
	case stepMessage:
		w.message(step)
	case stepNote:
		w.note(step)
	case stepFragmentStart:
		w.startFragment(step)
	case stepFragmentElse:
		w.elseFragment(step)
	case stepFragmentEnd:
		if len(w.fragments) > 0 {
			w.closeFragment(w.popFragment())
		}
	case stepActivateStart:
		w.startActivation(step.actor)
	case stepActivateEnd:
		w.endActivation(step.actor)
	}
}

func (w *sequenceWalk) startFragment(step sequenceStep) {
	w.fragments = append(w.fragments, fragmentRun{boxIndex: step.boxIndex, kind: step.fragmentKind, top: w.cursor})
	if step.fragmentKind == fragmentKindCode("rect") {
		w.cursor += w.pl.c.boxMargin
		return
	}
	w.cursor += w.sectionHeight(w.pl.labelByID(w.pl.in.Boxes[step.boxIndex].ID + ".label"))
}

func (w *sequenceWalk) elseFragment(step sequenceStep) {
	pl := w.pl
	label := pl.labelByID(pl.in.Boxes[step.boxIndex].ID + ".s" + strconv.Itoa(step.section))
	if n := len(w.fragments); n > 0 {
		w.fragments[n-1].dividers = append(w.fragments[n-1].dividers, sequenceDivider{row: w.cursor, label: label})
	}
	w.cursor += w.sectionHeight(label)
}

func (w *sequenceWalk) startActivation(actor int) {
	c := w.pl.c
	depth := w.barDepths[actor]
	w.barDepths[actor]++
	w.openBars = append(w.openBars, barRun{actor: actor, top: w.cursor + c.activationTop, x: w.pl.centres[actor] + depth*half(c.activationWidth), depth: depth + 1})
}

func (w *sequenceWalk) endActivation(actor int) {
	depth := max(w.barDepths[actor]-1, 0)
	w.barDepths[actor] = depth
	position := -1
	for i := len(w.openBars) - 1; i >= 0; i-- {
		if w.openBars[i].actor == actor && w.openBars[i].depth == depth+1 {
			position = i
			break
		}
	}
	if position < 0 {
		return
	}
	bar := w.openBars[position]
	w.openBars = slices.Delete(w.openBars, position, position+1)
	w.bars = append(w.bars, geom.Rect{X: bar.x, Y: bar.top, W: w.pl.c.activationWidth, H: max(w.cursor-bar.top, 0)})
}

func (w *sequenceWalk) addMember(rect geom.Rect) {
	if n := len(w.fragments); n > 0 {
		w.fragments[n-1].members = append(w.fragments[n-1].members, rect)
	}
}

func (w *sequenceWalk) actorBox(actor int) (int, bool) {
	if actor < 0 || actor >= len(w.pl.actorBoxes) {
		return 0, false
	}
	return w.pl.actorBoxes[actor], true
}

func (w *sequenceWalk) message(step sequenceStep) {
	pl := w.pl
	c := pl.c
	var lines []measure.StyledLine
	position := pl.routeLabelPosition(step.route)
	hasLabel := position >= 0 && position < len(pl.labelLines)
	if hasLabel {
		lines = pl.labelLines[position]
	}
	count := int32(len(lines))
	labelW := widestLine(lines)
	cFrom, cTo := pl.centres[step.from], pl.centres[step.to]
	y := w.cursor + c.messageTop + count*c.lineHeight
	rowH := c.messageTop + count*c.lineHeight + c.boxMargin
	var dx int32
	if step.from == step.to {
		dx = max(half(labelW+2*c.wrapPadding), c.selfLoopMinDx)
		rowH += c.selfLoopDepth
	}
	rowH += w.createdBox(step, y)
	if step.flags&flagDestroys != 0 && step.destroyed != noDestroyed && step.destroyed < len(w.destroyedY) {
		w.destroyedY[step.destroyed] = optionalCoord{value: y, set: true}
	}
	w.routeRuns = append(w.routeRuns, w.messageRun(step, y, dx))
	if hasLabel {
		w.labelRects[position] = geom.Rect{X: half(cFrom+cTo) - half(labelW), Y: w.cursor + c.messageTop, W: labelW, H: count * c.lineHeight}
	}
	w.addMember(geom.Rect{X: min(cFrom, cTo) - dx, Y: w.cursor, W: (max(cFrom, cTo) - min(cFrom, cTo)) + 2*dx, H: rowH})
	w.cursor += rowH
	w.bottom = max(w.bottom, w.cursor)
}

func (w *sequenceWalk) createdBox(step sequenceStep, y int32) int32 {
	if step.flags&flagCreates == 0 {
		return 0
	}
	boxIndex, ok := w.actorBox(step.to)
	if !ok {
		return 0
	}
	pl := w.pl
	to := step.to
	rect := geom.Rect{X: pl.centres[to] - half(pl.widths[to]), Y: y, W: pl.widths[to], H: pl.heights[to]}
	w.boxRects[boxIndex] = rect
	w.addMember(rect)
	return pl.heights[to] + pl.c.boxMargin
}

func (w *sequenceWalk) messageRun(step sequenceStep, y, dx int32) sequenceRouteRun {
	pl := w.pl
	c := pl.c
	cFrom, cTo := pl.centres[step.from], pl.centres[step.to]
	fromBox, _ := w.actorBox(step.from)
	toBox, _ := w.actorBox(step.to)
	fromBottom := w.boxRects[fromBox].Y + w.boxRects[fromBox].H
	var points []geom.Point
	if step.from == step.to {
		points = []geom.Point{{X: cFrom, Y: fromBottom}, {X: cFrom, Y: y}, {X: cFrom + dx, Y: y}, {X: cFrom + dx, Y: y + c.selfLoopDepth}, {X: cFrom, Y: y + c.selfLoopDepth}, {X: cFrom, Y: fromBottom}}
	} else {
		points = []geom.Point{{X: cFrom, Y: fromBottom}, {X: cFrom, Y: y}, {X: cTo, Y: y}, {X: cTo, Y: w.boxRects[toBox].Y + w.boxRects[toBox].H}}
	}
	run := sequenceRouteRun{points: points}
	w.attachMarkers(&run, step, y)
	if step.flags&flagCentralStart != 0 {
		run.central = append(run.central, geom.Point{X: cFrom, Y: y})
	}
	if step.flags&flagCentralEnd != 0 {
		run.central = append(run.central, geom.Point{X: cTo, Y: y})
	}
	if pl.profile == scene.ProfileVector && step.flags&flagNumbered != 0 {
		run.badge = &geom.Point{X: cFrom, Y: y}
	}
	return run
}

func (w *sequenceWalk) attachMarkers(run *sequenceRouteRun, step sequenceStep, y int32) {
	c := w.pl.c
	cFrom, cTo := w.pl.centres[step.from], w.pl.centres[step.to]
	startAxis := scene.AxisPlusX
	if cTo >= cFrom {
		startAxis = scene.AxisMinusX
	}
	if name, ok := w.routeMarker(step.route, true); ok {
		run.startMarker = &sequenceMarker{at: run.points[1], name: name, axis: startAxis}
	}
	name, ok := w.routeMarker(step.route, false)
	if !ok {
		return
	}
	run.endMarker = &sequenceMarker{at: geom.Point{X: cTo, Y: y}, name: name, axis: endAxis(cFrom, cTo)}
	if step.from == step.to {
		run.endMarker.at = geom.Point{X: cFrom, Y: y + c.selfLoopDepth}
		run.endMarker.axis = scene.AxisMinusX
	}
}

func endAxis(cFrom, cTo int32) scene.Axis {
	if cTo >= cFrom {
		return scene.AxisPlusX
	}
	return scene.AxisMinusX
}

var sequenceMarkerNames = []string{"arrowhead", "crosshead", "filled-head", "solidTopArrowHead", "solidBottomArrowHead", "stickTopArrowHead", "stickBottomArrowHead"}

func (w *sequenceWalk) routeMarker(route int, start bool) (string, bool) {
	if route < 0 || route >= len(w.pl.in.Routes) {
		return "", false
	}
	row := w.pl.in.Routes[route]
	name := row.MarkerEnd
	if start {
		name = row.MarkerStart
	}
	if name == "" || name == "none" || name == "point" || !slices.Contains(sequenceMarkerNames, name) {
		return "", false
	}
	return name, slices.ContainsFunc(gen.Markers, func(m gen.Marker) bool { return m.Name == name })
}

func (p *sequencePlanner) routeLabelPosition(route int) int {
	if route < 0 || route >= len(p.in.Routes) {
		return -1
	}
	id := p.in.Routes[route].ID
	return slices.IndexFunc(p.in.Labels, func(l Label) bool { return l.Owner == id })
}

func (w *sequenceWalk) note(step sequenceStep) {
	pl := w.pl
	c := pl.c
	a, b := step.a, step.b
	textW := pl.boxLabelWidth(step.boxIndex)
	noteID := pl.in.Boxes[step.boxIndex].ID
	position := slices.IndexFunc(pl.in.Labels, func(l Label) bool { return l.Owner == noteID })
	var textH int32
	if position >= 0 && position < len(pl.labelLines) {
		textH = int32(len(pl.labelLines[position])) * c.lineHeight
	}
	cA, cB := pl.centres[a], pl.centres[b]
	var actorW int32
	if a < len(pl.widths) {
		actorW = pl.widths[a]
	}
	width := max(actorW, textW+2*c.noteMargin)
	var x int32
	switch {
	case step.placement == 2 && a == b:
		x = cA - half(width)
	case step.placement == 2:
		left := min(cA, cB) - half(c.actorMargin)
		right := max(cA, cB) + half(c.actorMargin)
		x, width = left, max(right-left, textW+2*c.noteMargin)
	case step.placement == 1:
		x = cA + half(actorW) + half(c.actorMargin)
	default:
		x = cA - half(actorW) - half(c.actorMargin) - width
	}
	top := w.cursor + c.boxMargin
	height := textH + 2*c.noteMargin
	rect := geom.Rect{X: x, Y: top, W: width, H: height}
	w.boxRects[step.boxIndex] = rect
	w.addMember(rect)
	if position >= 0 {
		w.labelRects[position] = geom.Rect{X: x + c.noteMargin, Y: top + c.noteMargin, W: max(width-2*c.noteMargin, 0), H: textH}
	}
	w.cursor += c.boxMargin + height
	w.bottom = max(w.bottom, w.cursor)
}

func (w *sequenceWalk) closeFragment(run fragmentRun) {
	pl := w.pl
	c := pl.c
	var left, right int32
	for i, rect := range run.members {
		if i == 0 {
			left, right = rect.X, rect.X+rect.W
			continue
		}
		left, right = min(left, rect.X), max(right, rect.X+rect.W)
	}
	natural := (right - left) + 2*c.boxMargin
	width := natural
	plain := run.kind == fragmentKindCode("rect")
	if !plain {
		titleLines, err := measure.StyledLines("["+pl.in.Boxes[run.boxIndex].Text+"]", geom.I32Max, sequenceMetric(pl.profile, measure.RoleLabel).WithFontFamily(pl.in.Options.FontFamily))
		if err != nil {
			w.err = geom.ErrOverflow
		}
		titleW := widestLine(titleLines)
		width = max(width, c.labelBoxWidth+2*c.boxMargin, titleW+2*c.boxMargin)
		for _, divider := range run.dividers {
			width = max(width, w.labelWidth(divider.label)+2*c.boxMargin)
		}
	}
	bottom := w.cursor + c.boxMargin
	rect := geom.Rect{X: left - c.boxMargin - half(width-natural), Y: run.top, W: width, H: bottom - run.top}
	w.cursor = bottom
	w.boxRects[run.boxIndex] = rect
	w.bottom = max(w.bottom, bottom)
	if !plain {
		titleTop := c.boxMargin + c.boxTextMargin
		w.centreLabel(pl.labelByID(pl.in.Boxes[run.boxIndex].ID+".label"), rect, run.top+titleTop)
		for _, divider := range run.dividers {
			w.centreLabel(divider.label, rect, divider.row+titleTop)
		}
	}
	w.closed = append(w.closed, closedFrame{box: run.boxIndex, dividers: run.dividers})
	if n := len(w.fragments); n > 0 {
		w.fragments[n-1].members = append(w.fragments[n-1].members, rect)
	}
}

func (w *sequenceWalk) labelBottom(label int, top int32) int32 {
	if label < 0 || label >= len(w.pl.labelLines) {
		return top
	}
	return top + int32(len(w.pl.labelLines[label]))*w.pl.c.lineHeight
}

func (w *sequenceWalk) labelWidth(label int) int32 {
	if label < 0 || label >= len(w.pl.labelLines) {
		return 0
	}
	return widestLine(w.pl.labelLines[label])
}

func (w *sequenceWalk) centreLabel(label int, frame geom.Rect, top int32) {
	if label < 0 || label >= len(w.pl.labelLines) {
		return
	}
	lines := w.pl.labelLines[label]
	width := widestLine(lines)
	w.labelRects[label] = geom.Rect{X: frame.X + half(frame.W-width), Y: top, W: width, H: int32(len(lines)) * w.pl.c.lineHeight}
}
