package layout

import (
	"errors"
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

var errSequenceDomain = errors.New("sequence layout: invalid geometry")

type sequenceConstants struct {
	actorWidth, actorHeight, actorMargin, wrapPadding int32
	boxTextMargin, boxMargin, noteMargin              int32
	selfLoopMinDx, selfLoopDepth, messageTop          int32
	labelBoxHeight, labelBoxWidth                     int32
	activationWidth, activationTop                    int32
	diagramMarginX, diagramMarginY, lineHeight        int32
	cornerRadius, autonumberRadius, ruleRadiusUnits   int32
}

func loadSequenceConstants(profile scene.Profile) (sequenceConstants, error) {
	var c sequenceConstants
	required := []struct {
		name string
		into *int32
	}{
		{"actor_width", &c.actorWidth}, {"actor_height", &c.actorHeight}, {"actor_margin", &c.actorMargin},
		{"wrap_padding", &c.wrapPadding}, {"box_text_margin", &c.boxTextMargin}, {"box_margin", &c.boxMargin},
		{"note_margin", &c.noteMargin}, {"self_loop_min_dx", &c.selfLoopMinDx}, {"self_loop_depth", &c.selfLoopDepth},
		{"message_top", &c.messageTop}, {"label_box_height", &c.labelBoxHeight}, {"label_box_width", &c.labelBoxWidth},
		{"activation_width", &c.activationWidth}, {"activation_top", &c.activationTop},
		{"diagram_margin_x", &c.diagramMarginX}, {"diagram_margin_y", &c.diagramMarginY},
	}
	for _, row := range required {
		value, ok := layoutConstant(profile, "sequence."+row.name)
		if !ok {
			return sequenceConstants{}, errSequenceDomain
		}
		*row.into = value
	}
	corner, ok := layoutConstant(profile, "corner_radius")
	if !ok {
		return sequenceConstants{}, errSequenceDomain
	}
	c.cornerRadius = corner
	c.autonumberRadius = 1
	if value, ok := layoutConstant(profile, "sequence.autonumber_radius"); ok {
		c.autonumberRadius = value
	}
	c.lineHeight, c.ruleRadiusUnits = 1280, 512
	if profile == scene.ProfileCell {
		c.lineHeight, c.ruleRadiusUnits = 1, 0
	}
	return c, nil
}

func sequenceMetric(profile scene.Profile, role measure.Role) measure.Metric {
	if profile == scene.ProfileCell {
		return measure.CellMetric()
	}
	return measure.ForRole(role)
}

func half(value int32) int32 { return value >> 1 }

func sequenceWrapTarget(shared bool, override sequenceWrap, width, padding int32) int32 {
	wrapped := shared
	switch override {
	case wrapForced:
		wrapped = true
	case wrapSuppressed:
		wrapped = false
	}
	if !wrapped {
		return geom.I32Max
	}
	return max(width-2*padding, 1)
}

type sequenceWrap uint8

const (
	wrapInherited sequenceWrap = iota
	wrapForced
	wrapSuppressed
)

func boxWrap(box Box) sequenceWrap {
	switch box.Direction {
	case "w":
		return wrapForced
	case "n":
		return wrapSuppressed
	}
	return wrapInherited
}

func widen(gaps []int32, from, to int, need int32) {
	if from >= to || to > len(gaps) {
		return
	}
	var sum int32
	for _, gap := range gaps[from:to] {
		sum += gap
	}
	extra := need - sum
	if extra <= 0 {
		return
	}
	span := int32(to - from)
	share := extra / span
	remainder := extra - share*span
	for i := from; i < to; i++ {
		gaps[i] += share
		if remainder > 0 {
			gaps[i]++
			remainder--
		}
	}
}

func lifelineCentres(widths, gaps []int32) []int32 {
	out := make([]int32, len(widths))
	var centre int32
	if len(widths) > 0 {
		centre = half(widths[0])
	}
	for i := range widths {
		out[i] = centre
		if i < len(gaps) {
			centre += gaps[i]
		}
	}
	return out
}

func widestLine(lines []measure.StyledLine) int32 {
	var widest int32
	for _, line := range lines {
		widest = max(widest, line.Width)
	}
	return widest
}

type sequenceStepKind uint8

const (
	stepMessage sequenceStepKind = iota
	stepNote
	stepFragmentStart
	stepFragmentElse
	stepFragmentEnd
	stepActivateStart
	stepActivateEnd
)

type sequenceStep struct {
	kind                              sequenceStepKind
	from, to, flags, route, destroyed int
	placement, a, b                   int
	boxIndex, fragmentKind, section   int
	actor                             int
}

func decodeSequenceSteps(in Input) []sequenceStep {
	type ordered struct {
		parent int
		step   sequenceStep
	}
	steps := make([]ordered, 0, len(in.RegionSets))
	for _, region := range in.RegionSets {
		value := func(at int) int {
			if at < len(region.Regions) {
				return region.Regions[at]
			}
			return 0
		}
		tag := value(0)
		bits := tag &^ tagMask
		var step sequenceStep
		switch tag & tagMask {
		case tagMessage:
			step = sequenceStep{kind: stepMessage, from: value(1), to: value(2), flags: bits, route: value(3), destroyed: value(4)}
		case tagNote:
			step = sequenceStep{kind: stepNote, placement: (bits >> placementShift) & 3, a: value(1), b: value(2), boxIndex: value(3)}
		case tagFragmentStart:
			step = sequenceStep{kind: stepFragmentStart, fragmentKind: (bits >> 6) & 15, boxIndex: value(1)}
		case tagFragmentElse:
			step = sequenceStep{kind: stepFragmentElse, boxIndex: value(1), section: value(2)}
		case tagFragmentEnd:
			step = sequenceStep{kind: stepFragmentEnd}
		case tagActivateStart:
			step = sequenceStep{kind: stepActivateStart, actor: value(1)}
		default:
			step = sequenceStep{kind: stepActivateEnd, actor: value(1)}
		}
		steps = append(steps, ordered{region.Parent, step})
	}
	slices.SortStableFunc(steps, func(x, y ordered) int { return x.parent - y.parent })
	out := make([]sequenceStep, len(steps))
	for i, s := range steps {
		out[i] = s.step
	}
	return out
}

type sequencePlanner struct {
	in          Input
	profile     scene.Profile
	c           sequenceConstants
	sharedWrap  bool
	actorBoxes  []int
	widths      []int32
	heights     []int32
	centres     []int32
	gaps        []int32
	actorLines  [][]measure.StyledLine
	labelLines  [][]measure.StyledLine
	bandTop     int32
	bandHeight  int32
	shiftX      int32
	shiftY      int32
	bottom      int32
	destroyedY  []optionalCoord
	routeRuns   []sequenceRouteRun
	closed      []closedFrame
	bars        []geom.Rect
	dump        scene.Dump
	routeOwners map[string]struct{}
}

type optionalCoord struct {
	value int32
	set   bool
}

func newSequencePlanner(in Input) (*sequencePlanner, error) {
	c, err := loadSequenceConstants(in.Profile)
	if err != nil {
		return nil, err
	}
	p := &sequencePlanner{in: in, profile: in.Profile, c: c, routeOwners: map[string]struct{}{}}
	for _, config := range in.Options.Config {
		if config.Key == "wrap" && config.Value == "true" {
			p.sharedWrap = true
		}
	}
	for _, route := range in.Routes {
		p.routeOwners[route.ID] = struct{}{}
	}
	if err = p.measureText(); err != nil {
		return nil, err
	}
	p.dump = blankSequenceDump(in)
	p.actorSizes()
	return p, nil
}

func (p *sequencePlanner) measureText() error {
	for index, box := range p.in.Boxes {
		if !isSequenceActor(box) {
			continue
		}
		p.actorBoxes = append(p.actorBoxes, index)
		target := sequenceWrapTarget(p.sharedWrap, boxWrap(box), p.c.actorWidth, p.c.wrapPadding)
		lines, err := measure.StyledLines(box.Text, target, sequenceMetric(p.profile, measure.RoleLabel))
		if err != nil {
			return geom.ErrOverflow
		}
		p.actorLines = append(p.actorLines, lines)
	}
	for _, label := range p.in.Labels {
		wrap := wrapInherited
		if _, owned := p.routeOwners[label.Owner]; owned {
			wrap = p.messageWrap(label.Owner)
		} else if i := slices.IndexFunc(p.in.Boxes, func(b Box) bool { return b.ID == label.Owner }); i >= 0 {
			wrap = boxWrap(p.in.Boxes[i])
		}
		role := measure.RoleLabel
		if label.Role == scene.TextRoleBody {
			role = measure.RoleBody
		}
		target := sequenceWrapTarget(p.sharedWrap, wrap, p.c.actorWidth, p.c.wrapPadding)
		lines, err := measure.StyledLines(label.Text, target, sequenceMetric(p.profile, role))
		if err != nil {
			return geom.ErrOverflow
		}
		p.labelLines = append(p.labelLines, lines)
	}
	return nil
}

func (p *sequencePlanner) messageWrap(owner string) sequenceWrap {
	for _, region := range p.in.RegionSets {
		if len(region.Regions) == 0 || region.Regions[0]&tagMask != tagMessage {
			continue
		}
		route := 0
		if len(region.Regions) > 3 {
			route = region.Regions[3]
		}
		if route < len(p.in.Routes) && p.in.Routes[route].ID == owner {
			return wrapFromBits(region.Regions[0])
		}
	}
	return wrapInherited
}

func wrapFromBits(bits int) sequenceWrap {
	switch {
	case bits&wrapOn != 0:
		return wrapForced
	case bits&wrapOff != 0:
		return wrapSuppressed
	}
	return wrapInherited
}

func (p *sequencePlanner) actorSizes() {
	for ordinal, index := range p.actorBoxes {
		wrapped := p.sharedWrap
		switch boxWrap(p.in.Boxes[index]) {
		case wrapForced:
			wrapped = true
		case wrapSuppressed:
			wrapped = false
		}
		lines := p.actorLines[ordinal]
		textH := int32(len(lines)) * p.c.lineHeight
		width := p.c.actorWidth
		if !wrapped {
			width = max(width, widestLine(lines)+2*p.c.wrapPadding)
		}
		p.widths = append(p.widths, width)
		p.heights = append(p.heights, max(p.c.actorHeight, textH+2*p.c.boxTextMargin))
	}
	for i := 1; i < len(p.widths); i++ {
		p.gaps = append(p.gaps, half(p.widths[i-1]+p.widths[i])+p.c.actorMargin)
	}
	p.centres = lifelineCentres(p.widths, p.gaps)
	for index, box := range p.in.Boxes {
		if isParticipantBox(box) {
			header := int32(len(p.titleLines(index)))*p.c.lineHeight + p.c.boxMargin
			p.bandTop = max(p.bandTop, header)
		}
		if ordinal := slices.Index(p.actorBoxes, index); isSequenceActor(box) && ordinal >= 0 {
			p.bandHeight = max(p.bandHeight, p.heights[ordinal])
		}
	}
}

func isParticipantBox(box Box) bool {
	return box.Role == scene.RoleGroup && box.Shape == ""
}

func (p *sequencePlanner) titlePosition(boxIndex int) int {
	if boxIndex < 0 || boxIndex >= len(p.in.Boxes) {
		return -1
	}
	id := p.in.Boxes[boxIndex].ID
	return slices.IndexFunc(p.in.Labels, func(l Label) bool { return l.Owner == id && strings.HasSuffix(l.ID, ".label") })
}

func (p *sequencePlanner) titleLines(boxIndex int) []measure.StyledLine {
	if position := p.titlePosition(boxIndex); position >= 0 && position < len(p.labelLines) {
		return p.labelLines[position]
	}
	return nil
}

func (p *sequencePlanner) boxLabelWidth(boxIndex int) int32 {
	return widestLine(p.titleLines(boxIndex))
}

func (p *sequencePlanner) labelByID(id string) int {
	return slices.IndexFunc(p.in.Labels, func(l Label) bool { return l.ID == id })
}

func (p *sequencePlanner) widenGaps() {
	for _, step := range decodeSequenceSteps(p.in) {
		switch step.kind {
		case stepMessage:
			p.widenForMessage(step)
		case stepNote:
			p.widenForNote(step)
		}
	}
	p.centres = lifelineCentres(p.widths, p.gaps)
	p.clearParticipantBoxes()
	p.centres = lifelineCentres(p.widths, p.gaps)
}

func (p *sequencePlanner) widenForMessage(step sequenceStep) {
	c := p.c
	var width int32
	if position := p.routeLabelPosition(step.route); position >= 0 && position < len(p.labelLines) {
		width = widestLine(p.labelLines[position])
	}
	need := width + 2*c.wrapPadding
	if step.from == step.to {
		if step.from < len(p.gaps) {
			widen(p.gaps, step.from, step.from+1, max(half(need), c.selfLoopMinDx)+c.actorMargin)
		}
	} else {
		widen(p.gaps, min(step.from, step.to), max(step.from, step.to), need+c.actorMargin)
	}
	if step.flags&flagCreates != 0 && step.to > 0 {
		var toWidth int32
		if step.to < len(p.widths) {
			toWidth = p.widths[step.to]
		}
		p.gaps[step.to-1] += half(toWidth)
	}
}

func (p *sequencePlanner) widenForNote(step sequenceStep) {
	c := p.c
	textW := p.boxLabelWidth(step.boxIndex)
	a, b := step.a, step.b
	var actorW int32
	if a < len(p.widths) {
		actorW = p.widths[a]
	}
	width := max(actorW, textW+2*c.noteMargin)
	sideNeed := half(actorW) + 2*half(c.actorMargin) + width
	switch {
	case step.placement == 2 && a == b:
		need := half(width) + c.actorMargin
		if a > 0 {
			widen(p.gaps, a-1, a, need)
		}
		if a < len(p.gaps) {
			widen(p.gaps, a, a+1, need)
		}
	case step.placement == 2:
		widen(p.gaps, min(a, b), max(a, b), textW+2*c.noteMargin+c.actorMargin)
	case step.placement == 1:
		if a < len(p.gaps) {
			widen(p.gaps, a, a+1, sideNeed)
		}
	default:
		if a > 0 {
			widen(p.gaps, a-1, a, sideNeed)
		}
	}
}

type participantFrame struct {
	first, last int
	extra       int32
}

func (p *sequencePlanner) participantFrames() []participantFrame {
	var frames []participantFrame
	for index, box := range p.in.Boxes {
		if !isParticipantBox(box) {
			continue
		}
		var members []int
		for ordinal, at := range p.actorBoxes {
			if p.in.Boxes[at].Parent == box.ID {
				members = append(members, ordinal)
			}
		}
		if len(members) == 0 {
			continue
		}
		first, last := members[0], members[len(members)-1]
		left := p.centres[first] - half(p.widths[first])
		right := p.centres[last] + p.widths[last] - half(p.widths[last])
		titleW := widestLine(p.titleLines(index))
		extra := max(titleW+2*p.c.wrapPadding-((right-left)+2*p.c.boxTextMargin), 0)
		frames = append(frames, participantFrame{first, last, extra})
	}
	return frames
}

type frameSet struct {
	frames []participantFrame
	margin int32
}

func (s frameSet) reachRight(ordinal int) int32 {
	for _, f := range s.frames {
		if f.last == ordinal {
			return s.margin + (f.extra - half(f.extra))
		}
	}
	return 0
}

func (s frameSet) reachLeft(ordinal int) int32 {
	for _, f := range s.frames {
		if f.first == ordinal {
			return s.margin + half(f.extra)
		}
	}
	return 0
}

func (p *sequencePlanner) clearParticipantBoxes() {
	set := frameSet{frames: p.participantFrames(), margin: p.c.boxTextMargin}
	for _, f := range set.frames {
		if f.first > 0 {
			p.widenForReach(f.first-1, set.reachRight(f.first-1)+set.reachLeft(f.first))
		}
		if f.last+1 < len(p.widths) {
			p.widenForReach(f.last, set.reachRight(f.last)+set.reachLeft(f.last+1))
		}
	}
}

func (p *sequencePlanner) widenForReach(gap int, reach int32) {
	widen(p.gaps, gap, gap+1, p.widths[gap]-half(p.widths[gap])+half(p.widths[gap+1])+reach)
}

func blankSequenceDump(in Input) scene.Dump {
	options := resolveOptions(in.Options)
	options.Profile, options.Direction = in.Profile, in.Direction
	d := scene.Dump{Kind: sequenceKind, Options: options}
	for _, box := range in.Boxes {
		d.Boxes = append(d.Boxes, scene.Box{ID: box.ID, Role: box.Role, Parent: box.Parent, Exclusive: box.Exclusive})
	}
	for _, route := range in.Routes {
		d.Routes = append(d.Routes, scene.Route{ID: route.ID, From: route.From, To: route.To, Orthogonal: route.Orthogonal, MarkerStart: route.MarkerStart, MarkerEnd: route.MarkerEnd, Stroke: route.Line})
	}
	for _, label := range in.Labels {
		d.Labels = append(d.Labels, scene.Label{ID: label.ID, Owner: label.Owner, Text: label.Text})
	}
	return d
}
