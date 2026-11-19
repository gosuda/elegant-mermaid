package lanes

import (
	"errors"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const NoSection = -1

var ErrTimelineInput = errors.New("timeline layout: period references an unknown section")

type TimelineTitle struct {
	ID    string
	Label Text
}

type TimelineSection struct {
	ID    string
	Label Text
}

type TimelineEvent struct {
	ID    string
	Link  string
	Label Text
}

type TimelinePeriod struct {
	ID      string
	Section int
	Label   Text
	Events  []TimelineEvent
}

type TimelineInput struct {
	Direction scene.Direction
	Title     *TimelineTitle
	Sections  []TimelineSection
	Periods   []TimelinePeriod
}

type TimelineResult struct {
	Canvas   geom.Size
	Title    geom.Rect
	Sections []geom.Rect
	Periods  []geom.Rect
	Events   [][]geom.Rect
	Routes   [][][]geom.Point
	Groups   []*scene.Group
}

type timelinePlanner struct {
	in       TimelineInput
	c        timelineConstants
	profile  scene.Profile
	slot     []int
	first    []int
	span     []int
	cardW    int64
	periodH  int64
	sectionH int64
	title    box
	sections []box
	periods  []box
	events   [][]box
	routes   [][][]vec
	axis     [2]vec
}

func Timeline(in TimelineInput, p Params) (TimelineResult, error) {
	c, err := loadTimelineConstants(p.Profile)
	if err != nil {
		return TimelineResult{}, err
	}
	pl := &timelinePlanner{in: in, c: c, profile: p.Profile}
	if err := pl.assign(); err != nil {
		return TimelineResult{}, err
	}
	pl.size()
	pl.place()
	return pl.result()
}

func (pl *timelinePlanner) vertical() bool { return pl.in.Direction != scene.DirectionLR }

func (pl *timelinePlanner) assign() error {
	pl.slot = make([]int, len(pl.in.Periods))
	pl.first = make([]int, len(pl.in.Sections))
	pl.span = make([]int, len(pl.in.Sections))
	for _, p := range pl.in.Periods {
		if p.Section < NoSection || p.Section >= len(pl.in.Sections) {
			return ErrTimelineInput
		}
	}
	next := pl.fill(NoSection, 0)
	for s := range pl.in.Sections {
		pl.first[s] = next
		pl.span[s] = max(pl.fill(s, next)-next, 1)
		next += pl.span[s]
	}
	return nil
}

func (pl *timelinePlanner) fill(section, base int) int {
	n := base
	for i, p := range pl.in.Periods {
		if p.Section == section {
			pl.slot[i] = n
			n++
		}
	}
	return n
}

func (pl *timelinePlanner) members(section int) []int {
	var out []int
	for i, p := range pl.in.Periods {
		if p.Section == section {
			out = append(out, i)
		}
	}
	return out
}

func (pl *timelinePlanner) bandSlots(section int) int64 {
	if pl.vertical() {
		return 1
	}
	return int64(pl.span[section])
}

func (pl *timelinePlanner) size() {
	pad := 2 * pl.c.cardPadding
	pl.cardW = pl.c.cardWidth
	for _, p := range pl.in.Periods {
		pl.cardW = max(pl.cardW, int64(p.Label.W)+pad)
		pl.periodH = max(pl.periodH, int64(p.Label.H)+pad)
		for _, e := range p.Events {
			pl.cardW = max(pl.cardW, int64(e.Label.W)+pad)
		}
	}
	for s, section := range pl.in.Sections {
		n := pl.bandSlots(s)
		if need := int64(section.Label.W) + pad - (n-1)*pl.c.columnGap; need > 0 {
			pl.cardW = max(pl.cardW, geom.FloorDiv(need+n-1, n))
		}
		pl.sectionH = max(pl.sectionH, int64(section.Label.H)+pad)
	}
}

func (pl *timelinePlanner) contentTop() int64 {
	if pl.in.Title == nil {
		return 0
	}
	return int64(pl.in.Title.Label.H) + pl.c.eventGap
}

func (pl *timelinePlanner) eventHeight(e TimelineEvent) int64 {
	return int64(e.Label.H) + 2*pl.c.cardPadding
}

func (pl *timelinePlanner) place() {
	pl.sections = make([]box, len(pl.in.Sections))
	pl.periods = make([]box, len(pl.in.Periods))
	pl.events = make([][]box, len(pl.in.Periods))
	pl.routes = make([][][]vec, len(pl.in.Periods))
	place := pl.placeHorizontal
	if pl.vertical() {
		place = pl.placeVertical
	}
	left, right := place()
	if t := pl.in.Title; t != nil {
		w := int64(t.Label.W)
		pl.title = box{x: left + half(right-left-w), w: w, h: int64(t.Label.H)}
	}
}

func (pl *timelinePlanner) placeHorizontal() (int64, int64) {
	top := pl.contentTop()
	periodTop := top
	if len(pl.in.Sections) > 0 {
		periodTop += pl.sectionH + pl.c.sectionGap
	}
	pitch := pl.cardW + pl.c.columnGap
	column := func(slot int) int64 { return pl.c.leftMargin + int64(slot)*pitch }
	right := pl.c.leftMargin
	for s := range pl.in.Sections {
		n := int64(pl.span[s])
		pl.sections[s] = box{x: column(pl.first[s]), y: top, w: n*pitch - pl.c.columnGap, h: pl.sectionH}
		right = max(right, pl.sections[s].right())
	}
	bottom := periodTop + pl.periodH
	for i := range pl.in.Periods {
		pl.periods[i] = box{x: column(pl.slot[i]), y: periodTop, w: pl.cardW, h: pl.periodH}
		right = max(right, pl.periods[i].right())
		pl.stackColumn(i, bottom+pl.c.sectionGap)
	}
	axisY := bottom + half(pl.c.sectionGap)
	pl.axis = [2]vec{{x: 0, y: axisY}, {x: right + pl.c.columnGap, y: axisY}}
	return pl.c.leftMargin, right
}

func (pl *timelinePlanner) stackColumn(i int, top int64) {
	period := pl.periods[i]
	cx := period.x + half(pl.cardW)
	above, y := period, top
	for _, e := range pl.in.Periods[i].Events {
		b := box{x: period.x, y: y, w: pl.cardW, h: pl.eventHeight(e)}
		pl.events[i] = append(pl.events[i], b)
		pl.routes[i] = append(pl.routes[i], []vec{{x: cx, y: above.bottom()}, {x: cx, y: b.y}})
		above, y = b, b.bottom()+pl.c.eventGap
	}
}

func (pl *timelinePlanner) placeVertical() (int64, int64) {
	x := pl.c.leftMargin
	eventX := x + pl.cardW + pl.c.columnGap
	axisX := x + pl.cardW + half(pl.c.columnGap)
	top := pl.contentTop()
	y := top
	for section := NoSection; section < len(pl.in.Sections); section++ {
		if section != NoSection {
			pl.sections[section] = box{x: x, y: y, w: pl.cardW, h: pl.sectionH}
			y += pl.sectionH + pl.c.sectionGap
		}
		for _, i := range pl.members(section) {
			y = pl.row(i, y, axisX, eventX) + pl.c.sectionGap
		}
	}
	bottom := max(top, y-pl.c.sectionGap)
	pl.axis = [2]vec{{x: axisX, y: top}, {x: axisX, y: bottom + pl.c.sectionGap}}
	return x, eventX + pl.cardW
}

func (pl *timelinePlanner) row(i int, y, axisX, eventX int64) int64 {
	period := box{x: pl.c.leftMargin, y: y, w: pl.cardW, h: pl.periodH}
	pl.periods[i] = period
	from := vec{x: period.right(), y: y + half(pl.periodH)}
	bottom := period.bottom()
	next := y
	for _, e := range pl.in.Periods[i].Events {
		b := box{x: eventX, y: next, w: pl.cardW, h: pl.eventHeight(e)}
		pl.events[i] = append(pl.events[i], b)
		to := vec{x: b.x, y: b.y + half(b.h)}
		pl.routes[i] = append(pl.routes[i], elbow(from, to, axisX))
		bottom = max(bottom, b.bottom())
		next = b.bottom() + pl.c.eventGap
	}
	return bottom
}

func elbow(from, to vec, axisX int64) []vec {
	if from.y == to.y {
		return []vec{from, to}
	}
	return []vec{from, {x: axisX, y: from.y}, {x: axisX, y: to.y}, to}
}
