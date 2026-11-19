package lanes

import (
	"cmp"
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type EventLane struct {
	ID    string
	Index int
	Label *Text
}

type EventFrame struct {
	ID       string
	Lane     int
	Category string
	Name     Text
	Data     *Text
}

type EventRelation struct {
	ID   string
	From int
	To   int
}

type EventModelingInput struct {
	Lanes     []EventLane
	Frames    []EventFrame
	Relations []EventRelation
}

type EventModelingResult struct {
	Canvas     geom.Size
	Lanes      []geom.Rect
	LaneLabels []geom.Rect
	Frames     []geom.Rect
	Routes     [][]geom.Point
	Groups     []*scene.Group
}

type eventPoint struct{ x, y int64 }

type eventBox struct{ x, y, w, h int64 }

func (b eventBox) bottom() int64 { return b.y + b.h }

type eventPlanner struct {
	in        EventModelingInput
	c         eventConstants
	profile   scene.Profile
	order     []int
	rank      []int
	frames    []eventBox
	laneY     []int64
	laneH     []int64
	corridors []int64
	gutter    int64
	maxR      int64
	routes    [][]eventPoint
}

func EventModeling(in EventModelingInput, p Params) (EventModelingResult, error) {
	c, err := loadEventConstants(p.Profile)
	if err != nil {
		return EventModelingResult{}, err
	}
	pl := &eventPlanner{in: in, c: c, profile: p.Profile}
	if err := pl.validate(); err != nil {
		return EventModelingResult{}, err
	}
	pl.rankLanes()
	pl.placeColumns()
	pl.placeRows()
	if err := pl.routeRelations(); err != nil {
		return EventModelingResult{}, err
	}
	return pl.result()
}

func (pl *eventPlanner) validate() error {
	for _, frame := range pl.in.Frames {
		if frame.Lane < 0 || frame.Lane >= len(pl.in.Lanes) {
			return geom.ErrDomain
		}
	}
	for _, relation := range pl.in.Relations {
		if min(relation.From, relation.To) < 0 || max(relation.From, relation.To) >= len(pl.in.Frames) {
			return geom.ErrDomain
		}
	}
	return nil
}

func (pl *eventPlanner) rankLanes() {
	pl.order = make([]int, len(pl.in.Lanes))
	for i := range pl.order {
		pl.order[i] = i
	}
	slices.SortFunc(pl.order, func(a, b int) int {
		return cmp.Or(cmp.Compare(pl.in.Lanes[a].Index, pl.in.Lanes[b].Index), cmp.Compare(a, b))
	})
	pl.rank = make([]int, len(pl.order))
	for position, lane := range pl.order {
		pl.rank[lane] = position
	}
}

func clamp(value, low, high int64) int64 { return max(low, min(high, value)) }

func (pl *eventPlanner) frameSize(frame EventFrame) (w, h int64) {
	textW, textH := int64(frame.Name.W), int64(frame.Name.H)
	if frame.Data != nil {
		textW = max(textW, int64(frame.Data.W))
		textH += pl.c.lineHeight + int64(frame.Data.H)
	}
	w = clamp(textW, pl.c.boxMinWidth, pl.c.boxMaxWidth) + 2*pl.c.boxPadding
	h = clamp(textH, pl.c.boxMinHeight, pl.c.boxMaxHeight) + 2*pl.c.boxPadding
	return w, h
}

func (pl *eventPlanner) placeColumns() {
	pl.gutter = pl.c.contentStartX
	for _, lane := range pl.in.Lanes {
		if lane.Label != nil {
			pl.gutter = max(pl.gutter, 2*pl.c.labelInset()+int64(lane.Label.W))
		}
	}
	pl.frames = make([]eventBox, len(pl.in.Frames))
	reach := pl.gutter + pl.c.boxOverlap - pl.c.boxPadding
	floor := make([]int64, len(pl.in.Lanes))
	for i, frame := range pl.in.Frames {
		w, h := pl.frameSize(frame)
		x := max(reach-pl.c.boxOverlap+pl.c.boxPadding, floor[frame.Lane])
		pl.frames[i] = eventBox{x: x, w: w, h: h}
		reach = x + w + pl.c.boxPadding
		floor[frame.Lane] = reach
		pl.maxR = max(pl.maxR, reach)
	}
}

func (pl *eventPlanner) placeRows() {
	n := len(pl.in.Lanes)
	tallest := make([]int64, n)
	for lane := range tallest {
		tallest[lane] = pl.c.laneMinHeight
		if label := pl.in.Lanes[lane].Label; label != nil {
			tallest[lane] = max(tallest[lane], int64(label.H))
		}
	}
	for i, frame := range pl.in.Frames {
		tallest[frame.Lane] = max(tallest[frame.Lane], pl.frames[i].h)
	}
	pl.laneY, pl.laneH = make([]int64, n), make([]int64, n)
	pl.corridors = make([]int64, n+1)
	pl.corridors[0] = geom.FloorDiv(pl.c.lanePadding, 2)
	var y int64
	for position, lane := range pl.order {
		pl.laneY[lane] = y
		pl.laneH[lane] = tallest[lane] + 2*pl.c.lanePadding
		pl.corridors[position+1] = y + pl.laneH[lane] + geom.FloorDiv(pl.c.laneGap, 2)
		y += pl.laneH[lane] + pl.c.laneGap
	}
	for i, frame := range pl.in.Frames {
		pl.frames[i].y = pl.laneY[frame.Lane] + pl.c.lanePadding
	}
}

func (pl *eventPlanner) toGeom(points []eventPoint) ([]geom.Point, error) {
	out := make([]geom.Point, len(points))
	for i, p := range points {
		if abs64(p.x) > geom.CoordLimit || abs64(p.y) > geom.CoordLimit {
			return nil, geom.ErrOverflow
		}
		out[i] = geom.Point{X: int32(p.x), Y: int32(p.y)}
	}
	return out, nil
}

func abs64(v int64) int64 {
	if v < 0 {
		return -v
	}
	return v
}

func (pl *eventPlanner) routeRelations() error {
	pl.routes = make([][]eventPoint, len(pl.in.Relations))
	for i, relation := range pl.in.Relations {
		route, err := pl.route(relation)
		if err != nil {
			return err
		}
		pl.routes[i] = route
	}
	return nil
}

type eventPorts struct {
	from, to       eventPoint
	fromCorridor   int64
	toCorridor     int64
	laneDifference bool
}

func (pl *eventPlanner) ports(relation EventRelation) eventPorts {
	from, to := pl.frames[relation.From], pl.frames[relation.To]
	rankFrom, rankTo := pl.rank[pl.in.Frames[relation.From].Lane], pl.rank[pl.in.Frames[relation.To].Lane]
	start := eventPoint{x: from.x + geom.FloorDiv(2*from.w, 3)}
	end := eventPoint{x: to.x + geom.FloorDiv(to.w, 3)}
	ports := eventPorts{laneDifference: rankFrom != rankTo}
	switch {
	case rankFrom < rankTo:
		start.y, end.y = from.bottom(), to.y
		ports.fromCorridor, ports.toCorridor = pl.corridors[rankFrom+1], pl.corridors[rankTo]
	case rankFrom > rankTo:
		start.y, end.y = from.y, to.bottom()
		ports.fromCorridor, ports.toCorridor = pl.corridors[rankFrom], pl.corridors[rankTo+1]
	default:
		start.y, end.y = from.y, to.y
		ports.fromCorridor, ports.toCorridor = pl.corridors[rankFrom], pl.corridors[rankTo]
	}
	ports.from, ports.to = start, end
	return ports
}

func (pl *eventPlanner) route(relation EventRelation) ([]eventPoint, error) {
	ports := pl.ports(relation)
	if pl.profile == scene.ProfileVector && ports.laneDifference {
		straight := []eventPoint{ports.from, ports.to}
		hit, err := pl.hits(straight, relation)
		if err != nil || !hit {
			return straight, err
		}
	}
	column, err := pl.crossing(ports, relation)
	if err != nil {
		return nil, err
	}
	return tidy([]eventPoint{
		ports.from, {ports.from.x, ports.fromCorridor}, {column, ports.fromCorridor},
		{column, ports.toCorridor}, {ports.to.x, ports.toCorridor}, ports.to,
	}), nil
}

func (pl *eventPlanner) crossing(ports eventPorts, relation EventRelation) (int64, error) {
	for _, column := range []int64{ports.from.x, ports.to.x} {
		hit, err := pl.hits([]eventPoint{{column, ports.fromCorridor}, {column, ports.toCorridor}}, relation)
		if err != nil || !hit {
			return column, err
		}
	}
	return pl.maxR, nil
}

func (pl *eventPlanner) hits(points []eventPoint, relation EventRelation) (bool, error) {
	path, err := pl.toGeom(points)
	if err != nil {
		return false, err
	}
	for i, frame := range pl.frames {
		if i == relation.From || i == relation.To {
			continue
		}
		rect, err := pl.rect(frame)
		if err != nil {
			return false, err
		}
		hit, err := geom.PolylineHitsRect(path, rect)
		if err != nil || hit {
			return hit, err
		}
	}
	return false, nil
}

func (pl *eventPlanner) rect(b eventBox) (geom.Rect, error) {
	if max(abs64(b.x), abs64(b.y), abs64(b.w), abs64(b.h), abs64(b.x+b.w), abs64(b.bottom())) > geom.CoordLimit {
		return geom.Rect{}, geom.ErrOverflow
	}
	return geom.Rect{X: int32(b.x), Y: int32(b.y), W: int32(b.w), H: int32(b.h)}, nil
}

func tidy(points []eventPoint) []eventPoint {
	var out []eventPoint
	for _, p := range points {
		if n := len(out); n > 0 && out[n-1] == p {
			continue
		}
		for n := len(out); n >= 2 && straightThrough(out[n-2], out[n-1], p); n = len(out) {
			out = out[:n-1]
		}
		out = append(out, p)
	}
	return out
}

func straightThrough(a, b, c eventPoint) bool {
	cross := (b.x-a.x)*(c.y-b.y) - (b.y-a.y)*(c.x-b.x)
	dot := (b.x-a.x)*(c.x-b.x) + (b.y-a.y)*(c.y-b.y)
	return cross == 0 && dot > 0
}
