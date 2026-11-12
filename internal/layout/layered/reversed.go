package layered

import "github.com/gosuda/elegant-mermaid/internal/geom"

type ReversedRun struct {
	Edge                                               int32
	Lane, SourceX, TargetX, TargetRunX                 int32
	SourceGap, TargetGap, SourceSegment, TargetSegment int32
}

func drawChain(p *Proper, e ProperEdge) bool {
	if e.Original < 0 {
		return false
	}
	if len(p.Original) == 0 {
		return true
	}
	original := p.Original[e.Original]
	return !original.Synthetic && !original.Reversed
}
func reversedRuns(p *Proper, x []int32, r *Routing) error {
	right, maxLabel := reversedLaneBounds(p, x)
	for i, e := range p.Original {
		if !e.Reversed || e.Synthetic || e.SelfLoop() {
			continue
		}
		lane, err := coordinate(right + int64(p.Slot) + int64(len(r.Reversed))*(2*int64(p.Slot)+maxLabel))
		if err != nil {
			return err
		}
		run, err := newReversedRun(p, r, int32(i), lane)
		if err != nil {
			return err
		}
		r.Reversed = append(r.Reversed, run)
	}
	return nil
}

func reversedLaneBounds(p *Proper, x []int32) (int64, int64) {
	var right, maxLabel int64
	for i, n := range p.Nodes {
		right = max(right, int64(x[i])-int64(n.W)/2+int64(n.W)+int64(n.Extent))
	}
	for _, e := range p.Original {
		if e.Reversed && e.Label != nil {
			maxLabel = max(maxLabel, int64(e.Label.W))
		}
	}
	return right, maxLabel
}
func newReversedRun(p *Proper, r *Routing, i, lane int32) (ReversedRun, error) {
	first, last, err := routeChainEnds(p, i)
	if err != nil {
		return ReversedRun{}, err
	}
	e := p.Original[i]
	run := ReversedRun{Edge: i, Lane: lane, SourceX: r.TargetX[last], TargetX: r.SourceX[first], TargetRunX: r.sourceRun(int(first)), SourceGap: p.Rank[e.Tail] - 1, TargetGap: p.Rank[e.Head]}
	run.SourceSegment = appendReversedSegment(&r.Gaps[run.SourceGap], run.SourceX, lane, e.Decl, 0)
	run.TargetSegment = appendReversedSegment(&r.Gaps[run.TargetGap], run.TargetRunX, lane, e.Decl, 1)
	return run, nil
}
func appendReversedSegment(gap *RoutingGap, x, lane, decl, order int32) int32 {
	index := int32(len(gap.Segments))
	gap.Segments = append(gap.Segments, RoutingSegment{Tail: -1, Head: -1, Decl: decl, Slot: -1, SourceX: x, TargetX: lane, Order: order})
	return index
}
func (g routeGeometry) slotLine(gap, index int32) (int32, error) {
	slot := g.r.Gaps[gap].Segments[index].Slot
	return coordinate(int64(g.top[gap]) + int64(g.heights[gap]) + int64(g.slot)*(int64(slot)+1) + int64(g.slot)/2)
}
func (g routeGeometry) reversedPoints(routes []EdgeRoute, labels *labelPlacement) error {
	p, y, r := g.p, g.y, g.r
	for _, run := range r.Reversed {
		cs, err := g.slotLine(run.SourceGap, run.SourceSegment)
		if err != nil {
			return err
		}
		ct, err := g.slotLine(run.TargetGap, run.TargetSegment)
		if err != nil {
			return err
		}
		e := p.Original[run.Edge]
		bottom, err := coordinate(int64(y[e.Head]) + int64(p.Nodes[e.Head].H))
		if err != nil {
			return err
		}
		routes[run.Edge].Points = appendRoutePoints(nil, []geom.Point{{X: run.SourceX, Y: y[e.Tail]}, {X: run.SourceX, Y: cs}, {X: run.Lane, Y: cs}, {X: run.Lane, Y: ct}, {X: run.TargetRunX, Y: ct}, {X: run.TargetRunX, Y: bottom}, {X: run.TargetX, Y: bottom}})
		if err := reversedLabel(p, run, laneLines{source: cs, target: ct}, labels); err != nil {
			return err
		}
	}
	return nil
}

type laneLines struct{ source, target int32 }

func reversedLabel(p *Proper, run ReversedRun, lines laneLines, labels *labelPlacement) error {
	label := p.Original[run.Edge].Label
	if label == nil {
		return nil
	}
	rect, err := rectangle(int64(run.Lane)+int64(p.Slot), (int64(lines.source)+int64(lines.target))/2-int64(label.H)/2, int64(label.W), int64(label.H))
	if err != nil {
		return err
	}
	return labels.stack(label, rect, rect, p.Slot)
}
