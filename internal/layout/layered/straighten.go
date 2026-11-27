package layered

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type straightenContext struct {
	proper  *Proper
	layers  [][]int32
	x, y    []int32
	top     []int32
	routing *Routing
	dx, dy  int64
}

func straightenMerged(out *Layout) error {
	if len(out.straighten) == 0 {
		return nil
	}
	routes := make([]EdgeRoute, len(out.Routes))
	for i, r := range out.Routes {
		points := make([]geom.Point, len(r.Points))
		copy(points, r.Points)
		routes[i] = EdgeRoute{Original: r.Original, ID: r.ID, Points: points}
	}
	byDecl := make(map[int32]int, len(routes))
	for i, r := range routes {
		if r.Original < 0 {
			continue
		}
		if _, dup := byDecl[r.Original]; !dup {
			byDecl[r.Original] = i
		}
	}
	for ci := range out.straighten {
		obstacles := straightenObstacles(out.straighten[ci].proper, out.Boxes)
		if err := straightenComponent(&out.straighten[ci], obstacles, routes, byDecl); err != nil {
			return err
		}
	}
	out.Routes = routes
	return nil
}

func straightenObstacles(p *Proper, boxes []Box) []Box {
	real := make(map[string]struct{}, len(p.Nodes))
	for _, n := range p.Nodes {
		if !n.Dummy && n.Label == nil && n.Border == BorderNone {
			real[n.ID] = struct{}{}
		}
	}
	obstacles := make([]Box, 0, len(boxes))
	for _, b := range boxes {
		if b.Role == scene.RoleNode {
			obstacles = append(obstacles, b)
			continue
		}
		if _, ok := real[b.ID]; ok {
			obstacles = append(obstacles, b)
		}
	}
	return obstacles
}

type straightSpan struct {
	local, top, bottom, column int32
	tailID, headID             string
}

type straightEdge struct {
	ctx     *straightenContext
	routing *Routing
	i       int
	e       ProperEdge
	span    straightSpan
}

func straightenComponent(c *straightenContext, boxes []Box, routes []EdgeRoute, byDecl map[int32]int) error {
	p, r := c.proper, c.routing
	for i, e := range p.Edges {
		if err := (straightEdge{ctx: c, routing: r, i: i, e: e}).straighten(boxes, routes, byDecl); err != nil {
			return err
		}
	}
	return nil
}

func (s straightEdge) straighten(boxes []Box, routes []EdgeRoute, byDecl map[int32]int) error {
	if !straightEligible(s.ctx.proper, s.routing, s.i, s.e) {
		return nil
	}
	span, ok, err := straightSpanOf(s.ctx, s.i, s.e)
	if err != nil || !ok {
		return err
	}
	s.span = span
	decl, free, err := s.admitted(boxes, routes, byDecl)
	if err != nil {
		return err
	}
	at, ok := byDecl[decl]
	if !free || !ok {
		return nil
	}
	points, kept, err := s.rewrite(routes, decl, routes[at].Points)
	if kept {
		routes[at].Points = points
	}
	return err
}

func straightEligible(p *Proper, r *Routing, i int, e ProperEdge) bool {
	if !drawChain(p, e) {
		return false
	}
	tail, head := p.Nodes[e.Tail], p.Nodes[e.Head]
	if tail.Dummy || head.Dummy || tail.Border != BorderNone || head.Border != BorderNone || tail.Label != nil || head.Label != nil {
		return false
	}
	if e.Tail == e.Head {
		return false
	}
	return r.sourceRun(i) == r.SourceX[i] && r.SourceX[i] != r.TargetX[i]
}

func straightSpanOf(c *straightenContext, i int, e ProperEdge) (straightSpan, bool, error) {
	p, r := c.proper, c.routing
	tail, head := p.Nodes[e.Tail], p.Nodes[e.Head]
	tailLeft := int64(c.x[e.Tail]) - int64(tail.W)/2
	headLeft := int64(c.x[e.Head]) - int64(head.W)/2
	lo := max(tailLeft, headLeft)
	hi := min(tailLeft+int64(tail.W), headLeft+int64(head.W))
	if lo > hi {
		return straightSpan{}, false, nil
	}
	cx := straightPort(r.SourceX[i], r.TargetX[i], lo, hi)
	local, err := coordinate(cx)
	if err != nil {
		return straightSpan{}, false, err
	}
	top, err := coordinate(int64(c.y[e.Tail]) + int64(tail.H) + c.dy)
	if err != nil {
		return straightSpan{}, false, err
	}
	bottom, err := coordinate(int64(c.y[e.Head]) + c.dy)
	if err != nil {
		return straightSpan{}, false, err
	}
	if top >= bottom {
		return straightSpan{}, false, nil
	}
	column, err := coordinate(cx + c.dx)
	if err != nil {
		return straightSpan{}, false, err
	}
	return straightSpan{local: local, top: top, bottom: bottom, column: column,
		tailID: tail.ID, headID: head.ID}, true, nil
}

func (s straightEdge) admitted(boxes []Box, routes []EdgeRoute, byDecl map[int32]int) (int32, bool, error) {
	candidate := []geom.Point{{X: s.span.column, Y: s.span.top}, {X: s.span.column, Y: s.span.bottom}}
	clear, err := straightStepClearBoxes(boxes, s.span.tailID, s.span.headID, candidate)
	if err != nil {
		return 0, false, err
	}
	decl := s.ctx.proper.Original[s.e.Original].Decl
	return decl, clear && !straightStepBusy(routes, byDecl, decl, candidate), nil
}

func (s straightEdge) rewrite(routes []EdgeRoute, decl int32, old []geom.Point) ([]geom.Point, bool, error) {
	r := s.routing
	savedSource, savedTarget := r.SourceX[s.i], r.TargetX[s.i]
	hasRun := len(r.SourceRunX) > 0
	var savedRun int32
	if hasRun {
		savedRun = r.SourceRunX[s.i]
	}
	r.SourceX[s.i] = s.span.local
	r.TargetX[s.i] = s.span.local
	if hasRun {
		r.SourceRunX[s.i] = s.span.local
	}
	points, err := straightenChainPoints(s.ctx, s.e)
	if err != nil {
		return nil, false, err
	}
	grew, err := straightCrossingsGrew(routes, decl, old, points)
	if err != nil {
		return nil, false, err
	}
	if !grew && routeBoxContains(old, points) {
		return points, true, nil
	}
	r.SourceX[s.i] = savedSource
	r.TargetX[s.i] = savedTarget
	if hasRun {
		r.SourceRunX[s.i] = savedRun
	}
	return nil, false, nil
}

func routeBoxContains(old, next []geom.Point) bool {
	if len(old) == 0 {
		return len(next) == 0
	}
	x0, y0, x1, y1 := old[0].X, old[0].Y, old[0].X, old[0].Y
	for _, q := range old[1:] {
		x0, y0 = min(x0, q.X), min(y0, q.Y)
		x1, y1 = max(x1, q.X), max(y1, q.Y)
	}
	for _, q := range next {
		if q.X < x0 || q.X > x1 || q.Y < y0 || q.Y > y1 {
			return false
		}
	}
	return true
}

func straightPort(source, target int32, lo, hi int64) int64 {
	if int64(source) >= lo && int64(source) <= hi {
		return int64(source)
	}
	if int64(target) >= lo && int64(target) <= hi {
		return int64(target)
	}
	return lo + (hi-lo)/2
}

func straightStepClearBoxes(boxes []Box, tailID, headID string, candidate []geom.Point) (bool, error) {
	for _, b := range boxes {
		if b.ID == tailID || b.ID == headID {
			continue
		}
		hit, err := geom.PolylineHitsRect(candidate, b.Rect)
		if err != nil {
			return false, err
		}
		if hit {
			return false, nil
		}
	}
	return true, nil
}

func straightStepBusy(routes []EdgeRoute, byDecl map[int32]int, decl int32, candidate []geom.Point) bool {
	cx := int64(candidate[0].X)
	top, bottom := int64(candidate[0].Y), int64(candidate[1].Y)
	for k, r := range routes {
		if byDecl[decl] == k {
			continue
		}
		for s := 1; s < len(r.Points); s++ {
			a, b := r.Points[s-1], r.Points[s]
			if a.X != b.X || int64(a.X) != cx {
				continue
			}
			lo, hi := int64(a.Y), int64(b.Y)
			if lo > hi {
				lo, hi = hi, lo
			}
			if max(top, lo) <= min(bottom, hi) {
				return true
			}
		}
	}
	return false
}

func straightCrossingsGrew(routes []EdgeRoute, decl int32, oldPoints, newPoints []geom.Point) (bool, error) {
	var oldTotal, newTotal int64
	for _, r := range routes {
		if r.Original == decl {
			continue
		}
		oldCount, err := routeCrossings(oldPoints, r.Points)
		if err != nil {
			return false, err
		}
		newCount, err := routeCrossings(newPoints, r.Points)
		if err != nil {
			return false, err
		}
		oldTotal += oldCount
		newTotal += newCount
	}
	return newTotal > oldTotal, nil
}

func straightenChainPoints(c *straightenContext, e ProperEdge) ([]geom.Point, error) {
	p, r := c.proper, c.routing
	g := routeGeometry{p: p, r: r, x: c.x, y: c.y, top: c.top, layers: c.layers}
	params, err := coordinateParams(p)
	if err != nil {
		return nil, err
	}
	g.slot = params.Slot
	g.heights = rankHeights(p, c.layers)
	orig := e.Original
	var points []geom.Point
	chain := p.Chains[orig]
	for k := 0; k+1 < len(chain); k++ {
		step := chainEdgeIndex(p, p.Out[chain[k]], orig)
		if step < 0 || p.Edges[step].Head != chain[k+1] {
			return nil, ErrGraph
		}
		segment, err := g.chainPoints(p.Edges[step], int(step), g.slot)
		if err != nil {
			return nil, err
		}
		points = appendRoutePoints(points, segment)
	}
	final := make([]geom.Point, 0, len(points))
	for _, q := range points {
		xx, err := coordinate(int64(q.X) + c.dx)
		if err != nil {
			return nil, err
		}
		yy, err := coordinate(int64(q.Y) + c.dy)
		if err != nil {
			return nil, err
		}
		final = append(final, geom.Point{X: xx, Y: yy})
	}
	return final, nil
}
