package grid

import (
	"cmp"
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/geom"
)

type side uint8

const (
	sideTop side = iota
	sideBottom
	sideLeft
	sideRight
	sideCount
)

type direction uint8

const (
	east direction = iota
	west
	south
	north
	directionCount
)

var (
	outward = [sideCount]direction{sideTop: north, sideBottom: south, sideLeft: west, sideRight: east}
	inward  = [sideCount]direction{sideTop: south, sideBottom: north, sideLeft: east, sideRight: west}
)

type lattice struct {
	xs, ys       []int32
	freeH, freeV []bool
}

func (l *lattice) vertex(p geom.Point) (int, bool) {
	i, okX := slices.BinarySearch(l.xs, p.X)
	j, okY := slices.BinarySearch(l.ys, p.Y)
	return i*len(l.ys) + j, okX && okY
}

func (l *lattice) point(v int) geom.Point {
	return geom.Point{X: l.xs[v/len(l.ys)], Y: l.ys[v%len(l.ys)]}
}

func (b *builder) port(r geom.Rect, s side) (geom.Point, geom.Point) {
	pad := int64(b.p.Padding)
	x, y, w, h := int64(r.X), int64(r.Y), int64(r.W), int64(r.H)
	cx, cy := x+w/2, y+h/2
	switch s {
	case sideTop:
		return pointOf(cx, y), pointOf(cx, y-b.gapY+pad)
	case sideBottom:
		return pointOf(cx, y+h), pointOf(cx, y+h+pad)
	case sideLeft:
		return pointOf(x, cy), pointOf(x-b.gapX+pad, cy)
	}
	return pointOf(x+w, cy), pointOf(x+w+pad, cy)
}

func pointOf(x, y int64) geom.Point { return geom.Point{X: int32(x), Y: int32(y)} }

func (b *builder) leaves() []geom.Rect {
	var rects []geom.Rect
	for i, box := range b.in.Boxes {
		if box.Kind == KindLeaf {
			rects = append(rects, b.rects[i])
		}
	}
	return rects
}

const maxLattice = 1 << 20

func (b *builder) buildLattice() (*lattice, error) {
	xs, ys := slices.Clone(b.vlines), slices.Clone(b.hlines)
	for _, e := range b.in.Edges {
		for _, end := range [...]int{e.From, e.To} {
			r := b.rects[end]
			xs, ys = append(xs, int64(r.X)+int64(r.W)/2), append(ys, int64(r.Y)+int64(r.H)/2)
		}
	}
	l := &lattice{xs: sortedUnique(xs), ys: sortedUnique(ys)}
	if len(l.xs)*len(l.ys) > maxLattice {
		return nil, geom.ErrOverflow
	}
	l.freeH, l.freeV = make([]bool, len(l.xs)*len(l.ys)), make([]bool, len(l.xs)*len(l.ys))
	var boxes []obstacle
	for _, r := range b.leaves() {
		boxes = append(boxes, obstacle{x: interval{r.X, r.X + r.W}, y: interval{r.Y, r.Y + r.H}})
	}
	l.fillHorizontal(boxes)
	l.fillVertical(boxes)
	return l, nil
}

type interval struct{ start, end int32 }

type obstacle struct{ x, y interval }

func xRun(o obstacle) interval { return o.x }

func yRun(o obstacle) interval { return o.y }

func (l *lattice) fillHorizontal(boxes []obstacle) {
	ny := len(l.ys)
	for j, y := range l.ys {
		for i, free := range freeRuns(l.xs, blockedRuns(boxes, y, yRun, xRun)) {
			l.freeH[i*ny+j] = free
		}
	}
}

func (l *lattice) fillVertical(boxes []obstacle) {
	ny := len(l.ys)
	for i, x := range l.xs {
		for j, free := range freeRuns(l.ys, blockedRuns(boxes, x, xRun, yRun)) {
			l.freeV[i*ny+j] = free
		}
	}
}

func blockedRuns(boxes []obstacle, at int32, across, along func(obstacle) interval) []interval {
	var runs []interval
	for _, o := range boxes {
		if span := across(o); span.start < at && at < span.end {
			runs = append(runs, along(o))
		}
	}
	slices.SortFunc(runs, func(a, b interval) int {
		return cmp.Or(cmp.Compare(a.start, b.start), cmp.Compare(a.end, b.end))
	})
	var merged []interval
	for _, run := range runs {
		if n := len(merged); n > 0 && run.start < merged[n-1].end {
			merged[n-1].end = max(merged[n-1].end, run.end)
			continue
		}
		merged = append(merged, run)
	}
	return merged
}

func freeRuns(coords []int32, blocked []interval) []bool {
	free := make([]bool, len(coords))
	m := 0
	for i := 0; i+1 < len(coords); i++ {
		for m < len(blocked) && blocked[m].end <= coords[i] {
			m++
		}
		free[i] = m >= len(blocked) || blocked[m].start >= coords[i+1]
	}
	return free
}

type item struct {
	cost  int64
	state int32
}

func less(a, b item) bool { return a.cost < b.cost || a.cost == b.cost && a.state < b.state }

type queue []item

func (q *queue) push(v item) {
	*q = append(*q, v)
	for i := len(*q) - 1; i > 0; {
		parent := (i - 1) / 2
		if !less((*q)[i], (*q)[parent]) {
			break
		}
		(*q)[i], (*q)[parent] = (*q)[parent], (*q)[i]
		i = parent
	}
}

func (q *queue) pop() item {
	top := (*q)[0]
	last := len(*q) - 1
	(*q)[0] = (*q)[last]
	*q = (*q)[:last]
	for i := 0; ; {
		smallest, left, right := i, 2*i+1, 2*i+2
		if left < last && less((*q)[left], (*q)[smallest]) {
			smallest = left
		}
		if right < last && less((*q)[right], (*q)[smallest]) {
			smallest = right
		}
		if smallest == i {
			return top
		}
		(*q)[i], (*q)[smallest] = (*q)[smallest], (*q)[i]
		i = smallest
	}
}

type router struct {
	lat     *lattice
	bend    int64
	crowded int64
	edges   []Edge
	edge    int
	usedH   [][]int32
	usedV   [][]int32
	dist    []int64
	stamp   []uint32
	prev    []int32
	epoch   uint32
	heap    queue
}

func newRouter(lat *lattice, bend int32, edges []Edge) *router {
	cells := len(lat.xs) * len(lat.ys)
	states := cells * int(directionCount)
	return &router{lat: lat, bend: int64(bend), crowded: 4 * int64(bend), edges: edges, usedH: make([][]int32, cells), usedV: make([][]int32, cells), dist: make([]int64, states), stamp: make([]uint32, states), prev: make([]int32, states)}
}

type delta struct{ dx, dy int }

var deltas = [directionCount]delta{east: {1, 0}, west: {-1, 0}, south: {0, 1}, north: {0, -1}}

func (d direction) horizontal() bool { return d == east || d == west }

func (r *router) neighbour(v int, d direction) (int, bool) {
	ny := len(r.lat.ys)
	i, j := v/ny+deltas[d].dx, v%ny+deltas[d].dy
	if i < 0 || i >= len(r.lat.xs) || j < 0 || j >= ny {
		return 0, false
	}
	return i*ny + j, true
}

func (r *router) free(d direction) []bool {
	if d.horizontal() {
		return r.lat.freeH
	}
	return r.lat.freeV
}

func (r *router) used(d direction) [][]int32 {
	if d.horizontal() {
		return r.usedH
	}
	return r.usedV
}

func disjoint(a, b Edge) bool {
	return a.From != b.From && a.From != b.To && a.To != b.From && a.To != b.To
}

func (r *router) crowd(v, u int, d direction) int64 {
	if slices.ContainsFunc(r.used(d)[min(v, u)], func(o int32) bool { return disjoint(r.edges[o], r.edges[r.edge]) }) {
		return r.crowded
	}
	return 0
}

func (r *router) claim(state int) {
	for prev := r.prev[state]; prev >= 0; prev = r.prev[state] {
		d := direction(state % int(directionCount))
		v, u := int(prev)/int(directionCount), state/int(directionCount)
		used := r.used(d)
		used[min(v, u)] = append(used[min(v, u)], int32(r.edge))
		state = int(prev)
	}
}

func (r *router) relax(state int, cost int64, from int32) {
	if r.stamp[state] == r.epoch && r.dist[state] <= cost {
		return
	}
	r.stamp[state], r.dist[state], r.prev[state] = r.epoch, cost, from
	r.heap.push(item{cost, int32(state)})
}

func (r *router) step(v int, d direction) (int, int64, bool) {
	u, ok := r.neighbour(v, d)
	if !ok || !r.free(d)[min(v, u)] {
		return 0, 0, false
	}
	return u, manhattan(r.lat.point(v), r.lat.point(u)), true
}

type end struct {
	port   geom.Point
	vertex int
	stub   int64
}

func (b *builder) ends(lat *lattice, r geom.Rect) ([sideCount]end, error) {
	var out [sideCount]end
	for s := range sideCount {
		port, junction := b.port(r, s)
		v, ok := lat.vertex(junction)
		if !ok {
			return out, geom.ErrDomain
		}
		out[s] = end{port: port, vertex: v, stub: manhattan(port, junction)}
	}
	return out, nil
}

func manhattan(a, b geom.Point) int64 {
	return abs(int64(a.X)-int64(b.X)) + abs(int64(a.Y)-int64(b.Y))
}

func abs(v int64) int64 {
	if v < 0 {
		return -v
	}
	return v
}

func (r *router) turn(from, to direction) int64 {
	if from == to {
		return 0
	}
	return r.bend
}

type arrival struct {
	cost  int64
	state int
	side  side
}

func (r *router) search(sources, targets [sideCount]end) ([]geom.Point, bool) {
	r.epoch++
	r.heap = r.heap[:0]
	for s := range sideCount {
		r.relax(sources[s].vertex*int(directionCount)+int(outward[s]), sources[s].stub, -1-int32(s))
	}
	best := arrival{cost: -1}
	for len(r.heap) > 0 {
		it := r.heap.pop()
		if best.cost >= 0 && it.cost >= best.cost {
			break
		}
		if r.stale(it) {
			continue
		}
		best = r.arrive(it, targets, best)
		r.expand(it)
	}
	if best.cost < 0 {
		return nil, false
	}
	r.claim(best.state)
	return r.assemble(best.state, sources, targets[best.side]), true
}

func (r *router) stale(it item) bool {
	return r.stamp[it.state] != r.epoch || r.dist[it.state] < it.cost
}

func (r *router) arrive(it item, targets [sideCount]end, best arrival) arrival {
	state := int(it.state)
	v, d := state/int(directionCount), direction(state%int(directionCount))
	for s := range sideCount {
		if targets[s].vertex != v {
			continue
		}
		total := it.cost + targets[s].stub + r.turn(d, inward[s])
		if best.cost < 0 || total < best.cost {
			best = arrival{cost: total, state: state, side: s}
		}
	}
	return best
}

func (r *router) expand(it item) {
	state := int(it.state)
	v, d := state/int(directionCount), direction(state%int(directionCount))
	for next := range directionCount {
		if u, length, ok := r.step(v, next); ok {
			r.relax(u*int(directionCount)+int(next), it.cost+length+r.turn(d, next)+r.crowd(v, u, next), it.state)
		}
	}
}

func (r *router) assemble(state int, sources [sideCount]end, target end) []geom.Point {
	points := []geom.Point{target.port}
	for {
		points = append(points, r.lat.point(state/int(directionCount)))
		prev := r.prev[state]
		if prev < 0 {
			points = append(points, sources[-1-prev].port)
			break
		}
		state = int(prev)
	}
	slices.Reverse(points)
	return simplify(points)
}

func simplify(points []geom.Point) []geom.Point {
	out := points[:0:0]
	for _, p := range points {
		if n := len(out); n > 0 && out[n-1] == p {
			continue
		}
		for n := len(out); n >= 2 && collinear(out[n-2], out[n-1], p); n = len(out) {
			out = out[:n-1]
		}
		out = append(out, p)
	}
	return out
}

func collinear(a, b, c geom.Point) bool {
	return a.X == b.X && b.X == c.X || a.Y == b.Y && b.Y == c.Y
}

func (b *builder) loop(r geom.Rect) []geom.Point {
	x, y, w, h := int64(r.X), int64(r.Y), int64(r.W), int64(r.H)
	edge, out := x+w, x+w+int64(b.p.Padding)
	upper, lower := y+h/3, y+2*h/3
	return simplify([]geom.Point{pointOf(edge, upper), pointOf(out, upper), pointOf(out, lower), pointOf(edge, lower)})
}

func (b *builder) route() ([][]geom.Point, error) {
	routes := make([][]geom.Point, len(b.in.Edges))
	if len(routes) == 0 {
		return routes, nil
	}
	lat, err := b.buildLattice()
	if err != nil {
		return nil, err
	}
	rt := newRouter(lat, b.p.BendCost, b.in.Edges)
	for k, e := range b.in.Edges {
		rt.edge = k
		if e.From == e.To {
			routes[k] = b.loop(b.rects[e.From])
			continue
		}
		sources, err := b.ends(lat, b.rects[e.From])
		if err != nil {
			return nil, err
		}
		targets, err := b.ends(lat, b.rects[e.To])
		if err != nil {
			return nil, err
		}
		points, ok := rt.search(sources, targets)
		if !ok {
			return nil, geom.ErrDomain
		}
		routes[k] = points
	}
	return routes, nil
}
