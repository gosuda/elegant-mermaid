package layout

import (
	"container/heap"
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/cells"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func (a laneAxis) other() laneAxis {
	if a == laneAxisX {
		return laneAxisY
	}
	return laneAxisX
}

func (a laneAxis) at(cross, rank int32) geom.Point {
	if a == laneAxisX {
		return geom.Point{X: cross, Y: rank}
	}
	return geom.Point{X: rank, Y: cross}
}

func originalPoints(s *scene.Scene) [][]geom.Point {
	original := make([][]geom.Point, len(s.Routes))
	for i := range s.Routes {
		original[i] = slices.Clone(s.Routes[i].Points)
	}
	return original
}

func bandIndex(bands []laneBand, id string) int {
	return slices.IndexFunc(bands, func(b laneBand) bool { return b.id == id || slices.Contains(b.members, id) })
}

type gridPoint struct{ cross, rank int64 }

type obstacle struct{ cross0, cross1, rank0, rank1 int64 }

func newObstacle(axis laneAxis, r geom.Rect) obstacle {
	rank := axis.other()
	cross0, rank0 := int64(*axis.start(&r)), int64(*rank.start(&r))
	return obstacle{cross0, cross0 + int64(*axis.length(&r)), rank0, rank0 + int64(*rank.length(&r))}
}

func (o obstacle) crossesRankLine(rank, cross0, cross1 int64) bool {
	return o.rank0 < rank && rank < o.rank1 && cross0 < o.cross1 && o.cross0 < cross1
}

func (o obstacle) crossesCrossLine(cross, rank0, rank1 int64) bool {
	return o.cross0 < cross && cross < o.cross1 && rank0 < o.rank1 && o.rank0 < rank1
}

type routeGrid struct {
	cross, rank []int64
	obstacles   []obstacle
}

func newRouteGrid(obstacles []obstacle, inflate int64, entry, exit gridPoint) *routeGrid {
	cross := []int64{entry.cross, exit.cross}
	rank := []int64{entry.rank, exit.rank}
	for _, o := range obstacles {
		cross = append(cross, o.cross0-inflate, o.cross1+inflate)
		rank = append(rank, o.rank0-inflate, o.rank1+inflate)
	}
	slices.Sort(cross)
	slices.Sort(rank)
	return &routeGrid{cross: slices.Compact(cross), rank: slices.Compact(rank), obstacles: obstacles}
}

func (g *routeGrid) vertex(p gridPoint) int {
	i, _ := slices.BinarySearch(g.cross, p.cross)
	j, _ := slices.BinarySearch(g.rank, p.rank)
	return i*len(g.rank) + j
}

func (g *routeGrid) point(v int) gridPoint {
	return gridPoint{g.cross[v/len(g.rank)], g.rank[v%len(g.rank)]}
}

const (
	moveCrossUp = iota
	moveCrossDown
	moveRankUp
	moveRankDown
	moveCount
)

func (g *routeGrid) neighbour(v, move int) (int, bool) {
	i, j := v/len(g.rank), v%len(g.rank)
	switch move {
	case moveCrossUp:
		i++
	case moveCrossDown:
		i--
	case moveRankUp:
		j++
	default:
		j--
	}
	if i < 0 || i >= len(g.cross) || j < 0 || j >= len(g.rank) {
		return 0, false
	}
	return i*len(g.rank) + j, true
}

func (g *routeGrid) free(a, b gridPoint) bool {
	for _, o := range g.obstacles {
		if a.rank == b.rank && o.crossesRankLine(a.rank, min(a.cross, b.cross), max(a.cross, b.cross)) {
			return false
		}
		if a.cross == b.cross && o.crossesCrossLine(a.cross, min(a.rank, b.rank), max(a.rank, b.rank)) {
			return false
		}
	}
	return true
}

type searchItem struct {
	priority int64
	state    int
}

type searchQueue []searchItem

func (q searchQueue) Len() int { return len(q) }

func (q searchQueue) Less(i, j int) bool {
	return q[i].priority < q[j].priority || (q[i].priority == q[j].priority && q[i].state < q[j].state)
}

func (q searchQueue) Swap(i, j int) { q[i], q[j] = q[j], q[i] }

func (q *searchQueue) Push(x any) { *q = append(*q, x.(searchItem)) }

func (q *searchQueue) Pop() any {
	old := *q
	item := old[len(old)-1]
	*q = old[:len(old)-1]
	return item
}

type routeSearch struct {
	grid               *routeGrid
	start, goal        int
	startMove, endMove int
	bend               int64
	dist               map[int]int64
	pred               map[int]int
	queue              searchQueue
	best               int64
	bestState          int
}

func (s *routeSearch) turn(from, to int) int64 {
	if from == to {
		return 0
	}
	return s.bend
}

func (s *routeSearch) heuristic(v int) int64 {
	p, g := s.grid.point(v), s.grid.point(s.goal)
	return abs64(p.cross-g.cross) + abs64(p.rank-g.rank)
}

func (s *routeSearch) relax(state int, cost int64, move int) {
	v, last := state/moveCount, state%moveCount
	if move == last^1 {
		return
	}
	w, ok := s.grid.neighbour(v, move)
	if !ok {
		return
	}
	a, b := s.grid.point(v), s.grid.point(w)
	if !s.grid.free(a, b) {
		return
	}
	next := cost + abs64(b.cross-a.cross) + abs64(b.rank-a.rank) + s.turn(last, move)
	target := w*moveCount + move
	if known, seen := s.dist[target]; seen && known <= next {
		return
	}
	s.dist[target], s.pred[target] = next, state
	heap.Push(&s.queue, searchItem{next + s.heuristic(w), target})
}

func (s *routeSearch) settle(state int, cost int64) {
	if state/moveCount == s.goal {
		if total := cost + s.turn(state%moveCount, s.endMove); s.best < 0 || total < s.best {
			s.best, s.bestState = total, state
		}
	}
	for move := range moveCount {
		s.relax(state, cost, move)
	}
}

func (s *routeSearch) run() ([]int, bool) {
	s.dist, s.pred = map[int]int64{}, map[int]int{}
	s.best, s.bestState = -1, -1
	first := s.start*moveCount + s.startMove
	s.dist[first] = 0
	heap.Push(&s.queue, searchItem{s.heuristic(s.start), first})
	for s.queue.Len() > 0 {
		item := heap.Pop(&s.queue).(searchItem)
		if s.best >= 0 && item.priority >= s.best {
			break
		}
		cost := item.priority - s.heuristic(item.state/moveCount)
		if known, seen := s.dist[item.state]; seen && known == cost {
			s.settle(item.state, cost)
		}
	}
	if s.best < 0 {
		return nil, false
	}
	return s.path(), true
}

func (s *routeSearch) path() []int {
	var vertices []int
	for state, ok := s.bestState, true; ok; state, ok = s.pred[state] {
		vertices = append(vertices, state/moveCount)
	}
	slices.Reverse(vertices)
	return vertices
}

func abs64(v int64) int64 {
	if v < 0 {
		return -v
	}
	return v
}

type bandRouter struct {
	scene *scene.Scene
	axis  laneAxis
	slot  int64
	bend  int64
}

func routeBetweenBands(s *scene.Scene, axis laneAxis, spacing laneSpacing, bands []laneBand, original [][]geom.Point) error {
	router := bandRouter{scene: s, axis: axis, slot: spacing.slot, bend: spacing.bend}
	for i := range s.Routes {
		route := &s.Routes[i]
		from, to := bandIndex(bands, route.From), bandIndex(bands, route.To)
		if from < 0 || to < 0 || from == to || len(original[i]) < 2 {
			continue
		}
		if err := router.route(route, original[i], bands[from].shift, bands[to].shift); err != nil {
			return err
		}
	}
	return nil
}

func (r *bandRouter) gridPoint(p geom.Point) gridPoint {
	return gridPoint{int64(*r.axis.point(&p)), int64(*r.axis.other().point(&p))}
}

func (r *bandRouter) outward(box geom.Rect, rank int64) int64 {
	other := r.axis.other()
	start, length := int64(*other.start(&box)), int64(*other.length(&box))
	if 2*rank >= 2*start+length {
		return 1
	}
	return -1
}

func (r *bandRouter) moved(p geom.Point, shift int64) (geom.Point, error) {
	sum, err := laneAdd(int64(*r.axis.point(&p)), shift)
	if err != nil {
		return geom.Point{}, err
	}
	value, err := laneNarrow(sum)
	if err != nil {
		return geom.Point{}, err
	}
	*r.axis.point(&p) = value
	return p, nil
}

type routeEnds struct {
	source, target geom.Point
	entry, exit    gridPoint
	startMove      int
	endMove        int
}

func (r *bandRouter) ends(from, to geom.Rect, original []geom.Point, fromShift, toShift int64) (routeEnds, error) {
	source, err := r.moved(original[0], fromShift)
	if err != nil {
		return routeEnds{}, err
	}
	target, err := r.moved(original[len(original)-1], toShift)
	if err != nil {
		return routeEnds{}, err
	}
	s, t := r.gridPoint(source), r.gridPoint(target)
	leave, enter := r.outward(from, s.rank), r.outward(to, t.rank)
	ends := routeEnds{source: source, target: target, entry: gridPoint{s.cross, s.rank + leave*r.slot}, exit: gridPoint{t.cross, t.rank + enter*r.slot}}
	ends.startMove, ends.endMove = moveRankUp, moveRankDown
	if leave < 0 {
		ends.startMove = moveRankDown
	}
	if enter < 0 {
		ends.endMove = moveRankUp
	}
	return ends, nil
}

func (r *bandRouter) obstacles(from, to string) ([]obstacle, error) {
	var out []obstacle
	for i := range r.scene.Boxes {
		box := &r.scene.Boxes[i]
		if box.Exclusive && box.ID != from && box.ID != to {
			out = append(out, newObstacle(r.axis, box.Rect))
		}
	}
	if r.scene.Options.Profile == scene.ProfileCell {
		return r.appendCellTextObstacles(out)
	}
	return out, nil
}

func (r *bandRouter) appendCellTextObstacles(out []obstacle) ([]obstacle, error) {
	for _, group := range r.scene.Groups {
		for _, item := range group.Items {
			label, ok := item.(*scene.Text)
			if !ok {
				continue
			}
			lines, err := cells.PositionedLines(label)
			if err != nil {
				return nil, err
			}
			out = appendLineObstacles(out, r.axis, lines)
		}
	}
	return out, nil
}

func appendLineObstacles(out []obstacle, axis laneAxis, lines []cells.PositionedLine) []obstacle {
	for _, line := range lines {
		if line.Rect.W == 0 {
			continue
		}
		bound := newObstacle(axis, line.Rect)
		bound.cross0--
		bound.cross1++
		bound.rank0--
		bound.rank1++
		out = append(out, bound)
	}
	return out
}

func (r *bandRouter) route(route *scene.Route, original []geom.Point, fromShift, toShift int64) error {
	from, to := sceneBoxIndex(r.scene, route.From), sceneBoxIndex(r.scene, route.To)
	if from < 0 || to < 0 {
		return nil
	}
	ends, err := r.ends(r.scene.Boxes[from].Rect, r.scene.Boxes[to].Rect, original, fromShift, toShift)
	if err != nil {
		return err
	}
	obstacles, err := r.obstacles(route.From, route.To)
	if err != nil {
		return err
	}
	for _, inflate := range [2]int64{r.slot, 0} {
		grid := newRouteGrid(obstacles, inflate, ends.entry, ends.exit)
		search := routeSearch{grid: grid, start: grid.vertex(ends.entry), goal: grid.vertex(ends.exit), startMove: ends.startMove, endMove: ends.endMove, bend: r.bend}
		vertices, found := search.run()
		if !found {
			continue
		}
		points, err := r.polyline(grid, vertices, ends)
		if err != nil {
			return err
		}
		clear, err := r.clear(route, points, grid)
		if err != nil {
			return err
		}
		if clear {
			r.replace(route, points)
			return nil
		}
	}
	return geom.ErrDomain
}

func (r *bandRouter) polyline(grid *routeGrid, vertices []int, ends routeEnds) ([]geom.Point, error) {
	raw := []geom.Point{ends.source}
	for _, v := range vertices {
		p := grid.point(v)
		cross, err := laneNarrow(p.cross)
		if err != nil {
			return nil, err
		}
		rank, err := laneNarrow(p.rank)
		if err != nil {
			return nil, err
		}
		raw = append(raw, r.axis.at(cross, rank))
	}
	raw = append(raw, ends.target)
	var points []geom.Point
	for _, p := range raw {
		if len(points) > 0 && points[len(points)-1] == p {
			continue
		}
		for len(points) >= 2 && collinear(points[len(points)-2], points[len(points)-1], p) {
			points = points[:len(points)-1]
		}
		points = append(points, p)
	}
	return points, nil
}

func collinear(a, b, c geom.Point) bool {
	return (a.X == b.X && b.X == c.X) || (a.Y == b.Y && b.Y == c.Y)
}

func (r *bandRouter) clear(route *scene.Route, points []geom.Point, grid *routeGrid) (bool, error) {
	for i := range r.scene.Boxes {
		box := &r.scene.Boxes[i]
		if !box.Exclusive || box.ID == route.From || box.ID == route.To {
			continue
		}
		hit, err := geom.PolylineHitsRect(points, box.Rect)
		if err != nil || hit {
			return false, err
		}
	}
	return r.clearSegments(points, grid), nil
}

// Search checks entry-to-exit geometry; the assembled source and target stubs
// must clear the identical obstacles before the complete route is admitted.
func (r *bandRouter) clearSegments(points []geom.Point, grid *routeGrid) bool {
	for i := 1; i < len(points); i++ {
		if !grid.free(r.gridPoint(points[i-1]), r.gridPoint(points[i])) {
			return false
		}
	}
	return true
}

func (r *bandRouter) replace(route *scene.Route, points []geom.Point) {
	previous := route.Points
	route.Points = slices.Clone(points)
	for _, group := range r.scene.Groups {
		if group.Role != scene.GroupRoleEdge || group.Owner != route.ID {
			continue
		}
		for _, item := range group.Items {
			switch shape := item.(type) {
			case *scene.Polyline:
				shape.Points = slices.Clone(points)
			case *scene.MarkerRef:
				switch shape.At {
				case previous[0]:
					shape.At = points[0]
				case previous[len(previous)-1]:
					shape.At = points[len(points)-1]
				}
			}
		}
	}
}
