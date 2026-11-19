package layered

import (
	"cmp"
	"container/heap"
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/geom"
)

func endpointPorts(rect geom.Rect) ([4]geom.Point, error) {
	right, err := coordinate(int64(rect.X) + int64(rect.W))
	if err != nil {
		return [4]geom.Point{}, err
	}
	bottom, err := coordinate(int64(rect.Y) + int64(rect.H))
	if err != nil {
		return [4]geom.Point{}, err
	}
	x, err := coordinate(int64(rect.X) + int64(rect.W)/2)
	if err != nil {
		return [4]geom.Point{}, err
	}
	y, err := coordinate(int64(rect.Y) + int64(rect.H)/2)
	if err != nil {
		return [4]geom.Point{}, err
	}
	return [4]geom.Point{{X: rect.X, Y: y}, {X: right, Y: y}, {X: x, Y: rect.Y}, {X: x, Y: bottom}}, nil
}

func forcedPort(points [4]geom.Point, side geom.Side) ([]geom.Point, error) {
	var index int
	var dx, dy int64
	switch side {
	case geom.SideNone:
		return nil, nil
	case geom.SideLeft:
		index, dx, dy = 0, -1, 0
	case geom.SideRight:
		index, dx, dy = 1, 1, 0
	case geom.SideTop:
		index, dx, dy = 2, 0, -1
	case geom.SideBottom:
		index, dx, dy = 3, 0, 1
	default:
		return nil, ErrGraph
	}
	port := points[index]
	x, err := coordinate(int64(port.X) + dx)
	if err != nil {
		return nil, err
	}
	y, err := coordinate(int64(port.Y) + dy)
	if err != nil {
		return nil, err
	}
	return []geom.Point{port, {X: x, Y: y}}, nil
}

func sideSearchPoints(ports [4]geom.Point, pair []geom.Point) []geom.Point {
	if pair == nil {
		return ports[:]
	}
	return pair[1:]
}

func sideHits(a, b geom.Point, rect geom.Rect) bool {
	if rect.W == 0 || rect.H == 0 {
		return false
	}
	if a.Y == b.Y {
		return horizontalHit(a, b, rect)
	}
	return verticalHit(a, b, rect)
}

func horizontalHit(a, b geom.Point, rect geom.Rect) bool {
	right := int64(rect.X) + int64(rect.W)
	bottom := int64(rect.Y) + int64(rect.H)
	return int64(rect.Y) < int64(a.Y) && int64(a.Y) < bottom &&
		min(int64(a.X), int64(b.X)) < right && int64(rect.X) < max(int64(a.X), int64(b.X))
}

func verticalHit(a, b geom.Point, rect geom.Rect) bool {
	right := int64(rect.X) + int64(rect.W)
	bottom := int64(rect.Y) + int64(rect.H)
	return int64(rect.X) < int64(a.X) && int64(a.X) < right &&
		min(int64(a.Y), int64(b.Y)) < bottom && int64(rect.Y) < max(int64(a.Y), int64(b.Y))
}

func gridCollinear(a, b, c geom.Point) bool {
	return a.X == b.X && b.X == c.X || a.Y == b.Y && b.Y == c.Y
}

func checkedSum(a, b int64) (int64, error) {
	sum := a + b
	if (b > 0 && sum < a) || (b < 0 && sum > a) {
		return 0, geom.ErrOverflow
	}
	return sum, nil
}

type gridVertex struct {
	x, y int
	dir  uint8
}

type gridCost struct {
	dist  int64
	turns int
}

func (c gridCost) compare(other gridCost) int {
	if c.dist != other.dist {
		return cmp.Compare(c.dist, other.dist)
	}
	return cmp.Compare(c.turns, other.turns)
}

func (v gridVertex) compare(other gridVertex) int {
	if c := cmp.Compare(v.x, other.x); c != 0 {
		return c
	}
	if c := cmp.Compare(v.y, other.y); c != 0 {
		return c
	}
	return cmp.Compare(v.dir, other.dir)
}

type gridEntry struct {
	cost   gridCost
	vertex gridVertex
}

type gridQueue []gridEntry

func (q gridQueue) Len() int { return len(q) }
func (q gridQueue) Less(i, j int) bool {
	if c := q[i].cost.compare(q[j].cost); c != 0 {
		return c < 0
	}
	return q[i].vertex.compare(q[j].vertex) < 0
}
func (q gridQueue) Swap(i, j int) { q[i], q[j] = q[j], q[i] }
func (q *gridQueue) Push(x any)   { *q = append(*q, x.(gridEntry)) }
func (q *gridQueue) Pop() any {
	old := *q
	item := old[len(old)-1]
	*q = old[:len(old)-1]
	return item
}

type visibilityGrid struct {
	x, y      []int32
	obstacles []geom.Rect
	bound     geom.Rect
	open      bool
}

func rectFarCorner(rect geom.Rect) (int64, int64, error) {
	right := int64(rect.X) + int64(rect.W)
	bottom := int64(rect.Y) + int64(rect.H)
	if _, err := coordinate(right); err != nil {
		return 0, 0, err
	}
	if _, err := coordinate(bottom); err != nil {
		return 0, 0, err
	}
	return right, bottom, nil
}

func narrowAppend(dst []int32, values ...int64) ([]int32, error) {
	for _, v := range values {
		c, err := coordinate(v)
		if err != nil {
			return nil, err
		}
		dst = append(dst, c)
	}
	return dst, nil
}

func (g *visibilityGrid) spreadClearance(rect geom.Rect) error {
	right, bottom, err := rectFarCorner(rect)
	if err != nil {
		return err
	}
	if g.x, err = narrowAppend(g.x, int64(rect.X)-1, right+1); err != nil {
		return err
	}
	g.y, err = narrowAppend(g.y, int64(rect.Y)-1, bottom+1)
	return err
}

func newVisibilityGrid(obstacles []geom.Rect, starts, ends []geom.Point, bound geom.Rect) (*visibilityGrid, error) {
	g := &visibilityGrid{obstacles: obstacles, bound: bound}
	for _, rect := range obstacles {
		if err := g.spreadClearance(rect); err != nil {
			return nil, err
		}
	}
	for _, p := range starts {
		g.x = append(g.x, p.X)
		g.y = append(g.y, p.Y)
	}
	for _, p := range ends {
		g.x = append(g.x, p.X)
		g.y = append(g.y, p.Y)
	}
	right, bottom, err := rectFarCorner(bound)
	if err != nil {
		return nil, err
	}
	if g.x, err = narrowAppend(g.x, int64(bound.X), right); err != nil {
		return nil, err
	}
	if g.y, err = narrowAppend(g.y, int64(bound.Y), bottom); err != nil {
		return nil, err
	}
	g.x = slices.DeleteFunc(g.x, func(v int32) bool { return int64(v) < int64(bound.X) || int64(v) > right })
	g.y = slices.DeleteFunc(g.y, func(v int32) bool { return int64(v) < int64(bound.Y) || int64(v) > bottom })
	slices.Sort(g.x)
	g.x = slices.Compact(g.x)
	slices.Sort(g.y)
	g.y = slices.Compact(g.y)
	return g, nil
}

func (g *visibilityGrid) point(v gridVertex) geom.Point {
	return geom.Point{X: g.x[v.x], Y: g.y[v.y]}
}

func (g *visibilityGrid) vertex(p geom.Point) (gridVertex, error) {
	x, ok := slices.BinarySearch(g.x, p.X)
	if !ok {
		return gridVertex{}, ErrGraph
	}
	y, ok := slices.BinarySearch(g.y, p.Y)
	if !ok {
		return gridVertex{}, ErrGraph
	}
	return gridVertex{x: x, y: y, dir: 2}, nil
}

func (g *visibilityGrid) inside(p geom.Point) bool {
	if g.open {
		return true
	}
	right := int64(g.bound.X) + int64(g.bound.W)
	bottom := int64(g.bound.Y) + int64(g.bound.H)
	return int64(g.bound.X) <= int64(p.X) && int64(p.X) <= right &&
		int64(g.bound.Y) <= int64(p.Y) && int64(p.Y) <= bottom
}

func (g *visibilityGrid) clear(a, b geom.Point) bool {
	if !g.inside(a) || !g.inside(b) {
		return false
	}
	for _, rect := range g.obstacles {
		if sideHits(a, b, rect) {
			return false
		}
	}
	return true
}

func (g *visibilityGrid) checkStub(pair []geom.Point) error {
	if pair == nil {
		return nil
	}
	if !g.clear(pair[0], pair[1]) {
		return ErrGraph
	}
	return nil
}

func (g *visibilityGrid) neighbours(v gridVertex) []gridVertex {
	out := make([]gridVertex, 0, 4)
	if v.x > 0 {
		out = append(out, gridVertex{v.x - 1, v.y, 0})
	}
	if v.x+1 < len(g.x) {
		out = append(out, gridVertex{v.x + 1, v.y, 0})
	}
	if v.y > 0 {
		out = append(out, gridVertex{v.x, v.y - 1, 1})
	}
	if v.y+1 < len(g.y) {
		out = append(out, gridVertex{v.x, v.y + 1, 1})
	}
	return out
}

func (g *visibilityGrid) stepCost(from, to gridVertex, cost gridCost) (gridCost, error) {
	a, b := g.point(from), g.point(to)
	distance := abs64(int64(a.X)-int64(b.X)) + abs64(int64(a.Y)-int64(b.Y))
	sum, err := checkedSum(cost.dist, distance)
	if err != nil {
		return gridCost{}, err
	}
	turns := cost.turns
	if from.dir != 2 && from.dir != to.dir {
		turns++
	}
	return gridCost{dist: sum, turns: turns}, nil
}

func (g *visibilityGrid) shortest(starts, ends []geom.Point) ([]geom.Point, error) {
	frontier := &gridQueue{}
	distances := make(map[gridVertex]gridCost)
	previous := make(map[gridVertex]gridVertex)
	if err := g.seedSearch(frontier, distances, starts); err != nil {
		return nil, err
	}
	return g.runSearch(frontier, distances, previous, ends)
}

func (g *visibilityGrid) seedSearch(frontier *gridQueue, distances map[gridVertex]gridCost, starts []geom.Point) error {
	for _, p := range starts {
		if !g.inside(p) {
			continue
		}
		v, err := g.vertex(p)
		if err != nil {
			return err
		}
		heap.Push(frontier, gridEntry{vertex: v})
		distances[v] = gridCost{}
	}
	return nil
}

func (g *visibilityGrid) runSearch(frontier *gridQueue, distances map[gridVertex]gridCost, previous map[gridVertex]gridVertex, ends []geom.Point) ([]geom.Point, error) {
	for frontier.Len() > 0 {
		entry := heap.Pop(frontier).(gridEntry)
		if current, ok := distances[entry.vertex]; !ok || current != entry.cost {
			continue
		}
		if slices.Contains(ends, g.point(entry.vertex)) {
			return g.reconstruct(entry.vertex, previous), nil
		}
		if err := g.relax(entry, distances, previous, frontier); err != nil {
			return nil, err
		}
	}
	return nil, ErrGraph
}

func (g *visibilityGrid) relax(entry gridEntry, distances map[gridVertex]gridCost, previous map[gridVertex]gridVertex, frontier *gridQueue) error {
	for _, next := range g.neighbours(entry.vertex) {
		if !g.clear(g.point(entry.vertex), g.point(next)) {
			continue
		}
		candidate, err := g.stepCost(entry.vertex, next, entry.cost)
		if err != nil {
			return err
		}
		if old, ok := distances[next]; ok && old.compare(candidate) <= 0 {
			continue
		}
		distances[next] = candidate
		previous[next] = entry.vertex
		heap.Push(frontier, gridEntry{cost: candidate, vertex: next})
	}
	return nil
}

func (g *visibilityGrid) reconstruct(v gridVertex, previous map[gridVertex]gridVertex) []geom.Point {
	points := []geom.Point{g.point(v)}
	for {
		parent, ok := previous[v]
		if !ok {
			break
		}
		points = append(points, g.point(parent))
		v = parent
	}
	slices.Reverse(points)
	result := make([]geom.Point, 0, len(points))
	for _, p := range points {
		if len(result) >= 2 && gridCollinear(result[len(result)-2], result[len(result)-1], p) {
			result = result[:len(result)-1]
		}
		result = append(result, p)
	}
	return result
}
