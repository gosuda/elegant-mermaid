package layered

import "github.com/gosuda/elegant-mermaid/internal/geom"

type loopSite struct {
	rect                     geom.Rect
	slot, band, index, total int64
}

func sizeExactLoops(g *Graph, v int32) error {
	var count, widest int64
	for _, e := range g.Edges {
		if !e.NodeLoop() || e.Tail != v {
			continue
		}
		if e.Label != nil {
			widest = max(widest, int64(e.Label.W))
		}
		count++
	}
	extent := widest
	if count > 0 {
		term, err := product(int64(g.Slot), 2*count+1)
		if err != nil {
			return err
		}
		arithmetic := coordinateArithmetic{}
		extent = arithmetic.add(term, widest)
		if arithmetic.err != nil {
			return arithmetic.err
		}
	}
	ex, err := coordinate(extent)
	if err != nil {
		return err
	}
	g.Nodes[v].Extent = ex
	return nil
}

func (s loopSite) exactPoints() ([]geom.Point, error) {
	right, err := coordinate(int64(s.rect.X) + int64(s.rect.W))
	if err != nil {
		return nil, err
	}
	arithmetic := coordinateArithmetic{}
	denominator := 2*s.total + 1
	endA := arithmetic.add(int64(s.rect.Y), arithmetic.multiply(2*s.index+1, int64(s.rect.H))/denominator)
	endB := arithmetic.add(int64(s.rect.Y), arithmetic.multiply(2*s.index+2, int64(s.rect.H))/denominator)
	laneA := arithmetic.add(int64(right), arithmetic.multiply(s.slot, 2*s.index+1))
	laneB := arithmetic.add(int64(right), arithmetic.multiply(s.slot, 2*s.index+2))
	centre := arithmetic.add(int64(s.rect.Y), arithmetic.add(arithmetic.multiply(s.index, s.band), s.band/2))
	turn := arithmetic.add(centre, s.slot)
	if arithmetic.err != nil {
		return nil, arithmetic.err
	}
	coordinates := [...]int64{endA, laneA, turn, laneB, endB}
	var narrowed [len(coordinates)]int32
	for i, value := range coordinates {
		narrowed[i], err = coordinate(value)
		if err != nil {
			return nil, err
		}
	}
	ea, la, b, lb, eb := narrowed[0], narrowed[1], narrowed[2], narrowed[3], narrowed[4]
	return []geom.Point{{X: right, Y: ea}, {X: la, Y: ea}, {X: la, Y: b}, {X: lb, Y: b}, {X: lb, Y: eb}, {X: right, Y: eb}}, nil
}

func loopLabelFactor(g *Graph, tail int32, total int64) int64 {
	if g.Nodes[tail].Exact {
		return 2*total + 1
	}
	return total + 1
}

func exactHeight(n Node, rect geom.Rect) int64 {
	if n.Exact {
		return int64(rect.H)
	}
	return 0
}

type exactRanks struct {
	g       *Graph
	p       *Proper
	y, top  []int32
	heights []int32
}

func reserveExactRanks(g *Graph, p *Proper, layers [][]int32, y, top []int32) error {
	extra, err := exactRanks{g: g, p: p, y: y, top: top, heights: rankHeights(p, layers)}.extra()
	if err != nil {
		return err
	}
	if err := offsetRanks(top, extra); err != nil {
		return err
	}
	return offsetRankedRows(p, y, extra)
}

func (r exactRanks) extra() ([]int64, error) {
	counts := make([]int64, len(r.g.Nodes))
	for _, e := range r.g.Edges {
		if e.NodeLoop() {
			counts[e.Tail]++
		}
	}
	extra := make([]int64, len(r.top))
	for i, count := range counts {
		if count == 0 || !r.g.Nodes[i].Exact {
			continue
		}
		reserved, err := product(count, loopBand(r.g, int32(i)))
		if err != nil {
			return nil, err
		}
		reserved = max(reserved, int64(r.g.Nodes[i].H))
		rank := r.p.Rank[i]
		extra[rank] = max(extra[rank], int64(r.y[i])+reserved-int64(r.top[rank])-int64(r.heights[rank]))
	}
	return extra, nil
}

func offsetRanks(top []int32, extra []int64) error {
	var shift int64
	for rank := range top {
		shifted, err := coordinate(int64(top[rank]) + shift)
		if err != nil {
			return err
		}
		top[rank] = shifted
		added := extra[rank]
		extra[rank] = shift
		next, err := coordinate(shift + added)
		if err != nil {
			return err
		}
		shift = int64(next)
	}
	return nil
}

func offsetRankedRows(p *Proper, y []int32, offsets []int64) error {
	for v := range y {
		moved, err := coordinate(int64(y[v]) + offsets[p.Rank[v]])
		if err != nil {
			return err
		}
		y[v] = moved
	}
	return nil
}
