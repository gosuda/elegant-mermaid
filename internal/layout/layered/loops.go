package layered

import "github.com/gosuda/elegant-mermaid/internal/geom"

func loopBand(g *Graph, v int32) int64 {
	band := 2 * int64(g.Slot)
	for _, e := range g.Edges {
		if e.Tail == v && e.NodeLoop() && e.Label != nil {
			band = max(band, int64(e.Label.H))
		}
	}
	return band
}
func sizeLoops(g *Graph) error {
	for v := range g.Nodes {
		count, extent, err := nodeLoopExtent(g, int32(v))
		if err != nil {
			return err
		}
		reserved, err := product(2*count, loopBand(g, int32(v)))
		if err != nil {
			return err
		}
		h, err := coordinate(max(int64(g.Nodes[v].H), reserved))
		if err != nil {
			return err
		}
		ex, err := coordinate(extent)
		if err != nil {
			return err
		}
		g.Nodes[v].H = h
		g.Nodes[v].Extent = ex
	}
	return nil
}
func nodeLoopExtent(g *Graph, v int32) (int64, int64, error) {
	var count, extent int64
	for _, e := range g.Edges {
		if !e.NodeLoop() || e.Tail != v {
			continue
		}
		term, err := product(int64(g.Slot), count+2)
		if err != nil {
			return 0, 0, err
		}
		width := int64(0)
		if e.Label != nil {
			width = int64(e.Label.W)
		}
		arithmetic := coordinateArithmetic{}
		extent = arithmetic.add(extent, arithmetic.add(term, width))
		if arithmetic.err != nil {
			return 0, 0, arithmetic.err
		}
		count++
	}
	return count, extent, nil
}
func Loops(g *Graph, boxes []Box) ([]EdgeRoute, error) {
	if err := validateGraph(g); err != nil {
		return nil, err
	}
	if g.Slot <= 0 {
		return nil, ErrGraph
	}
	if len(boxes) != len(g.Nodes) {
		return nil, ErrGraph
	}
	counts := make([]int64, len(g.Nodes))
	var out []EdgeRoute
	for i, e := range g.Edges {
		if !e.NodeLoop() {
			continue
		}
		points, err := loopPoints(boxes[e.Tail].Rect, int64(g.Slot), loopBand(g, e.Tail), counts[e.Tail])
		if err != nil {
			return nil, err
		}
		counts[e.Tail]++
		out = append(out, EdgeRoute{Original: int32(i), Points: points})
	}
	return out, nil
}
func loopPoints(b geom.Rect, slot, band, index int64) ([]geom.Point, error) {
	right, err := coordinate(int64(b.X) + int64(b.W))
	if err != nil {
		return nil, err
	}
	arithmetic := coordinateArithmetic{}
	laneValue := arithmetic.add(int64(right), arithmetic.multiply(slot, index+1))
	yaValue := arithmetic.subtract(arithmetic.add(int64(b.Y), arithmetic.add(arithmetic.multiply(index, band), band/2)), slot)
	if arithmetic.err != nil {
		return nil, arithmetic.err
	}
	lane, err := coordinate(laneValue)
	if err != nil {
		return nil, err
	}
	ya, err := coordinate(yaValue)
	if err != nil {
		return nil, err
	}
	yb, err := coordinate(int64(ya) + 2*slot)
	if err != nil {
		return nil, err
	}
	return []geom.Point{{X: right, Y: ya}, {X: lane, Y: ya}, {X: lane, Y: yb}, {X: right, Y: yb}}, nil
}
func loopLabels(g *Graph, boxes []Box) (labelPlacement, error) {
	counts := make([]int64, len(g.Nodes))
	totals := make([]int64, len(g.Nodes))
	for _, e := range g.Edges {
		if e.NodeLoop() {
			totals[e.Tail]++
		}
	}
	var out labelPlacement
	for _, e := range g.Edges {
		if !e.NodeLoop() {
			continue
		}
		k := counts[e.Tail]
		counts[e.Tail]++
		if e.Label == nil {
			continue
		}
		rect, err := loopLabelRect(g, e, boxes[e.Tail].Rect, k, totals[e.Tail])
		if err != nil {
			return out, err
		}
		if err := out.stack(e.Label, rect, rect, g.Slot); err != nil {
			return out, err
		}
	}
	return out, nil
}
func loopLabelRect(g *Graph, edge Edge, box geom.Rect, index, total int64) (geom.Rect, error) {
	band := loopBand(g, edge.Tail)
	arithmetic := coordinateArithmetic{}
	x := arithmetic.add(int64(box.X)+int64(box.W), arithmetic.multiply(int64(g.Slot), total+1))
	center := arithmetic.add(int64(box.Y), arithmetic.add(arithmetic.multiply(index, band), band/2))
	y := arithmetic.subtract(center, int64(edge.Label.H)/2)
	if arithmetic.err != nil {
		return geom.Rect{}, arithmetic.err
	}
	return rectangle(x, y, int64(edge.Label.W), int64(edge.Label.H))
}

func loopExtents(g *Graph, boxes []Box) ([]Box, error) {
	counts := make([]int64, len(g.Nodes))
	for _, e := range g.Edges {
		if e.NodeLoop() {
			counts[e.Tail]++
		}
	}
	var out []Box
	for i, n := range g.Nodes {
		if counts[i] == 0 {
			continue
		}
		x, err := coordinate(int64(boxes[i].Rect.X) + int64(n.W))
		if err != nil {
			return nil, err
		}
		h, err := coordinate(counts[i] * loopBand(g, int32(i)))
		if err != nil {
			return nil, err
		}
		out = append(out, Box{ID: n.ID, Rect: geom.Rect{X: x, Y: boxes[i].Rect.Y, W: n.Extent, H: h}})
	}
	return out, nil
}
