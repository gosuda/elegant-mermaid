package layered

import (
	"cmp"
	"math"
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func clusterIndex(g *Graph, id string) int {
	for i, c := range g.Clusters {
		if c.ID == id {
			return i
		}
	}
	return -1
}
func sourceEndpoint(g *Graph, in Input, r scene.Route) (int32, string) {
	index := clusterIndex(g, r.From)
	if index < 0 {
		return nodeIndex(g, r.From), ""
	}
	cluster := g.Clusters[index]
	if r.From != r.To && inputInside(in, r.To, r.From) {
		return cluster.Top, r.From
	}
	return cluster.Bottom, r.From
}
func targetEndpoint(g *Graph, in Input, r scene.Route) (int32, string) {
	index := clusterIndex(g, r.To)
	if index < 0 {
		return nodeIndex(g, r.To), ""
	}
	cluster := g.Clusters[index]
	if r.From != r.To && inputInside(in, r.From, r.To) {
		return cluster.Bottom, r.To
	}
	return cluster.Top, r.To
}
func modelEdge(g *Graph, in Input, r scene.Route) (Edge, error) {
	tail, source := sourceEndpoint(g, in, r)
	head, target := targetEndpoint(g, in, r)
	edge := Edge{Tail: tail, Head: head, SourceGroup: source, TargetGroup: target}
	if r.From == r.To && inputGroup(in, r.From) {
		edge.FrameLoop = r.From
		edge.Head = edge.Tail
	}
	if edge.Tail < 0 || edge.Head < 0 {
		return Edge{}, ErrGraph
	}
	return edge, nil
}
func inputGroup(in Input, id string) bool {
	for _, b := range in.Boxes {
		if b.ID == id {
			return b.Role == scene.RoleGroup
		}
	}
	return false
}

type proxyPort struct {
	edge, anchor, neighbour, original int32
	end, origin                       proxyEnd
}
type proxyEnd uint8

const (
	proxySource proxyEnd = iota
	proxyTarget
)

func routeChainEnds(p *Proper, original int32) (int32, int32, error) {
	chain := p.Chains[original]
	if len(chain) < 2 {
		return 0, 0, ErrRanking
	}
	first := chainEdgeIndex(p, p.Out[chain[0]], original)
	last := chainEdgeIndex(p, p.In[chain[len(chain)-1]], original)
	if first < 0 || last < 0 {
		return 0, 0, ErrRanking
	}
	return first, last, nil
}
func chainEdgeIndex(p *Proper, indices []int32, original int32) int32 {
	for _, index := range indices {
		if p.Edges[index].Original == original {
			return index
		}
	}
	return -1
}

type horizontalSpan struct{ Lo, Hi int32 }
type proxySide struct {
	anchor int32
	bounds horizontalSpan
}
type proxyGeometry struct {
	proper  *Proper
	routing *Routing
	x       []int32
}

func groupProxyPorts(p *Proper, x []int32, r *Routing) error {
	ports, err := collectProxyPorts(p)
	if err != nil {
		return err
	}
	bounds, err := clusterBounds(p, x)
	if err != nil {
		return err
	}
	r.ClusterBounds = bounds
	geometry := proxyGeometry{proper: p, routing: r, x: x}
	for i, c := range p.Clusters {
		if err := geometry.placeSide(ports, proxySide{anchor: c.Top, bounds: bounds[i]}); err != nil {
			return err
		}
		if err := geometry.placeSide(ports, proxySide{anchor: c.Bottom, bounds: bounds[i]}); err != nil {
			return err
		}
	}
	geometry.installGutters(ports)
	return nil
}
func collectProxyPorts(p *Proper) ([]proxyPort, error) {
	var ports []proxyPort
	for i, edge := range p.Original {
		if edge.Synthetic || edge.SelfLoop() || edge.SourceGroup == "" && edge.TargetGroup == "" {
			continue
		}
		source, target, err := proxyEnds(p, int32(i))
		if err != nil {
			return nil, err
		}
		if edge.SourceGroup != "" {
			ports = append(ports, source)
		}
		if edge.TargetGroup != "" {
			ports = append(ports, target)
		}
	}
	return ports, nil
}
func proxyEnds(p *Proper, index int32) (proxyPort, proxyPort, error) {
	first, last, err := routeChainEnds(p, index)
	if err != nil {
		return proxyPort{}, proxyPort{}, err
	}
	edge := p.Original[index]
	source := proxyPort{edge: first, anchor: edge.Tail, neighbour: p.Edges[first].Head, original: index, end: proxySource, origin: proxySource}
	target := proxyPort{edge: last, anchor: edge.Head, neighbour: p.Edges[last].Tail, original: index, end: proxyTarget, origin: proxyTarget}
	if edge.Reversed {
		source.edge = last
		source.neighbour = p.Edges[last].Tail
		source.end = proxyTarget
		target.edge = first
		target.neighbour = p.Edges[first].Head
		target.end = proxySource
	}
	return source, target, nil
}
func (g proxyGeometry) placeSide(ports []proxyPort, side proxySide) error {
	var selected []proxyPort
	for _, port := range ports {
		if port.anchor == side.anchor {
			selected = append(selected, port)
		}
	}
	slices.SortStableFunc(selected, g.compare)
	var neighbours []int32
	for _, port := range selected {
		if !slices.Contains(neighbours, port.neighbour) {
			neighbours = append(neighbours, port.neighbour)
		}
	}
	width := int64(side.bounds.Hi) - int64(side.bounds.Lo)
	for _, port := range selected {
		index := slices.Index(neighbours, port.neighbour)
		value, err := coordinate(int64(side.bounds.Lo) + int64(index+1)*width/int64(len(neighbours)+1))
		if err != nil {
			return err
		}
		if port.end == proxySource {
			g.routing.SourceX[port.edge] = value
		} else {
			g.routing.TargetX[port.edge] = value
		}
	}
	return nil
}
func (g proxyGeometry) compare(a, b proxyPort) int {
	if d := cmp.Compare(g.x[a.neighbour], g.x[b.neighbour]); d != 0 {
		return d
	}
	if d := cmp.Compare(g.proper.Nodes[a.neighbour].Decl, g.proper.Nodes[b.neighbour].Decl); d != 0 {
		return d
	}
	if d := cmp.Compare(g.proper.Original[a.original].Decl, g.proper.Original[b.original].Decl); d != 0 {
		return d
	}
	return cmp.Compare(a.origin, b.origin)
}
func (g proxyGeometry) installGutters(ports []proxyPort) {
	for i, cluster := range g.proper.Clusters {
		for _, port := range ports {
			if port.anchor == cluster.Top && port.end == proxySource {
				setTopGutter(g.routing, int(port.edge), g.routing.ClusterBounds[i].Lo)
			}
		}
	}
}
func setTopGutter(r *Routing, index int, left int32) {
	if len(r.SourceRunX) == 0 {
		r.SourceRunX = slices.Clone(r.SourceX)
	}
	r.SourceRunX[index] = left
}
func clusterBounds(p *Proper, x []int32) ([]horizontalSpan, error) {
	bounds := make([]horizontalSpan, len(p.Clusters))
	indices := make(map[string]int, len(p.Clusters))
	for i, c := range p.Clusters {
		indices[c.ID] = i
		bounds[i] = horizontalSpan{Lo: math.MaxInt32, Hi: math.MinInt32}
	}
	for i, node := range p.Nodes {
		if node.Border != BorderLeft && node.Border != BorderRight {
			continue
		}
		index, ok := indices[node.Parent]
		if !ok {
			return nil, ErrGraph
		}
		span, err := borderSpan(node, x[i])
		if err != nil {
			return nil, err
		}
		bounds[index].Lo = min(bounds[index].Lo, span.Lo)
		bounds[index].Hi = max(bounds[index].Hi, span.Hi)
	}
	for _, span := range bounds {
		if span.Lo > span.Hi {
			return nil, ErrGraph
		}
	}
	return bounds, nil
}
func borderSpan(node ProperNode, x int32) (horizontalSpan, error) {
	lo, err := coordinate(int64(x) - int64(node.W)/2)
	if err != nil {
		return horizontalSpan{}, err
	}
	hi, err := coordinate(int64(lo) + int64(node.W))
	if err != nil {
		return horizontalSpan{}, err
	}
	return horizontalSpan{Lo: lo, Hi: hi}, nil
}
