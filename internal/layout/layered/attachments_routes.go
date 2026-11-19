package layered

import (
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type attachmentRouting struct {
	graph     *Graph
	boxes     map[string]geom.Rect
	obstacles []geom.Rect
}

func (x attachmentExpansion) reconnect(result *Layout, routes expandedRoutes) error {
	routing := newAttachmentRouting(x.graph, *result)
	if err := x.rerouteAffected(routing, routes); err != nil {
		return err
	}
	if err := x.rerouteUnrouted(routing, routes); err != nil {
		return err
	}
	out := make([]EdgeRoute, 0, len(x.graph.Edges)+len(routes.extra))
	for _, e := range x.graph.Edges {
		if !e.Synthetic {
			out = append(out, EdgeRoute{Original: e.Decl, ID: e.ID, Points: routes.points[e.ID]})
		}
	}
	result.Routes = append(out, routes.extra...)
	return nil
}

func (x attachmentExpansion) rerouteAffected(routing attachmentRouting, routes expandedRoutes) error {
	for _, index := range x.contraction.kept {
		e := x.graph.Edges[index]
		if !x.affected(e) {
			continue
		}
		points, err := routing.route(e)
		if err != nil {
			return err
		}
		routes.points[e.ID] = points
	}
	return nil
}

func (x attachmentExpansion) rerouteUnrouted(routing attachmentRouting, routes expandedRoutes) error {
	for _, e := range x.graph.Edges {
		if e.Synthetic || len(routes.points[e.ID]) > 0 && !x.resizedEndpoint(e) {
			continue
		}
		points, err := routing.route(e)
		if err != nil {
			return err
		}
		routes.points[e.ID] = points
	}
	return nil
}

func (x attachmentExpansion) affected(e Edge) bool {
	for _, b := range x.bundles {
		if b.part.mask[e.Tail] || b.part.mask[e.Head] {
			return true
		}
		for _, note := range b.notes {
			if note.node == e.Tail || note.node == e.Head {
				return true
			}
		}
	}
	return false
}

func (x attachmentExpansion) resizedEndpoint(e Edge) bool {
	if e.Tail == e.Head {
		return false
	}
	tail, head := edgeEndpointIDs(x.graph, e)
	for _, b := range x.bundles {
		if (b.growth.W > 0 || b.growth.H > 0) && (tail == b.target.id || head == b.target.id) {
			return true
		}
	}
	return false
}

func newAttachmentRouting(g *Graph, result Layout) attachmentRouting {
	routing := attachmentRouting{graph: g, boxes: make(map[string]geom.Rect, len(result.Boxes))}
	for _, box := range result.Boxes {
		if _, ok := routing.boxes[box.ID]; !ok {
			routing.boxes[box.ID] = box.Rect
		}
	}
	labels, titles := fixedInnerText(g)
	for _, label := range result.Labels {
		if !labels[label.ID] {
			routing.obstacles = append(routing.obstacles, label.Rect)
		}
	}
	for _, title := range result.Titles {
		if !titles[title.ID] {
			routing.obstacles = append(routing.obstacles, title.Rect)
		}
	}
	return routing
}

func fixedInnerText(g *Graph) (map[string]bool, map[string]bool) {
	labels, titles := make(map[string]bool), make(map[string]bool)
	for _, f := range g.Fixed {
		for _, label := range f.Scene.Labels {
			labels[label.ID] = true
		}
		for _, title := range f.Titles {
			titles[title.ID] = true
		}
	}
	return labels, titles
}

func (r attachmentRouting) route(e Edge) ([]geom.Point, error) {
	tail, head := edgeEndpointIDs(r.graph, e)
	from, ok := r.boxes[tail]
	if !ok {
		return nil, ErrGraph
	}
	to, ok := r.boxes[head]
	if !ok {
		return nil, ErrGraph
	}
	obstacles := append(r.exclusiveObstacles(tail, head), r.obstacles...)
	starts, err := endpointPorts(from)
	if err != nil {
		return nil, err
	}
	ends, err := endpointPorts(to)
	if err != nil {
		return nil, err
	}
	grid, err := r.grid(e, obstacles, starts, ends)
	if err != nil {
		return nil, err
	}
	return grid.shortest(starts[:], ends[:])
}

func (r attachmentRouting) grid(e Edge, obstacles []geom.Rect, starts, ends [4]geom.Point) (*visibilityGrid, error) {
	tail, head := edgeEndpointIDs(r.graph, e)
	region, err := sharedRegion(r.graph, semanticParent(r.graph.semantic, tail), semanticParent(r.graph.semantic, head))
	if err != nil {
		return nil, err
	}
	if region == "" {
		return newOpenGrid(obstacles, starts[:], ends[:])
	}
	bound, ok := r.boxes[region]
	if !ok {
		return nil, ErrGraph
	}
	return newVisibilityGrid(obstacles, starts[:], ends[:], bound)
}

func semanticParent(boxes []scene.Box, id string) string {
	for _, b := range boxes {
		if b.ID == id {
			return b.Parent
		}
	}
	return ""
}

func (r attachmentRouting) exclusiveObstacles(tail, head string) []geom.Rect {
	semantic := r.graph.semantic
	ancestors := append(semanticAncestors(semantic, tail), semanticAncestors(semantic, head)...)
	var out []geom.Rect
	for _, n := range r.graph.Nodes {
		decl := int(n.Decl)
		if n.Border != BorderNone || decl < 0 || decl >= len(semantic) {
			continue
		}
		if semantic[decl].Exclusive && !slices.Contains(ancestors, decl) {
			out = append(out, r.boxes[n.ID])
		}
	}
	return out
}

func newOpenGrid(obstacles []geom.Rect, starts, ends []geom.Point) (*visibilityGrid, error) {
	g := &visibilityGrid{obstacles: obstacles, open: true}
	for _, rect := range obstacles {
		if err := g.spreadClearance(rect); err != nil {
			return nil, err
		}
	}
	for _, p := range slices.Concat(starts, ends) {
		g.x = append(g.x, p.X)
		g.y = append(g.y, p.Y)
	}
	slices.Sort(g.x)
	g.x = slices.Compact(g.x)
	slices.Sort(g.y)
	g.y = slices.Compact(g.y)
	return g, nil
}
