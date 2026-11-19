package layered

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type orderedComponent struct {
	regions         *componentRegions
	proper          *Proper
	order           OrderResult
	budgetExhausted bool
}

func runComponent(g *Graph, opts OrderOptions) (Layout, error) {
	ordered, err := orderComponent(g, opts)
	if err != nil {
		return Layout{}, err
	}
	return ordered.place(g)
}

func orderComponent(g *Graph, opts OrderOptions) (orderedComponent, error) {
	regions, err := newComponentRegions(g)
	if err != nil {
		return orderedComponent{}, err
	}
	rank, err := regions.rank(g)
	if err != nil {
		return orderedComponent{}, err
	}
	p, err := Normalize(g, rank.Ranks)
	if err != nil {
		return orderedComponent{}, err
	}
	if err := sizeProperPorts(g, p); err != nil {
		return orderedComponent{}, err
	}
	if err := regions.constrain(p); err != nil {
		return orderedComponent{}, err
	}
	order, err := OrderWithBudget(p, opts)
	if err != nil {
		return orderedComponent{}, err
	}
	return orderedComponent{regions: regions, proper: p, order: order, budgetExhausted: rank.BudgetExhausted || order.BudgetExhausted}, nil
}

func (c orderedComponent) place(g *Graph) (Layout, error) {
	p, order := c.proper, c.order
	x, err := c.regions.crossCoords(p, order.Layers)
	if err != nil {
		return Layout{}, err
	}
	routing, err := Route(p, order.Layers, x)
	if err != nil {
		return Layout{}, err
	}
	y, top, err := RankCoords(p, order.Layers, routing)
	if err != nil {
		return Layout{}, err
	}
	if err := reserveExactRanks(g, p, order.Layers, y, top); err != nil {
		return Layout{}, err
	}
	routes, labels, err := RoutePoints(p, order.Layers, x, y, top, routing)
	if err != nil {
		return Layout{}, err
	}
	placement := componentPlacement{proper: p, x: x, y: y, bounds: routing.ClusterBounds}
	return placement.finish(g, Layout{Routes: routes, Labels: labels, LabelReservations: routing.LabelReservations, BudgetExhausted: c.budgetExhausted})
}

type componentPlacement struct {
	proper *Proper
	x, y   []int32
	bounds []horizontalSpan
}

func (placement componentPlacement) finish(g *Graph, part Layout) (Layout, error) {
	p, x, y := placement.proper, placement.x, placement.y
	boxes, err := componentBoxes(g, x, y)
	if err != nil {
		return Layout{}, err
	}
	if err := componentLoops(g, boxes, &part); err != nil {
		return Layout{}, err
	}
	for i, n := range g.Nodes {
		if n.Border == BorderNone {
			part.Boxes = append(part.Boxes, boxes[i])
		}
	}
	frames, err := clusterBoxes(p, y, placement.bounds)
	if err != nil {
		return Layout{}, err
	}
	part.Boxes = append(part.Boxes, frames...)
	titles, err := placedTitles(p, x, y)
	if err != nil {
		return Layout{}, err
	}
	part.Titles = titles
	if err := componentFrameLoops(g, &part); err != nil {
		return Layout{}, err
	}
	part.Routes = visibleRoutes(g, part.Routes)
	if err := expandComponentFixed(g, &part); err != nil {
		return Layout{}, err
	}
	return part, nil
}

func componentLoops(g *Graph, boxes []Box, part *Layout) error {
	loops, err := Loops(g, boxes)
	if err != nil {
		return err
	}
	for _, r := range loops {
		part.Routes[r.Original] = r
	}
	labels, err := loopLabels(g, boxes)
	if err != nil {
		return err
	}
	part.Labels = append(part.Labels, labels.boxes...)
	part.LabelReservations = append(part.LabelReservations, labels.reservations...)
	part.Extents, err = loopExtents(g, boxes)
	return err
}

func visibleRoutes(g *Graph, source []EdgeRoute) []EdgeRoute {
	routes := make([]EdgeRoute, 0, len(source))
	for i, r := range source {
		if g.Edges[i].Synthetic {
			continue
		}
		r.ID = g.Edges[i].ID
		r.Original = g.Edges[i].Decl
		routes = append(routes, r)
	}
	return routes
}

func clusterFrame(c Cluster, bounds horizontalSpan, y []int32) (geom.Rect, error) {
	top, bottom := y[c.Top], y[c.Bottom]
	if bottom < top {
		return geom.Rect{}, ErrRanking
	}
	return rectangle(int64(bounds.Lo), int64(top), int64(bounds.Hi)-int64(bounds.Lo), int64(bottom)-int64(top))
}

func componentBoxes(g *Graph, x, y []int32) ([]Box, error) {
	boxes := make([]Box, len(g.Nodes))
	for i, n := range g.Nodes {
		rect, err := rectangle(int64(x[i])-int64(n.W)/2, int64(y[i]), int64(n.W), int64(n.H))
		if err != nil {
			return nil, err
		}
		boxes[i] = Box{ID: n.ID, Role: n.Role, Rect: rect}
	}
	return boxes, nil
}

func clusterBoxes(p *Proper, y []int32, bounds []horizontalSpan) ([]Box, error) {
	if len(bounds) != len(p.Clusters) {
		return nil, ErrGraph
	}
	frames := make([]Box, 0, len(p.Clusters))
	for i, c := range p.Clusters {
		frame, err := clusterFrame(c, bounds[i], y)
		if err != nil {
			return nil, err
		}
		frames = append(frames, Box{ID: c.ID, Rect: frame, Role: scene.RoleGroup})
	}
	return frames, nil
}
