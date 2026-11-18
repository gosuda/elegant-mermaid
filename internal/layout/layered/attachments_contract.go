package layered

import (
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type attachmentContraction struct {
	graph *Graph
	owner []int
	kept  []int
}

type contractedNodes struct {
	nodes    []Node
	local    []int32
	clusters []Cluster
}

func contractBundles(g *Graph, entry []bool, bundles []attachmentBundle) (attachmentContraction, error) {
	owner := attachmentOwners(g, bundles)
	contracted := contractNodes(g, bundles, owner)
	cg := &Graph{Nodes: contracted.nodes, Clusters: contracted.clusters, Direction: g.Direction, Params: g.Params, regions: g.regions}
	for _, f := range g.Fixed {
		index := nodeIndex(g, f.ID)
		if index >= 0 && owner[index] < 0 {
			cg.Fixed = append(cg.Fixed, f)
		}
	}
	contraction := attachmentContraction{graph: cg, owner: owner}
	for i, e := range g.Edges {
		if e.Synthetic || owner[e.Tail] >= 0 && owner[e.Tail] == owner[e.Head] {
			continue
		}
		cg.Edges = append(cg.Edges, contractedEdge(e, entry[i], owner, contracted.local))
		contraction.kept = append(contraction.kept, i)
	}
	if err := rebuildBorderEdges(cg, syntheticBase(g)); err != nil {
		return attachmentContraction{}, err
	}
	return contraction, breakAttachedCycles(cg)
}

func contractedEdge(e Edge, reversed bool, owner []int, local []int32) Edge {
	if owner[e.Tail] >= 0 {
		e.SourceGroup = ""
	}
	if owner[e.Head] >= 0 {
		e.TargetGroup = ""
	}
	e.Tail, e.Head, e.Reversed = local[e.Tail], local[e.Head], reversed
	return e
}

func rebuildBorderEdges(g *Graph, base int64) error {
	routes := len(g.Edges)
	clusterRankEdges(g)
	for i := routes; i < len(g.Edges); i++ {
		decl, err := coordinate(base + int64(i-routes))
		if err != nil {
			return err
		}
		g.Edges[i].Decl = decl
	}
	return nil
}

func syntheticBase(g *Graph) int64 {
	base := int64(0)
	for _, e := range g.Edges {
		if e.Synthetic {
			return int64(e.Decl)
		}
		base = int64(e.Decl) + 1
	}
	return base
}

func attachmentOwners(g *Graph, bundles []attachmentBundle) []int {
	owner := make([]int, len(g.Nodes))
	for i := range owner {
		owner[i] = -1
	}
	for b, bundle := range bundles {
		for v, inside := range bundle.part.mask {
			if inside {
				owner[v] = b
			}
		}
		for _, note := range bundle.notes {
			owner[note.node] = b
		}
	}
	return owner
}

type contractedEntry struct {
	decl   int32
	node   int
	bundle int
}

func contractionOrder(g *Graph, bundles []attachmentBundle, owner []int) []contractedEntry {
	var order []contractedEntry
	for v, n := range g.Nodes {
		if n.Border == BorderNone && (owner[v] < 0 || bundles[owner[v]].target.node == int32(v)) {
			order = append(order, contractedEntry{decl: n.Decl, node: v, bundle: owner[v]})
		}
	}
	for b, bundle := range bundles {
		if bundle.target.node >= 0 {
			continue
		}
		at := slices.IndexFunc(order, func(entry contractedEntry) bool { return entry.decl > bundle.target.decl })
		if at < 0 {
			at = len(order)
		}
		order = slices.Insert(order, at, contractedEntry{decl: bundle.target.decl, node: -1, bundle: b})
	}
	return order
}

func (out *contractedNodes) appendClusters(g *Graph, owner []int) {
	for _, c := range g.Clusters {
		if owner[c.Top] >= 0 {
			continue
		}
		top, bottom := g.Nodes[c.Top], g.Nodes[c.Bottom]
		out.local[c.Top] = int32(len(out.nodes))
		out.local[c.Bottom] = out.local[c.Top] + 1
		c.Top, c.Bottom = out.local[c.Top], out.local[c.Bottom]
		out.nodes = append(out.nodes, top, bottom)
		out.clusters = append(out.clusters, c)
	}
}

func contractNodes(g *Graph, bundles []attachmentBundle, owner []int) contractedNodes {
	out := contractedNodes{local: make([]int32, len(g.Nodes))}
	envelopes := make([]int32, len(bundles))
	for _, entry := range contractionOrder(g, bundles, owner) {
		if entry.bundle >= 0 {
			envelopes[entry.bundle] = int32(len(out.nodes))
			out.nodes = append(out.nodes, envelopeNode(g, bundles[entry.bundle]))
			continue
		}
		out.local[entry.node] = int32(len(out.nodes))
		out.nodes = append(out.nodes, g.Nodes[entry.node])
	}
	out.appendClusters(g, owner)
	for v, b := range owner {
		if b >= 0 {
			out.local[v] = envelopes[b]
		}
	}
	return out
}

func envelopeNode(g *Graph, bundle attachmentBundle) Node {
	node := Node{ID: bundle.target.id, Decl: bundle.target.decl}
	if bundle.target.node >= 0 {
		node = g.Nodes[bundle.target.node]
	} else {
		node.Parent = g.Clusters[bundle.target.cluster].Parent
	}
	node.W, node.H = bundle.footprint.size.W, bundle.footprint.size.H
	node.Exact, node.Extent, node.Role, node.Border = true, 0, scene.RoleNode, BorderNone
	return node
}

type attachmentExpansion struct {
	graph       *Graph
	contraction attachmentContraction
	bundles     []attachmentBundle
}

type expandedRoutes struct {
	points map[string][]geom.Point
	extra  []EdgeRoute
	edges  map[string]bool
}

func (x attachmentExpansion) expand(result Layout) (Layout, error) {
	envelopes := make([]geom.Rect, len(x.bundles))
	for i, b := range x.bundles {
		index := slices.IndexFunc(result.Boxes, func(box Box) bool { return box.ID == b.target.id })
		if index < 0 {
			return Layout{}, ErrGraph
		}
		envelopes[i] = result.Boxes[index].Rect
	}
	targets := make(map[string]bool, len(x.bundles))
	for _, b := range x.bundles {
		targets[b.target.id] = true
	}
	result.Boxes = slices.DeleteFunc(result.Boxes, func(box Box) bool { return targets[box.ID] })
	result.Titles = slices.DeleteFunc(result.Titles, func(box Box) bool { return targets[box.ID] })
	routes := x.collectRoutes(result.Routes)
	for i := range x.bundles {
		if err := x.placeBundle(&result, &routes, i, envelopes[i]); err != nil {
			return Layout{}, err
		}
	}
	if err := x.reconnect(&result, routes); err != nil {
		return Layout{}, err
	}
	return result, nil
}

func (x attachmentExpansion) collectRoutes(source []EdgeRoute) expandedRoutes {
	routes := expandedRoutes{points: make(map[string][]geom.Point), edges: make(map[string]bool)}
	for _, e := range x.graph.Edges {
		if !e.Synthetic {
			routes.edges[e.ID] = true
		}
	}
	routes.merge(source)
	return routes
}

func (r *expandedRoutes) merge(source []EdgeRoute) {
	for _, route := range source {
		if r.edges[route.ID] {
			r.points[route.ID] = route.Points
			continue
		}
		r.extra = append(r.extra, route)
	}
}

func (x attachmentExpansion) placeBundle(result *Layout, routes *expandedRoutes, index int, envelope geom.Rect) error {
	bundle := &x.bundles[index]
	if err := bundle.fitFinalFrame(envelope, x.graph); err != nil {
		return err
	}
	origin := geom.Point{X: envelope.X, Y: envelope.Y}
	at, err := translatedRect(bundle.footprint.target, origin)
	if err != nil {
		return err
	}
	if err := placeAttachmentFragment(result, routes, &bundle.part, at); err != nil {
		return err
	}
	for i := range bundle.notes {
		at, err := translatedRect(bundle.footprint.notes[i], origin)
		if err != nil {
			return err
		}
		if err := placeAttachmentFragment(result, routes, &bundle.notes[i].fragment, at); err != nil {
			return err
		}
	}
	result.Extents = append(result.Extents, Box{ID: bundle.target.id, Rect: envelope})
	return nil
}

func placeAttachmentFragment(result *Layout, routes *expandedRoutes, fragment *attachmentFragment, at geom.Rect) error {
	part := &fragment.layout
	if err := translateLayout(part, int64(at.X), int64(at.Y)); err != nil {
		return err
	}
	result.Boxes = append(result.Boxes, part.Boxes...)
	routes.merge(part.Routes)
	result.Labels = append(result.Labels, part.Labels...)
	result.LabelReservations = append(result.LabelReservations, part.LabelReservations...)
	result.Extents = append(result.Extents, part.Extents...)
	result.Titles = append(result.Titles, part.Titles...)
	result.BudgetExhausted = result.BudgetExhausted || part.BudgetExhausted
	result.fixedArea += part.fixedArea
	return nil
}

func (b *attachmentBundle) fitFinalFrame(reservation geom.Rect, g *Graph) error {
	growth, err := b.targetGrowth(reservation, g.Direction)
	if err != nil {
		return err
	}
	if err := b.part.growRoot(g, b.target, growth); err != nil {
		return err
	}
	b.footprint, err = b.measure(g)
	if err != nil {
		return err
	}
	if b.footprint.size.W != reservation.W || b.footprint.size.H != reservation.H {
		return ErrGraph
	}
	b.growth = growth
	return nil
}

func (b *attachmentBundle) targetGrowth(reservation geom.Rect, direction scene.Direction) (geom.Size, error) {
	w, err := coordinate(int64(reservation.W) - int64(b.footprint.size.W))
	if err != nil {
		return geom.Size{}, err
	}
	h, err := coordinate(int64(reservation.H) - int64(b.footprint.size.H))
	if err != nil {
		return geom.Size{}, err
	}
	growth := geom.Size{W: w, H: h}
	if growth.W < 0 || growth.H < 0 {
		return geom.Size{}, ErrGraph
	}
	axis, extent := &growth.H, func(s geom.Size) int32 { return s.H }
	if direction == scene.DirectionLR || direction == scene.DirectionRL {
		axis, extent = &growth.W, func(s geom.Size) int32 { return s.W }
	}
	target, note := extent(b.part.size), int32(0)
	for _, n := range b.notes {
		note = max(note, extent(n.fragment.size))
	}
	if *axis > 0 {
		*axis, err = coordinate(int64(*axis) + max(int64(note)-int64(target), 0))
	}
	return growth, err
}

func (f *attachmentFragment) growRoot(g *Graph, target attachmentTarget, amount geom.Size) error {
	if amount.W == 0 && amount.H == 0 {
		return nil
	}
	root := slices.IndexFunc(f.layout.Boxes, func(box Box) bool { return box.ID == target.id })
	if root < 0 {
		return ErrGraph
	}
	frame := &f.layout.Boxes[root].Rect
	if err := growExtent(&frame.W, &frame.H, amount); err != nil {
		return err
	}
	if err := f.shiftTitles(target.id, int64(amount.W)/2); err != nil {
		return err
	}
	if err := f.moveRootLoops(rootLoops(g, target), amount.W); err != nil {
		return err
	}
	return growExtent(&f.size.W, &f.size.H, amount)
}

func growExtent(w, h *int32, amount geom.Size) error {
	var err error
	if *w, err = coordinate(int64(*w) + int64(amount.W)); err != nil {
		return err
	}
	*h, err = coordinate(int64(*h) + int64(amount.H))
	return err
}

func (f *attachmentFragment) shiftTitles(id string, dx int64) error {
	for i := range f.layout.Titles {
		title := &f.layout.Titles[i]
		if title.ID != id {
			continue
		}
		x, err := coordinate(int64(title.Rect.X) + dx)
		if err != nil {
			return err
		}
		title.Rect.X = x
	}
	return nil
}

type loopOwners struct {
	routes map[string]bool
	labels map[string]bool
}

func rootLoops(g *Graph, target attachmentTarget) loopOwners {
	owners := loopOwners{routes: make(map[string]bool), labels: make(map[string]bool)}
	for _, e := range g.Edges {
		if e.Synthetic || !rootLoop(e, target) {
			continue
		}
		owners.routes[e.ID] = true
		if e.Label == nil {
			continue
		}
		for _, item := range e.Label.Items {
			owners.labels[item.ID] = true
		}
	}
	return owners
}

func rootLoop(e Edge, target attachmentTarget) bool {
	if target.node >= 0 {
		return e.NodeLoop() && e.Tail == target.node
	}
	return e.FrameLoop == target.id
}

func (f *attachmentFragment) moveRootLoops(owners loopOwners, dx int32) error {
	if err := f.moveLoopRoutes(owners, dx); err != nil {
		return err
	}
	if err := f.moveLoopLabels(owners, dx); err != nil {
		return err
	}
	return f.moveLoopReservations(owners, dx)
}

func (f *attachmentFragment) moveLoopRoutes(owners loopOwners, dx int32) error {
	for _, route := range f.layout.Routes {
		if !owners.routes[route.ID] {
			continue
		}
		if err := translatePoints(route.Points, int64(dx), 0); err != nil {
			return err
		}
	}
	return nil
}

func (f *attachmentFragment) moveLoopLabels(owners loopOwners, dx int32) error {
	for i := range f.layout.Labels {
		if !owners.labels[f.layout.Labels[i].ID] {
			continue
		}
		if err := translateBox(&f.layout.Labels[i], int64(dx), 0); err != nil {
			return err
		}
	}
	return nil
}

func (f *attachmentFragment) moveLoopReservations(owners loopOwners, dx int32) error {
	for i := range f.layout.LabelReservations {
		reservation := &f.layout.LabelReservations[i]
		if reservation.Label == nil || !slices.ContainsFunc(reservation.Label.Items, func(item MeasuredLabel) bool { return owners.labels[item.ID] }) {
			continue
		}
		rect, err := translatedRect(reservation.Rect, geom.Point{X: dx})
		if err != nil {
			return err
		}
		reservation.Rect = rect
	}
	return nil
}
