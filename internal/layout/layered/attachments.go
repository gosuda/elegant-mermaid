package layered

import (
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/geom"
)

type attachmentTarget struct {
	decl    int32
	id      string
	node    int32
	cluster int
}

type attachmentFragment struct {
	mask   []bool
	layout Layout
	size   geom.Size
}

type attachedNote struct {
	node     int32
	fragment attachmentFragment
	side     AttachmentSide
}

type attachmentBundle struct {
	target    attachmentTarget
	part      attachmentFragment
	notes     []attachedNote
	footprint attachmentFootprint
	growth    geom.Size
}

type fragmentContext struct {
	graph   *Graph
	entry   []bool
	options OrderOptions
}

func layoutAttached(g *Graph, entry []bool, options OrderOptions) (Layout, error) {
	context := fragmentContext{graph: g, entry: entry, options: options}
	bundles, err := context.bundles()
	if err != nil {
		return Layout{}, err
	}
	if len(bundles) == 0 {
		return runComponent(g, options)
	}
	contraction, err := contractBundles(g, entry, bundles)
	if err != nil {
		return Layout{}, err
	}
	result, err := runComponent(contraction.graph, options)
	if err != nil {
		return Layout{}, err
	}
	expansion := attachmentExpansion{graph: g, contraction: contraction, bundles: bundles}
	return expansion.expand(result)
}

func (c fragmentContext) target(decl int32) (attachmentTarget, bool) {
	for i, n := range c.graph.Nodes {
		if n.Border == BorderNone && n.Decl == decl {
			return attachmentTarget{decl: decl, id: n.ID, node: int32(i), cluster: -1}, true
		}
	}
	for i, cluster := range c.graph.Clusters {
		if cluster.Decl == decl {
			return attachmentTarget{decl: decl, id: cluster.ID, node: -1, cluster: i}, true
		}
	}
	return attachmentTarget{}, false
}

func (c fragmentContext) bundles() ([]attachmentBundle, error) {
	var bundles []attachmentBundle
	for _, a := range c.graph.Attachments {
		target, ok := c.target(int32(a.Target))
		if !ok || c.nested(target) || bundledTarget(bundles, target.decl) {
			continue
		}
		bundle, err := c.bundle(target)
		if err != nil {
			return nil, err
		}
		bundles = append(bundles, bundle)
	}
	return bundles, nil
}

func bundledTarget(bundles []attachmentBundle, decl int32) bool {
	return slices.ContainsFunc(bundles, func(b attachmentBundle) bool { return b.target.decl == decl })
}

func (c fragmentContext) nested(target attachmentTarget) bool {
	ancestors := semanticAncestors(c.graph.semantic, target.id)
	for _, a := range c.graph.Attachments {
		if _, ok := c.target(int32(a.Target)); ok && slices.Contains(ancestors, a.Target) {
			return true
		}
	}
	return false
}

func (c fragmentContext) bundle(target attachmentTarget) (attachmentBundle, error) {
	part, err := c.build(c.subtree(target), target.decl)
	if err != nil {
		return attachmentBundle{}, err
	}
	bundle := attachmentBundle{target: target, part: part}
	for _, a := range c.graph.Attachments {
		if int32(a.Target) != target.decl {
			continue
		}
		note, ok := c.target(int32(a.Note))
		if !ok || note.node < 0 {
			return attachmentBundle{}, ErrGraph
		}
		mask := make([]bool, len(c.graph.Nodes))
		mask[note.node] = true
		fragment, err := c.build(mask, target.decl)
		if err != nil {
			return attachmentBundle{}, err
		}
		bundle.notes = append(bundle.notes, attachedNote{node: note.node, fragment: fragment, side: a.Side})
	}
	bundle.footprint, err = bundle.measure(c.graph)
	return bundle, err
}

func (b attachmentBundle) measure(g *Graph) (attachmentFootprint, error) {
	gap, err := coordinate(2*int64(g.Slot) + 2)
	if err != nil {
		return attachmentFootprint{}, err
	}
	sizes := make([]attachmentNoteSize, len(b.notes))
	for i, note := range b.notes {
		sizes[i] = attachmentNoteSize{size: note.fragment.size, side: note.side}
	}
	return attachmentFootprintOf(footprintInput{target: b.part.size, notes: sizes, direction: g.Direction, gap: gap})
}

func (c fragmentContext) subtree(target attachmentTarget) []bool {
	g := c.graph
	mask := make([]bool, len(g.Nodes))
	for i, n := range g.Nodes {
		if n.Border == BorderNone && (n.ID == target.id || semanticInside(g.semantic, n.ID, target.id)) {
			mask[i] = true
		}
	}
	for _, cluster := range g.Clusters {
		if cluster.ID == target.id || semanticInside(g.semantic, cluster.ID, target.id) {
			mask[cluster.Top] = true
			mask[cluster.Bottom] = true
		}
	}
	return mask
}

func (c fragmentContext) build(mask []bool, excluded int32) (attachmentFragment, error) {
	graph := attachmentSubgraph(c.graph, c.entry, mask)
	for _, a := range c.graph.Attachments {
		if int32(a.Target) != excluded {
			graph.Attachments = append(graph.Attachments, a)
		}
	}
	if err := breakAttachedCycles(graph); err != nil {
		return attachmentFragment{}, err
	}
	layout, err := layoutAttached(graph, edgeFlags(graph), c.options)
	if err != nil {
		return attachmentFragment{}, err
	}
	bounds, err := layoutBounds(layout)
	if err != nil {
		return attachmentFragment{}, err
	}
	if err := translateLayout(&layout, -int64(bounds.X), -int64(bounds.Y)); err != nil {
		return attachmentFragment{}, err
	}
	return attachmentFragment{mask: mask, layout: layout, size: geom.Size{W: bounds.W, H: bounds.H}}, nil
}

func attachmentSubgraph(g *Graph, entry []bool, mask []bool) *Graph {
	sub := &Graph{Params: g.Params, Direction: g.Direction, semantic: g.semantic, regions: g.regions}
	local := make([]int32, len(g.Nodes))
	for v, n := range g.Nodes {
		if !mask[v] {
			continue
		}
		local[v] = int32(len(sub.Nodes))
		sub.Nodes = append(sub.Nodes, n)
	}
	for i, e := range g.Edges {
		if !mask[e.Tail] || !mask[e.Head] {
			continue
		}
		e.Tail, e.Head, e.Reversed = local[e.Tail], local[e.Head], entry[i]
		sub.Edges = append(sub.Edges, e)
	}
	sub.Clusters = componentClusters(g, mask, local)
	sub.Fixed = componentFixed(g, mask)
	detachAbsentParents(sub)
	return sub
}

func detachAbsentParents(g *Graph) {
	present := make(map[string]bool, len(g.Clusters))
	for _, c := range g.Clusters {
		present[c.ID] = true
	}
	for i := range g.Nodes {
		if !present[g.Nodes[i].Parent] {
			g.Nodes[i].Parent = ""
		}
	}
	for i := range g.Clusters {
		if !present[g.Clusters[i].Parent] {
			g.Clusters[i].Parent = ""
		}
	}
}
