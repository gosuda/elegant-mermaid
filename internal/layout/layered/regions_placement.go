package layered

import (
	"math"
	"slices"
)

type reservedLane struct {
	x  int32
	ok bool
}

type laneSequence struct {
	right, maxLabel, fallback int64
}

func (s *laneSequence) next(p *Proper, edge int) (int32, error) {
	if edge < len(p.reservedLanes) && p.reservedLanes[edge].ok {
		return p.reservedLanes[edge].x, nil
	}
	lane, err := coordinate(s.right + int64(p.Slot) + s.fallback*(2*int64(p.Slot)+s.maxLabel))
	s.fallback++
	return lane, err
}

func gutterRun(p *Proper, r *Routing, anchor, edge int32) int32 {
	if node := p.Nodes[anchor]; node.Border == BorderTop && node.H > 0 {
		return r.SourceX[edge]
	}
	return r.sourceRun(int(edge))
}

func semanticHeight(p *Proper, v int32) int32 {
	if p.Nodes[v].Border == BorderTop {
		return 0
	}
	return p.Nodes[v].H
}

func sourceTopProxy(p *Proper, e ProperEdge) bool {
	original := p.Original[e.Original]
	node := p.Nodes[e.Tail]
	return original.SourceGroup != "" && node.Border == BorderTop && node.Parent == original.SourceGroup
}

type regionTree struct {
	children   [][]int
	order      []int
	nodeGroups []int
}

func newRegionTree(r *componentRegions, p *Proper) (*regionTree, error) {
	children, err := regionChildren(r)
	if err != nil {
		return nil, err
	}
	t := &regionTree{children: children, order: childPreorder(children), nodeGroups: make([]int, len(p.Nodes))}
	for v, node := range p.Nodes {
		group, ok := r.scope(node.Parent)
		if !ok {
			return nil, ErrGraph
		}
		t.nodeGroups[v] = group
	}
	if len(t.order) != len(children) {
		return nil, ErrGraph
	}
	return t, nil
}

func regionChildren(r *componentRegions) ([][]int, error) {
	n := len(r.clusters)
	children := make([][]int, n+1)
	owner := make([]int, n)
	for group := range r.parents {
		parent := parentGroup(r, group)
		children[parent] = append(children[parent], group)
		owner[group] = -1
	}
	for index, set := range r.sets {
		for _, region := range set.regions {
			owner[region] = index
		}
		owned := func(g int) bool { return owner[g] == index }
		first := slices.IndexFunc(children[set.parent], owned)
		if first < 0 {
			return nil, ErrGraph
		}
		kept := slices.DeleteFunc(slices.Clone(children[set.parent]), owned)
		children[set.parent] = slices.Insert(kept, first, set.regions...)
	}
	return children, nil
}

func childPreorder(children [][]int) []int {
	order := make([]int, 0, len(children))
	stack := []int{len(children) - 1}
	for len(stack) > 0 {
		group := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		order = append(order, group)
		for i := len(children[group]) - 1; i >= 0; i-- {
			stack = append(stack, children[group][i])
		}
	}
	return order
}

func (t *regionTree) root() int { return len(t.children) - 1 }

func (t *regionTree) edgeOwner(r *componentRegions, e Edge) int {
	seen := make([]bool, len(t.children))
	for g := t.nodeGroups[e.Tail]; g != t.root(); g = parentGroup(r, g) {
		seen[g] = true
	}
	for g := t.nodeGroups[e.Head]; g != t.root(); g = parentGroup(r, g) {
		if seen[g] {
			return g
		}
	}
	return t.root()
}

func parentGroup(r *componentRegions, g int) int {
	if parent := r.parents[g]; parent >= 0 {
		return parent
	}
	return len(r.clusters)
}

func (t *regionTree) pin(p *Proper, layers [][]int32) error {
	prefixes := make([][]int, len(t.children))
	for _, group := range t.order {
		for position, child := range t.children[group] {
			prefixes[child] = append(slices.Clone(prefixes[group]), position+2)
		}
	}
	keys := make([][]int, len(p.Nodes))
	for v, node := range p.Nodes {
		kind := 1
		switch node.Border {
		case BorderLeft:
			kind = 0
		case BorderRight:
			kind = math.MaxInt
		}
		keys[v] = append(slices.Clone(prefixes[t.nodeGroups[v]]), kind)
	}
	for _, layer := range layers {
		for _, v := range layer {
			if v < 0 || int(v) >= len(keys) {
				return ErrGraph
			}
		}
		slices.SortStableFunc(layer, func(a, b int32) int { return slices.Compare(keys[a], keys[b]) })
	}
	return nil
}

func (r *componentRegions) requiredSpans() ([]optionalSpan, error) {
	required := make([]optionalSpan, len(r.clusters))
	for _, band := range r.minimum.bands {
		if band.right <= band.left || band.group < 0 || band.group >= len(required) {
			return nil, ErrGraph
		}
		if span := r.minimum.spans[band.group]; !span.ok || span.span != band.span {
			return nil, ErrGraph
		}
		required[band.group] = optionalSpan{span: band.span, ok: true}
	}
	return required, nil
}

func (r *componentRegions) commonSpans(p *Proper) error {
	required, err := r.requiredSpans()
	if err != nil {
		return err
	}
	for _, c := range p.Clusters {
		group := r.group(c.ID)
		if group < 0 {
			return ErrGraph
		}
		span := required[group]
		if span.ok && (p.Rank[c.Top] != span.span.first || p.Rank[c.Bottom] != span.span.last) {
			return ErrGraph
		}
	}
	return nil
}

type regionBuckets struct {
	members   [][]int32
	low       []int32
	widths    []int32
	lanes     [][]int
	laneWidth []int32
	loopWidth []int32
}

func newRegionBuckets(r *componentRegions, p *Proper, t *regionTree, desired []int32) (*regionBuckets, error) {
	n := len(t.children)
	b := &regionBuckets{members: make([][]int32, n), low: make([]int32, n), widths: make([]int32, n), lanes: make([][]int, n), laneWidth: make([]int32, n), loopWidth: make([]int32, n)}
	high := make([]int32, n)
	for i := range n {
		b.low[i], high[i] = math.MaxInt32, math.MinInt32
	}
	for v, node := range p.Nodes {
		if node.Border != BorderNone {
			continue
		}
		owner := t.nodeGroups[v]
		width := int64(node.W) + 2*int64(node.Extent)
		left, err := coordinate(int64(desired[v]) - width/2)
		if err != nil {
			return nil, err
		}
		right, err := coordinate(int64(left) + width)
		if err != nil {
			return nil, err
		}
		b.low[owner], high[owner] = min(b.low[owner], left), max(high[owner], right)
		b.members[owner] = append(b.members[owner], int32(v))
	}
	for i := range n {
		if len(b.members[i]) == 0 {
			continue
		}
		width, err := subtractCoordinates(high[i], b.low[i])
		if err != nil {
			return nil, err
		}
		b.widths[i] = width
	}
	b.collectLanes(r, p, t)
	for _, c := range p.Clusters {
		b.loopWidth[r.group(c.ID)] = c.Extent
	}
	return b, nil
}

func (b *regionBuckets) collectLanes(r *componentRegions, p *Proper, t *regionTree) {
	for i, e := range p.Original {
		if !e.Reversed || e.SelfLoop() || e.Synthetic {
			continue
		}
		owner := t.edgeOwner(r, e)
		if owner == t.root() {
			continue
		}
		b.lanes[owner] = append(b.lanes[owner], i)
		if e.Label != nil {
			b.laneWidth[owner] = max(b.laneWidth[owner], e.Label.W)
		}
	}
}

func (b *regionBuckets) laneExtent(group int, slot int32) (int32, error) {
	return coordinate((2*int64(slot) + int64(b.laneWidth[group])) * int64(len(b.lanes[group])))
}

func regionInset(p *Proper) (int32, error) {
	return addCoordinates(p.ClusterPad, p.ClusterBorder)
}

type regionPlacement struct {
	r       *componentRegions
	p       *Proper
	tree    *regionTree
	buckets *regionBuckets
}

func (pl regionPlacement) reserveWidths() ([]int32, error) {
	root := pl.tree.root()
	inset, err := regionInset(pl.p)
	if err != nil {
		return nil, err
	}
	footprints := make([]int32, root)
	for _, c := range pl.p.Clusters {
		footprints[pl.r.group(c.ID)] = c.TitleSize.W
	}
	widths := make([]int32, root+1)
	for i := len(pl.tree.order) - 1; i >= 0; i-- {
		group := pl.tree.order[i]
		width := int64(pl.buckets.widths[group])
		for _, child := range pl.tree.children[group] {
			width += int64(widths[child])
		}
		lanes, err := pl.buckets.laneExtent(group, pl.p.Slot)
		if err != nil {
			return nil, err
		}
		width += int64(lanes)
		if group != root {
			width = max(width+2*int64(inset), int64(pl.r.minimum.widths[group]), int64(footprints[group])+2*int64(inset))
		}
		if widths[group], err = coordinate(width + int64(pl.buckets.loopWidth[group])); err != nil {
			return nil, err
		}
	}
	return widths, nil
}

type regionAllocation struct {
	widths, lefts []int32
	lanes         []reservedLane
}

func (pl regionPlacement) allocate(x []int32) (regionAllocation, error) {
	widths, err := pl.reserveWidths()
	if err != nil {
		return regionAllocation{}, err
	}
	out := regionAllocation{widths: widths, lefts: make([]int32, len(widths)), lanes: make([]reservedLane, len(pl.p.Original))}
	for _, group := range pl.tree.order {
		if err := pl.allocateGroup(group, x, &out); err != nil {
			return regionAllocation{}, err
		}
	}
	return out, nil
}

func (pl regionPlacement) allocateGroup(group int, x []int32, out *regionAllocation) error {
	b := pl.buckets
	start := int64(out.lefts[group])
	if group != pl.tree.root() {
		start += int64(pl.r.minimum.origins[group])
	}
	cursor := start + int64(b.widths[group])
	if len(b.members[group]) > 0 {
		if err := shiftMembers(x, b.members[group], start-int64(b.low[group])); err != nil {
			return err
		}
	}
	for _, child := range pl.tree.children[group] {
		left, err := coordinate(cursor)
		if err != nil {
			return err
		}
		out.lefts[child] = left
		cursor += int64(out.widths[child])
	}
	return pl.allocateLanes(group, cursor, out)
}

func shiftMembers(x []int32, members []int32, shift int64) error {
	for _, v := range members {
		moved, err := coordinate(int64(x[v]) + shift)
		if err != nil {
			return err
		}
		x[v] = moved
	}
	return nil
}

func (pl regionPlacement) allocateLanes(group int, cursor int64, out *regionAllocation) error {
	b, slot := pl.buckets, int64(pl.p.Slot)
	if group != pl.tree.root() && len(b.lanes[group]) > 0 {
		inset, err := regionInset(pl.p)
		if err != nil {
			return err
		}
		extent, err := b.laneExtent(group, pl.p.Slot)
		if err != nil {
			return err
		}
		cursor = int64(out.lefts[group]) + int64(out.widths[group]) - int64(b.loopWidth[group]) - int64(inset) - int64(extent)
	}
	for _, edge := range b.lanes[group] {
		cursor += slot
		lane, err := coordinate(cursor)
		if err != nil {
			return err
		}
		out.lanes[edge] = reservedLane{x: lane, ok: true}
		cursor += slot + int64(b.laneWidth[group])
	}
	return nil
}

func (r *componentRegions) crossCoords(p *Proper, layers [][]int32) ([]int32, error) {
	if r == nil {
		return CrossCoords(p, layers)
	}
	tree, err := newRegionTree(r, p)
	if err != nil {
		return nil, err
	}
	if err := tree.pin(p, layers); err != nil {
		return nil, err
	}
	x, err := CrossCoords(p, layers)
	if err != nil {
		return nil, err
	}
	if err := r.commonSpans(p); err != nil {
		return nil, err
	}
	buckets, err := newRegionBuckets(r, p, tree, x)
	if err != nil {
		return nil, err
	}
	placement := regionPlacement{r: r, p: p, tree: tree, buckets: buckets}
	allocation, err := placement.allocate(x)
	if err != nil {
		return nil, err
	}
	if err := placement.frames(allocation, x); err != nil {
		return nil, err
	}
	p.reservedLanes = allocation.lanes
	return x, placement.reservedPorts(x)
}

func (pl regionPlacement) frames(allocation regionAllocation, x []int32) error {
	border := pl.p.ClusterBorder
	for _, c := range pl.p.Clusters {
		group := pl.r.group(c.ID)
		left := allocation.lefts[group]
		frameRight, err := coordinate(int64(left) + int64(allocation.widths[group]) - int64(pl.buckets.loopWidth[group]))
		if err != nil {
			return err
		}
		center := left + (frameRight-left)/2
		for v, node := range pl.p.Nodes {
			if node.Parent != c.ID {
				continue
			}
			switch node.Border {
			case BorderLeft:
				x[v] = left + border/2
			case BorderRight:
				x[v] = frameRight - border + border/2
			case BorderTitle:
				x[v] = center
			}
		}
		x[c.Top], x[c.Bottom] = center, center
	}
	return nil
}

func (pl regionPlacement) reservedPorts(x []int32) error {
	for _, c := range pl.p.Clusters {
		if err := clusterPort(pl.p, c, c.Top, x); err != nil {
			return err
		}
		if err := clusterPort(pl.p, c, c.Bottom, x); err != nil {
			return err
		}
		footprint := max(c.TitleSize.H, c.LoopHeight)
		if c.TitleSize.W < 0 || footprint < 0 {
			return ErrGraph
		}
		pl.p.Nodes[c.Top].H = max(pl.p.Nodes[c.Top].H, footprint)
	}
	return nil
}

func clusterPort(p *Proper, c Cluster, node int32, x []int32) error {
	rank := p.Rank[node]
	left, right := int32(-1), int32(-1)
	for v, n := range p.Nodes {
		if n.Parent != c.ID || p.Rank[v] != rank {
			continue
		}
		switch n.Border {
		case BorderLeft:
			left = int32(v)
		case BorderRight:
			right = int32(v)
		}
	}
	if left < 0 || right < 0 {
		return ErrGraph
	}
	lo := int64(x[left]) - int64(p.Nodes[left].W)/2
	hi := int64(x[right]) - int64(p.Nodes[right].W)/2 + int64(p.Nodes[right].W)
	if hi < lo {
		return ErrGraph
	}
	center, err := coordinate(lo + (hi-lo)/2)
	x[node] = center
	return err
}
