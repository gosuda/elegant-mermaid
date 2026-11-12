package layered

import (
	"cmp"
	"math"
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type coordinatePass struct {
	p                            *Proper
	layers                       [][]int32
	pos, rank, root, align, sink []int32
	x, shift                     []int64
	set, shifted                 []bool
	marked                       []bool
	gap                          int64
	coordinateArithmetic
}
type coordinateArithmetic struct{ err error }

func (a *coordinateArithmetic) add(x, y int64) int64 {
	if y > 0 && x > math.MaxInt64-y || y < 0 && x < math.MinInt64-y {
		a.err = geom.ErrOverflow
		return 0
	}
	return x + y
}
func (a *coordinateArithmetic) subtract(x, y int64) int64 {
	if y == math.MinInt64 {
		if x >= 0 {
			a.err = geom.ErrOverflow
			return 0
		}
		return x - y
	}
	return a.add(x, -y)
}
func (a *coordinateArithmetic) multiply(x, y int64) int64 {
	n, err := product(x, y)
	if err != nil {
		a.err = err
	}
	return n
}

func coordinateParams(p *Proper) (Params, error) {
	d, err := DefaultParams(scene.ProfileVector)
	if err != nil {
		return Params{}, err
	}
	if p.Slot != 0 {
		d.Slot = p.Slot
	}
	if p.NodeGap != 0 {
		d.NodeGap = p.NodeGap
	}
	if p.RankGap != 0 {
		d.RankGap = p.RankGap
	}
	if p.PortGap != 0 {
		d.PortGap = p.PortGap
	}
	if d.Slot < 1 || d.NodeGap < 1 || d.RankGap < 1 {
		return Params{}, ErrGraph
	}
	return d, nil
}
func coordinateLayers(p *Proper, layers [][]int32) ([]int32, error) {
	if p == nil || len(p.Rank) != len(p.Nodes) {
		return nil, ErrGraph
	}
	if err := coordinateSizes(p); err != nil {
		return nil, err
	}
	pos := make([]int32, len(p.Nodes))
	seen := make([]bool, len(pos))
	for r, layer := range layers {
		if err := coordinateLayer(p, layer, int32(r), pos, seen); err != nil {
			return nil, err
		}
	}
	for _, s := range seen {
		if !s {
			return nil, ErrGraph
		}
	}
	if err := coordinateEdges(p); err != nil {
		return nil, err
	}
	return pos, nil
}
func coordinateLayer(p *Proper, layer []int32, rank int32, pos []int32, seen []bool) error {
	for j, v := range layer {
		if v < 0 || int(v) >= len(pos) || seen[v] || p.Rank[v] != rank {
			return ErrGraph
		}
		seen[v] = true
		pos[v] = int32(j)
	}
	return nil
}
func coordinateEdges(p *Proper) error {
	for _, e := range p.Edges {
		if e.Tail < 0 || e.Head < 0 || int(e.Tail) >= len(p.Nodes) || int(e.Head) >= len(p.Nodes) {
			return ErrGraph
		}
		if int64(p.Rank[e.Head]) != int64(p.Rank[e.Tail])+1 {
			return ErrGraph
		}
	}
	return nil
}
func coordinateSizes(p *Proper) error {
	if int64(len(p.Nodes)) > math.MaxInt32 || int64(len(p.Edges)) > math.MaxInt32 {
		return geom.ErrOverflow
	}
	for _, n := range p.Nodes {
		if n.W < 0 || n.H < 0 {
			return ErrGraph
		}
	}
	return nil
}
func typeOneConflicts(p *Proper, pos []int32) []bool {
	marked := make([]bool, len(p.Edges))
	for i, e := range p.Edges {
		if p.Nodes[e.Tail].Dummy && p.Nodes[e.Head].Dummy {
			continue
		}
		marked[i] = crossesInner(p, pos, e)
	}
	return marked
}
func crossesInner(p *Proper, pos []int32, e ProperEdge) bool {
	for _, f := range p.Edges {
		if p.Rank[e.Tail] != p.Rank[f.Tail] || !p.Nodes[f.Tail].Dummy || !p.Nodes[f.Head].Dummy {
			continue
		}
		a := int64(pos[e.Tail]) - int64(pos[f.Tail])
		b := int64(pos[e.Head]) - int64(pos[f.Head])
		if a*b < 0 {
			return true
		}
	}
	return false
}
func newCoordinatePass(p *Proper, layers [][]int32, marked []bool, gap int64, pass int) *coordinatePass {
	n := len(p.Nodes)
	c := &coordinatePass{p: p, layers: make([][]int32, len(layers)), pos: make([]int32, n), rank: make([]int32, n), root: make([]int32, n), align: make([]int32, n), sink: make([]int32, n), x: make([]int64, n), shift: make([]int64, n), set: make([]bool, n), shifted: make([]bool, n), marked: marked, gap: gap}
	for i := range n {
		c.root[i] = int32(i)
		c.align[i] = int32(i)
		c.sink[i] = int32(i)
	}
	for i := range layers {
		r := i
		if pass >= 2 {
			r = len(layers) - 1 - i
		}
		c.layers[i] = slices.Clone(layers[r])
		if pass%2 == 1 {
			slices.Reverse(c.layers[i])
		}
		for j, v := range c.layers[i] {
			c.pos[v] = int32(j)
			c.rank[v] = int32(i)
		}
	}
	return c
}
func (c *coordinatePass) neighbours(v int32) []int32 {
	var edges []int32
	for i, e := range c.p.Edges {
		if e.Head == v && c.rank[e.Tail] < c.rank[v] || e.Tail == v && c.rank[e.Head] < c.rank[v] {
			edges = append(edges, int32(i))
		}
	}
	slices.SortStableFunc(edges, func(a, b int32) int {
		u, w := c.other(a, v), c.other(b, v)
		if d := cmp.Compare(c.pos[u], c.pos[w]); d != 0 {
			return d
		}
		return cmp.Compare(a, b)
	})
	return edges
}
func (c *coordinatePass) other(e, v int32) int32 {
	edge := c.p.Edges[e]
	if edge.Tail == v {
		return edge.Head
	}
	return edge.Tail
}
func (c *coordinatePass) alignment() {
	for _, layer := range c.layers {
		c.alignLayer(layer)
	}
}
func (c *coordinatePass) alignLayer(layer []int32) {
	last := int32(-1)
	for _, v := range layer {
		last = c.alignNode(v, last)
	}
}
func (c *coordinatePass) alignNode(v, last int32) int32 {
	neighbours := c.neighbours(v)
	if len(neighbours) == 0 {
		return last
	}
	for _, index := range [2]int{(len(neighbours) - 1) / 2, len(neighbours) / 2} {
		edge := neighbours[index]
		other := c.other(edge, v)
		if c.align[v] == v && !c.marked[edge] && c.pos[other] > last {
			c.align[other] = v
			c.align[v] = c.root[other]
			c.root[v] = c.root[other]
			last = c.pos[other]
		}
	}
	return last
}
func (c *coordinatePass) separation(a, b int32) int64 {
	left, right := c.p.Nodes[a], c.p.Nodes[b]
	gap := c.gap
	if (borderMember(c.p, left, right) || borderMember(c.p, right, left)) && c.p.ClusterPad > 0 {
		gap = int64(c.p.ClusterPad)
	} else if ownTitleAnchor(left, right) {
		gap = 0
	}
	return int64(left.W)/2 + int64(left.Extent) + int64(right.W)/2 + int64(right.Extent) + gap
}
func (c *coordinatePass) predecessor(w int32) (int32, bool) {
	if c.pos[w] == 0 {
		return 0, false
	}
	return c.layers[c.rank[w]][c.pos[w]-1], true
}
func (c *coordinatePass) place(root int32, fuel *int) error {
	stack := [][2]int32{{root, root}}
	c.set[root] = true
	for len(stack) > 0 {
		if *fuel == 0 {
			return ErrGraph
		}
		*fuel--
		f := &stack[len(stack)-1]
		v, w := f[0], f[1]
		pred, ok := c.predecessor(w)
		if ok && !c.set[c.root[pred]] {
			u := c.root[pred]
			c.set[u] = true
			stack = append(stack, [2]int32{u, u})
			continue
		}
		if ok {
			c.placeAfter(v, w, pred)
		}
		f[1] = c.align[w]
		if f[1] != v {
			continue
		}
		c.finishBlock(v)
		stack = stack[:len(stack)-1]
	}
	return nil
}
func (c *coordinatePass) placeAfter(v, w, pred int32) {
	u := c.root[pred]
	if c.sink[v] == v {
		c.sink[v] = c.sink[u]
	}
	if c.sink[v] == c.sink[u] {
		c.x[v] = max(c.x[v], c.add(c.x[u], c.separation(pred, w)))
	}
}
func (c *coordinatePass) finishBlock(v int32) {
	for m := c.align[v]; m != v; m = c.align[m] {
		c.x[m] = c.x[v]
		c.sink[m] = c.sink[v]
		c.set[m] = true
	}
}
func (c *coordinatePass) offsets() {
	pairs := make([][][2]int32, len(c.layers))
	for _, layer := range c.layers {
		for i := 1; i < len(layer); i++ {
			a, b := layer[i-1], layer[i]
			if c.sink[a] != c.sink[b] {
				r := c.rank[c.sink[b]]
				pairs[r] = append(pairs[r], [2]int32{a, b})
			}
		}
	}
	for i, layer := range c.layers {
		if len(layer) == 0 {
			continue
		}
		s := layer[0]
		if c.sink[s] == s && !c.shifted[s] {
			c.shifted[s] = true
		}
		c.shiftPairs(pairs[i])
	}
	for v := range c.x {
		c.x[v] = c.add(c.x[v], c.shift[c.sink[v]])
	}
}
func (c *coordinatePass) shiftPairs(pairs [][2]int32) {
	for _, pair := range pairs {
		a, b := pair[0], pair[1]
		sa, sb := c.sink[a], c.sink[b]
		d := c.subtract(c.subtract(c.add(c.shift[sb], c.x[b]), c.x[a]), c.separation(a, b))
		if !c.shifted[sa] || d < c.shift[sa] {
			c.shift[sa] = d
			c.shifted[sa] = true
		}
	}
}
func (c *coordinatePass) run(pass int) ([]int64, error) {
	c.alignment()
	fuel := 2 * len(c.x)
	for _, layer := range c.layers {
		if err := c.placeLayer(layer, &fuel); err != nil {
			return nil, err
		}
	}
	c.offsets()
	if pass%2 == 1 {
		for i := range c.x {
			c.x[i] = c.subtract(0, c.x[i])
		}
	}
	if len(c.x) > 0 {
		lo := slices.Min(c.x)
		for i := range c.x {
			c.x[i] = c.subtract(c.x[i], lo)
		}
	}
	return c.x, c.err
}
func (c *coordinatePass) placeLayer(layer []int32, fuel *int) error {
	for _, v := range layer {
		if c.root[v] != v || c.set[v] {
			continue
		}
		if err := c.place(v, fuel); err != nil {
			return err
		}
	}
	return nil
}
func CrossCoords(p *Proper, layers [][]int32) ([]int32, error) {
	pos, err := coordinateLayers(p, layers)
	if err != nil {
		return nil, err
	}
	params, err := coordinateParams(p)
	if err != nil {
		return nil, err
	}
	if len(pos) == 0 {
		return []int32{}, nil
	}
	marked := typeOneConflicts(p, pos)
	var passes [4][]int64
	for k := range passes {
		passes[k], err = newCoordinatePass(p, layers, marked, int64(params.NodeGap), k).run(k)
		if err != nil {
			return nil, err
		}
	}
	return balanceCoordinates(passes)
}
func balanceCoordinates(passes [4][]int64) ([]int32, error) {
	widths := [4]int64{}
	var arithmetic coordinateArithmetic
	best := 0
	for k, x := range passes {
		widths[k] = slices.Max(x)
		if widths[k] < widths[best] {
			best = k
		}
	}
	low := int64(0)
	for k := range passes {
		if k%2 == 0 {
			continue
		}
		d := arithmetic.subtract(widths[best], widths[k])
		low = min(low, d)
		for i := range passes[k] {
			passes[k][i] = arithmetic.add(passes[k][i], d)
		}
	}
	out := make([]int32, len(passes[0]))
	for i := range out {
		v := [4]int64{}
		for k := range v {
			v[k] = arithmetic.subtract(passes[k][i], low)
		}
		slices.Sort(v[:])
		n := arithmetic.add(v[1], v[2]) / 2
		if n > math.MaxInt32 {
			return nil, geom.ErrOverflow
		}
		out[i] = int32(n)
	}
	return out, arithmetic.err
}
func rankHeights(p *Proper, layers [][]int32) []int32 {
	h := make([]int32, len(layers))
	for i, layer := range layers {
		for _, v := range layer {
			h[i] = max(h[i], p.Nodes[v].H)
		}
	}
	return h
}
func RankCoords(p *Proper, layers [][]int32, r *Routing) ([]int32, []int32, error) {
	if _, err := coordinateLayers(p, layers); err != nil {
		return nil, nil, err
	}
	params, err := coordinateParams(p)
	if err != nil {
		return nil, nil, err
	}
	if r == nil || len(r.Gaps) != max(0, len(layers)-1) {
		return nil, nil, ErrGraph
	}
	h := rankHeights(p, layers)
	top, err := rankBandTops(h, r, params)
	if err != nil {
		return nil, nil, err
	}
	y := make([]int32, len(p.Nodes))
	for v, n := range p.Nodes {
		rank := p.Rank[v]
		a := int64(top[rank]) + int64(h[rank]-n.H)/2
		switch n.Border {
		case BorderTop:
			a = int64(top[rank])
		case BorderBottom:
			a = int64(top[rank]) + int64(h[rank])
		}
		if a > math.MaxInt32 {
			return nil, nil, geom.ErrOverflow
		}
		y[v] = int32(a)
	}
	return y, top, nil
}

func rankBandTops(h []int32, r *Routing, params Params) ([]int32, error) {
	top := make([]int32, len(h))
	for i := 1; i < len(top); i++ {
		n := int64(top[i-1]) + int64(h[i-1]) + int64(params.RankGap) + int64(params.Slot)*int64(r.Gaps[i-1].Slots)
		if n > math.MaxInt32 {
			return nil, geom.ErrOverflow
		}
		top[i] = int32(n)
	}
	return top, nil
}
