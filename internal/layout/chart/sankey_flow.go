package chart

import (
	"cmp"
	"fmt"
	"math"
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
)

const (
	unitQ16    = 1 << 16
	alphaBase  = 99
	alphaScale = 100
)

type alignment uint8

const (
	alignJustify alignment = iota
	alignLeft
	alignRight
	alignCenter
)

func parseAlignment(name string) alignment {
	switch name {
	case "left":
		return alignLeft
	case "right":
		return alignRight
	case "center":
		return alignCenter
	}
	return alignJustify
}

type arith struct{ failed bool }

func (a *arith) add(x, y int64) int64 {
	s := x + y
	if x > 0 && y > 0 && s < 0 || x < 0 && y < 0 && s >= 0 {
		a.failed = true
		return 0
	}
	return s
}

func (a *arith) mul(x, y int64) int64 {
	if x == 0 || y == 0 {
		return 0
	}
	p := x * y
	if p/y != x || x == math.MinInt64 && y == -1 || y == math.MinInt64 && x == -1 {
		a.failed = true
		return 0
	}
	return p
}

func (a *arith) roundHalfUp(n, d int64) int64 {
	return geom.FloorDiv(a.add(a.mul(2, n), d), a.mul(2, d))
}

func (a *arith) scaled(v, q int64) int64 { return geom.FloorDiv(a.mul(v, q), unitQ16) }

type flowNode struct {
	value  int64
	depth  int
	height int
	layer  int
	y0, y1 int64
	out    []int
	in     []int
}

type flowLink struct {
	source, target int
	value, width   int64
	y0, y1         int64
}

type flow struct {
	nodes      []flowNode
	links      []flowLink
	columns    [][]int
	extent     int64
	pad        int64
	py         int64
	iterations int
	arith      arith
}

func errCircular() error { return fmt.Errorf("sankey layout: circular link: %w", errDomain) }

func newFlow(s *chartmodel.Sankey) (*flow, error) {
	f := &flow{nodes: make([]flowNode, len(s.Nodes)), links: make([]flowLink, len(s.Links))}
	for i, l := range s.Links {
		switch {
		case l.Kind == chartmodel.ValueOverflow:
			return nil, ErrOverflow
		case l.Kind == chartmodel.ValueNonFinite:
			return nil, fmt.Errorf("sankey layout: link %d has no finite value: %w", i, errDomain)
		case l.Value < 0:
			return nil, fmt.Errorf("sankey layout: link %d has a negative value: %w", i, errDomain)
		}
		f.links[i] = flowLink{source: l.Source, target: l.Target, value: int64(l.Value)}
		f.nodes[l.Source].out = append(f.nodes[l.Source].out, i)
		f.nodes[l.Target].in = append(f.nodes[l.Target].in, i)
	}
	for i := range f.nodes {
		n := &f.nodes[i]
		n.value = max(f.sum(n.out), f.sum(n.in))
	}
	return f, nil
}

func (f *flow) sum(list []int) int64 {
	var total int64
	for _, li := range list {
		total = f.arith.add(total, f.links[li].value)
	}
	return total
}

func (f *flow) outgoing(v int) []int { return f.nodes[v].out }

func (f *flow) incoming(v int) []int { return f.nodes[v].in }

func (f *flow) targetOf(li int) int { return f.links[li].target }

func (f *flow) sourceOf(li int) int { return f.links[li].source }

func (f *flow) depths() ([]int, error) { return f.levels(f.outgoing, f.targetOf) }

func (f *flow) heights() ([]int, error) { return f.levels(f.incoming, f.sourceOf) }

func (f *flow) levels(adjacent func(int) []int, far func(int) int) ([]int, error) {
	n := len(f.nodes)
	level := make([]int, n)
	marked := make([]bool, n)
	current := make([]int, n)
	for i := range current {
		current[i] = i
	}
	for x := 0; len(current) > 0; {
		for _, v := range current {
			level[v] = x
			for _, li := range adjacent(v) {
				marked[far(li)] = true
			}
		}
		if x++; x > n {
			return nil, errCircular()
		}
		current = current[:0]
		for i, m := range marked {
			if m {
				current = append(current, i)
				marked[i] = false
			}
		}
	}
	return level, nil
}

func (f *flow) place(a alignment) error {
	depth, err := f.depths()
	if err != nil {
		return err
	}
	height, err := f.heights()
	if err != nil {
		return err
	}
	count := 1
	for i := range f.nodes {
		f.nodes[i].depth, f.nodes[i].height = depth[i], height[i]
		count = max(count, depth[i]+1)
	}
	f.columns = make([][]int, count)
	for i := range f.nodes {
		layer := min(max(f.layerOf(i, a, count), 0), count-1)
		f.nodes[i].layer = layer
		f.columns[layer] = append(f.columns[layer], i)
	}
	return nil
}

func (f *flow) layerOf(i int, a alignment, count int) int {
	n := &f.nodes[i]
	switch a {
	case alignLeft:
		return n.depth
	case alignRight:
		return count - 1 - n.height
	case alignCenter:
		return f.centerLayer(n)
	}
	if len(n.out) > 0 {
		return n.depth
	}
	return count - 1
}

func (f *flow) centerLayer(n *flowNode) int {
	if len(n.in) > 0 {
		return n.depth
	}
	if len(n.out) == 0 {
		return 0
	}
	shallowest := math.MaxInt
	for _, li := range n.out {
		shallowest = min(shallowest, f.nodes[f.links[li].target].depth)
	}
	return shallowest - 1
}

func (f *flow) padding() {
	widest := 0
	for _, c := range f.columns {
		widest = max(widest, len(c))
	}
	f.py = f.pad
	if widest > 1 {
		f.py = min(f.pad, geom.FloorDiv(f.extent, int64(widest-1)))
	}
}

func (f *flow) scale() (int64, error) {
	var ky int64
	found := false
	for _, c := range f.columns {
		if len(c) == 0 {
			continue
		}
		room := f.extent - int64(len(c)-1)*f.py
		if room < 0 {
			return 0, fmt.Errorf("sankey layout: column does not fit its height: %w", errDomain)
		}
		var total int64
		for _, n := range c {
			total = f.arith.add(total, f.nodes[n].value)
		}
		if total <= 0 {
			continue
		}
		candidate := geom.FloorDiv(f.arith.mul(room, unitQ16), total)
		if !found || candidate < ky {
			ky, found = candidate, true
		}
	}
	return ky, nil
}

func (f *flow) initialise() error {
	ky, err := f.scale()
	if err != nil {
		return err
	}
	for _, c := range f.columns {
		f.stack(c, ky)
		f.reorderLinks(c)
	}
	return nil
}

func (f *flow) stack(column []int, ky int64) {
	y := int64(0)
	for _, ni := range column {
		n := &f.nodes[ni]
		n.y0 = y
		n.y1 = f.arith.add(y, f.arith.scaled(n.value, ky))
		y = f.arith.add(n.y1, f.py)
		for _, li := range n.out {
			f.links[li].width = f.arith.scaled(f.links[li].value, ky)
		}
	}
	if len(column) == 0 {
		return
	}
	free := f.extent - (y - f.py)
	for k, ni := range column {
		shift := geom.FloorDiv(f.arith.mul(int64(k+1), free), int64(len(column)+1))
		f.nodes[ni].y0 = f.arith.add(f.nodes[ni].y0, shift)
		f.nodes[ni].y1 = f.arith.add(f.nodes[ni].y1, shift)
	}
}

func (f *flow) byTarget(a, b int) int {
	return cmp.Or(cmp.Compare(f.nodes[f.links[a].target].y0, f.nodes[f.links[b].target].y0), cmp.Compare(a, b))
}

func (f *flow) bySource(a, b int) int {
	return cmp.Or(cmp.Compare(f.nodes[f.links[a].source].y0, f.nodes[f.links[b].source].y0), cmp.Compare(a, b))
}

func (f *flow) reorderLinks(nodes []int) {
	for _, ni := range nodes {
		slices.SortFunc(f.nodes[ni].out, f.byTarget)
		slices.SortFunc(f.nodes[ni].in, f.bySource)
	}
}

func (f *flow) reorderNodeLinks(ni int) {
	n := &f.nodes[ni]
	for _, li := range n.in {
		slices.SortFunc(f.nodes[f.links[li].source].out, f.byTarget)
	}
	for _, li := range n.out {
		slices.SortFunc(f.nodes[f.links[li].target].in, f.bySource)
	}
}

func (f *flow) relax() {
	for i := range f.iterations {
		alpha := f.arith.mul(unitQ16, f.pow(alphaBase, i))
		alpha = geom.FloorDiv(alpha, f.pow(alphaScale, i))
		beta := max(unitQ16-alpha, geom.FloorDiv(int64(i+1)*unitQ16, int64(f.iterations)))
		f.relaxRightToLeft(alpha, beta)
		f.relaxLeftToRight(alpha, beta)
	}
}

func (f *flow) pow(base int64, exponent int) int64 {
	v := int64(1)
	for range exponent {
		v = f.arith.mul(v, base)
	}
	return v
}

func (f *flow) relaxRightToLeft(alpha, beta int64) {
	for c := len(f.columns) - 2; c >= 0; c-- {
		for _, ni := range f.columns[c] {
			f.pullSource(ni, alpha)
		}
		f.settle(f.columns[c], beta)
	}
}

func (f *flow) relaxLeftToRight(alpha, beta int64) {
	for c := 1; c < len(f.columns); c++ {
		for _, ni := range f.columns[c] {
			f.pullTarget(ni, alpha)
		}
		f.settle(f.columns[c], beta)
	}
}

func (f *flow) settle(column []int, beta int64) {
	slices.SortStableFunc(column, func(a, b int) int { return cmp.Compare(f.nodes[a].y0, f.nodes[b].y0) })
	f.resolveCollisions(column, beta)
}

func (f *flow) pullSource(ni int, alpha int64) {
	var y, w int64
	for _, li := range f.nodes[ni].out {
		t := f.links[li].target
		v := f.arith.mul(f.links[li].value, int64(f.nodes[t].layer-f.nodes[ni].layer))
		y = f.arith.add(y, f.arith.mul(f.sourceTop(ni, t), v))
		w = f.arith.add(w, v)
	}
	f.shift(ni, y, w, alpha)
}

func (f *flow) pullTarget(ni int, alpha int64) {
	var y, w int64
	for _, li := range f.nodes[ni].in {
		s := f.links[li].source
		v := f.arith.mul(f.links[li].value, int64(f.nodes[ni].layer-f.nodes[s].layer))
		y = f.arith.add(y, f.arith.mul(f.targetTop(s, ni), v))
		w = f.arith.add(w, v)
	}
	f.shift(ni, y, w, alpha)
}

func (f *flow) shift(ni int, y, w, alpha int64) {
	if w <= 0 {
		return
	}
	n := &f.nodes[ni]
	dy := f.arith.roundHalfUp(f.arith.mul(f.arith.roundHalfUp(y, w)-n.y0, alpha), unitQ16)
	n.y0 = f.arith.add(n.y0, dy)
	n.y1 = f.arith.add(n.y1, dy)
	f.reorderNodeLinks(ni)
}

func (f *flow) prefix(list []int, stop func(link int) bool, gap int64) int64 {
	var total int64
	for _, li := range list {
		if stop(li) {
			break
		}
		total = f.arith.add(total, f.arith.add(f.links[li].width, gap))
	}
	return total
}

func (f *flow) targetTop(s, t int) int64 {
	src, tgt := &f.nodes[s], &f.nodes[t]
	a := f.prefix(src.out, func(li int) bool { return f.links[li].target == t }, f.py)
	b := f.prefix(tgt.in, func(li int) bool { return f.links[li].source == s }, 0)
	n := f.arith.add(f.arith.mul(2, src.y0), -f.arith.mul(int64(len(src.out)-1), f.py))
	n = f.arith.add(n, f.arith.add(f.arith.mul(2, a), -f.arith.mul(2, b)))
	return geom.FloorDiv(n, 2)
}

func (f *flow) sourceTop(s, t int) int64 {
	src, tgt := &f.nodes[s], &f.nodes[t]
	a := f.prefix(tgt.in, func(li int) bool { return f.links[li].source == s }, f.py)
	b := f.prefix(src.out, func(li int) bool { return f.links[li].target == t }, 0)
	n := f.arith.add(f.arith.mul(2, tgt.y0), -f.arith.mul(int64(len(tgt.in)-1), f.py))
	n = f.arith.add(n, f.arith.add(f.arith.mul(2, a), -f.arith.mul(2, b)))
	return geom.FloorDiv(n, 2)
}

func (f *flow) resolveCollisions(column []int, beta int64) {
	m := len(column)
	if m == 0 {
		return
	}
	k := m >> 1
	subject := &f.nodes[column[k]]
	f.pushUp(column, subject.y0-f.py, k-1, beta)
	f.pushDown(column, subject.y1+f.py, k+1, beta)
	f.pushUp(column, f.extent, m-1, beta)
	f.pushDown(column, 0, 0, beta)
}

func (f *flow) pushDown(column []int, y int64, from int, beta int64) {
	for i := from; i < len(column); i++ {
		n := &f.nodes[column[i]]
		if dy := f.arith.roundHalfUp(f.arith.mul(y-n.y0, beta), unitQ16); dy > 0 {
			n.y0 = f.arith.add(n.y0, dy)
			n.y1 = f.arith.add(n.y1, dy)
		}
		y = f.arith.add(n.y1, f.py)
	}
}

func (f *flow) pushUp(column []int, y int64, from int, beta int64) {
	for i := from; i >= 0; i-- {
		n := &f.nodes[column[i]]
		if dy := f.arith.roundHalfUp(f.arith.mul(n.y1-y, beta), unitQ16); dy > 0 {
			n.y0 = f.arith.add(n.y0, -dy)
			n.y1 = f.arith.add(n.y1, -dy)
		}
		y = f.arith.add(n.y0, -f.py)
	}
}

func (f *flow) anchorLinks() {
	for i := range f.nodes {
		n := &f.nodes[i]
		y := n.y0
		for _, li := range n.out {
			l := &f.links[li]
			l.y0 = f.arith.add(y, geom.FloorDiv(l.width, 2))
			y = f.arith.add(y, l.width)
		}
		y = n.y0
		for _, li := range n.in {
			l := &f.links[li]
			l.y1 = f.arith.add(y, geom.FloorDiv(l.width, 2))
			y = f.arith.add(y, l.width)
		}
	}
}

func (f *flow) run(a alignment) error {
	if err := f.place(a); err != nil {
		return err
	}
	f.padding()
	if err := f.initialise(); err != nil {
		return err
	}
	f.relax()
	f.anchorLinks()
	if f.arith.failed {
		return ErrOverflow
	}
	return nil
}
