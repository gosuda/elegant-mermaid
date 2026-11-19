package grid

import (
	"cmp"
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/geom"
)

const identity = int64(1) << 60

var empty = span{identity, identity, -identity, -identity}

var sideSteps = map[geom.Side]cell{
	geom.SideLeft:   {-1, 0},
	geom.SideRight:  {1, 0},
	geom.SideTop:    {0, -1},
	geom.SideBottom: {0, 1},
}

var sideOrder = [4]geom.Side{geom.SideLeft, geom.SideRight, geom.SideTop, geom.SideBottom}

type unit struct{ node, group int }

type levelEdge struct {
	a, b         int
	sideA, sideB geom.Side
}

type level struct {
	units    []unit
	rects    []span
	abs      []span
	at       []cell
	placed   []bool
	edges    []levelEdge
	incident [][]int
	bounds   span
}

func (b *archBuilder) place() {
	b.local = make([]cell, b.total)
	b.localGroup = make([]cell, len(b.in.Groups))
	b.rel = make([]span, len(b.in.Groups))
	b.lift()
	for g := len(b.in.Groups) - 1; g >= 0; g-- {
		b.arrange(g)
	}
	b.arrange(-1)
	b.resolve()
}

func (b *archBuilder) chainOf(v int) []unit {
	var groups []unit
	for g := b.parent[v]; g >= 0; g = b.in.Groups[g].Parent {
		groups = append(groups, unit{-1, g})
	}
	slices.Reverse(groups)
	return append(groups, unit{v, -1})
}

type liftedEdge struct {
	a, b         unit
	sideA, sideB geom.Side
}

func (b *archBuilder) lift() {
	b.lifted = make([][]liftedEdge, len(b.in.Groups)+1)
	for _, e := range b.in.Edges {
		if e.From == e.To {
			continue
		}
		from, to := b.chainOf(e.From), b.chainOf(e.To)
		i := 0
		for from[i] == to[i] {
			i++
		}
		parent := -1
		if i > 0 {
			parent = from[i-1].group
		}
		b.lifted[parent+1] = append(b.lifted[parent+1], liftedEdge{from[i], to[i], e.FromSide, e.ToSide})
	}
}

func (b *archBuilder) cellRect() span { return span{0, 0, b.px, b.py} }

func (b *archBuilder) newLevel(p int) *level {
	lv := &level{bounds: empty}
	for _, w := range b.childNodes[p+1] {
		lv.units = append(lv.units, unit{w, -1})
	}
	for _, g := range b.childGroups[p+1] {
		lv.units = append(lv.units, unit{-1, g})
	}
	slices.SortFunc(lv.units, func(x, y unit) int { return cmp.Compare(b.key(x), b.key(y)) })
	index := make(map[unit]int, len(lv.units))
	for i, u := range lv.units {
		index[u] = i
		lv.rects = append(lv.rects, b.unitRect(u))
	}
	n := len(lv.units)
	lv.abs, lv.at, lv.placed, lv.incident = make([]span, n), make([]cell, n), make([]bool, n), make([][]int, n)
	for _, e := range b.lifted[p+1] {
		k := len(lv.edges)
		lv.edges = append(lv.edges, levelEdge{index[e.a], index[e.b], e.sideA, e.sideB})
		lv.incident[index[e.a]] = append(lv.incident[index[e.a]], k)
		lv.incident[index[e.b]] = append(lv.incident[index[e.b]], k)
	}
	return lv
}

func (b *archBuilder) key(u unit) int {
	if u.group >= 0 {
		return b.firstNode[u.group]
	}
	return u.node
}

func (b *archBuilder) unitRect(u unit) span {
	if u.group >= 0 {
		return b.rel[u.group]
	}
	return b.cellRect()
}

func (b *archBuilder) arrange(p int) {
	lv := b.newLevel(p)
	for first := range lv.units {
		if lv.placed[first] {
			continue
		}
		b.put(lv, first, b.seedCell(lv, first))
		queue := []int{first}
		for head := 0; head < len(queue); head++ {
			if b.pops >= int64(b.p.Fuel) {
				b.budget = true
				break
			}
			b.pops++
			queue = b.expand(lv, queue[head], queue)
		}
	}
	content := empty
	for i, u := range lv.units {
		if u.group >= 0 {
			b.localGroup[u.group] = lv.at[i]
		} else {
			b.local[u.node] = lv.at[i]
		}
		content = content.union(lv.abs[i])
	}
	if p >= 0 {
		b.rel[p] = b.frameOf(p, content)
	}
}

func (b *archBuilder) seedCell(lv *level, u int) cell {
	if lv.bounds == empty {
		return cell{}
	}
	return cell{ceilDiv(lv.bounds.x1-lv.rects[u].x0, b.px) + 1, 0}
}

func (b *archBuilder) put(lv *level, u int, c cell) {
	lv.placed[u], lv.at[u] = true, c
	lv.abs[u] = lv.rects[u].shift(c.x*b.px, c.y*b.py)
	lv.bounds = lv.bounds.union(lv.abs[u])
}

func (b *archBuilder) expand(lv *level, u int, queue []int) []int {
	for _, k := range lv.incident[u] {
		e := lv.edges[k]
		v, side := e.b, e.sideA
		if e.b == u {
			v, side = e.a, e.sideB
		}
		if lv.placed[v] {
			continue
		}
		b.put(lv, v, b.choose(lv, v, u, side))
		queue = append(queue, v)
	}
	return queue
}

func (b *archBuilder) reach(lv *level, v, u int, side geom.Side) cell {
	a, r, from := lv.abs[u], lv.rects[v], lv.at[u]
	switch side {
	case geom.SideLeft:
		return cell{min(geom.FloorDiv(a.x0-r.x1, b.px), from.x-1), from.y}
	case geom.SideRight:
		return cell{max(ceilDiv(a.x1-r.x0, b.px), from.x+1), from.y}
	case geom.SideTop:
		return cell{from.x, min(geom.FloorDiv(a.y0-r.y1, b.py), from.y-1)}
	}
	return cell{from.x, max(ceilDiv(a.y1-r.y0, b.py), from.y+1)}
}

func (b *archBuilder) choose(lv *level, v, u int, side geom.Side) cell {
	sides := []geom.Side{side}
	for _, s := range sideOrder {
		if s != side {
			sides = append(sides, s)
		}
	}
	var candidates []cell
	for extra := range int64(2) {
		for _, s := range sides {
			step, c := sideSteps[s], b.reach(lv, v, u, s)
			candidates = append(candidates, cell{c.x + extra*step.x, c.y + extra*step.y})
		}
	}
	tiers := []struct {
		accept func(*level, int, cell) bool
		radius int64
	}{{b.alignedClear, int64(b.p.RingCap)}, {b.clear, b.sweep(lv, v)}}
	for _, t := range tiers {
		for _, c := range candidates {
			if t.accept(lv, v, c) {
				return c
			}
		}
		if c, found := b.ring(lv, v, lv.at[u], t.radius, t.accept); found {
			return c
		}
	}
	return b.seedCell(lv, v)
}

func (b *archBuilder) ring(lv *level, v int, from cell, radius int64, accept func(*level, int, cell) bool) (cell, bool) {
	for d := int64(1); d <= radius; d++ {
		for dy := -d; dy <= d; dy++ {
			dx := d - max(dy, -dy)
			for _, x := range []int64{from.x - dx, from.x + dx} {
				if c := (cell{x, from.y + dy}); accept(lv, v, c) {
					return c, true
				}
			}
		}
	}
	return cell{}, false
}

func (b *archBuilder) sweep(lv *level, v int) int64 {
	r := lv.rects[v]
	width := ceilDiv(lv.bounds.x1-lv.bounds.x0+r.x1-r.x0, b.px)
	height := ceilDiv(lv.bounds.y1-lv.bounds.y0+r.y1-r.y0, b.py)
	return width + height + 2
}

func (b *archBuilder) clear(lv *level, v int, c cell) bool {
	r := lv.rects[v].shift(c.x*b.px, c.y*b.py)
	for i, placed := range lv.placed {
		if placed && r.overlaps(lv.abs[i]) {
			return false
		}
	}
	return true
}

func (b *archBuilder) alignedClear(lv *level, v int, c cell) bool {
	return b.clear(lv, v, c) && b.aligned(lv, v, c)
}

func (b *archBuilder) aligned(lv *level, v int, c cell) bool {
	u := lv.units[v]
	if u.node < 0 {
		return true
	}
	for _, i := range b.alignsOf[u.node] {
		if !b.alignedMembers(lv, u.node, c, b.in.Aligns[i]) {
			return false
		}
	}
	return true
}

func (b *archBuilder) alignedMembers(lv *level, node int, c cell, a ArchAlign) bool {
	for _, m := range a.Members {
		j := slices.Index(lv.units, unit{m, -1})
		if m == node || j < 0 || !lv.placed[j] {
			continue
		}
		return (!a.Column || lv.at[j].x == c.x) && (a.Column || lv.at[j].y == c.y)
	}
	return true
}

func (b *archBuilder) resolve() {
	origins := make([]cell, len(b.in.Groups))
	b.frame = make([]span, len(b.in.Groups))
	for g, entry := range b.in.Groups {
		base := cell{}
		if entry.Parent >= 0 {
			base = origins[entry.Parent]
		}
		origins[g] = cell{base.x + b.localGroup[g].x, base.y + b.localGroup[g].y}
		b.frame[g] = b.rel[g].shift(origins[g].x*b.px, origins[g].y*b.py)
	}
	b.pos = make([]cell, b.total)
	for v, parent := range b.parent {
		base := cell{}
		if parent >= 0 {
			base = origins[parent]
		}
		b.pos[v] = cell{base.x + b.local[v].x, base.y + b.local[v].y}
	}
}
