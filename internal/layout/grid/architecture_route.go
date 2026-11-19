package grid

import (
	"cmp"
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/geom"
)

type portEnd struct {
	p, g     pt
	line     int64
	vertical bool
	at       cell
}

type endRef struct {
	edge int
	to   bool
}

func (b *archBuilder) geometry() {
	b.boxes = make([]span, b.real)
	b.icons = make([]span, b.real)
	b.labels = make([]span, b.real)
	for i, n := range b.in.Nodes {
		c := b.pos[i]
		iw, ih := int64(n.Icon.W), int64(n.Icon.H)
		x := c.x*b.px + geom.FloorDiv(b.px-iw, 2)
		y := c.y*b.py + b.top
		if n.Junction {
			y = c.y*b.py + geom.FloorDiv(b.py-ih, 2)
		}
		b.icons[i] = span{x, y, x + iw, y + ih}
		b.labels[i] = sized(x+geom.FloorDiv(iw-int64(n.Label.W), 2), y+ih, n.Label)
		b.boxes[i] = span{x, y, x + iw, y + ih + int64(n.Label.H) + b.underLabel(n)}
	}
	b.titles = make([]span, len(b.in.Groups))
	b.badges = make([]span, len(b.in.Groups))
	inset := int64(b.p.Inset)
	for g, entry := range b.in.Groups {
		f := b.frame[g]
		lead, badge := int64(0), int64(0)
		if entry.Icon {
			lead, badge = int64(b.p.Badge)+inset, int64(b.p.Badge)
		}
		b.badges[g] = span{f.x0 + inset, f.y0 + inset, f.x0 + inset + badge, f.y0 + inset + badge}
		b.titles[g] = sized(f.x0+inset+lead, f.y0+inset, entry.Title)
	}
}

func (b *archBuilder) underLabel(n ArchNode) int64 {
	if n.Label.H > 0 {
		return int64(b.p.Thickness)
	}
	return 0
}

func (b *archBuilder) vline(k int64) int64 { return k*b.px - b.shift }

func (b *archBuilder) hline(k int64) int64 { return k*b.py - b.shift }

func (b *archBuilder) route() {
	ends := b.assignPorts()
	b.routes = make([][]pt, len(b.in.Edges))
	for i := range b.in.Edges {
		b.routes[i] = b.path(ends[i][0], ends[i][1])
	}
}

func (b *archBuilder) assignPorts() [][2]portEnd {
	slots := make([][4][]endRef, b.real)
	for i, e := range b.in.Edges {
		slots[e.From][e.FromSide-geom.SideTop] = append(slots[e.From][e.FromSide-geom.SideTop], endRef{i, false})
		slots[e.To][e.ToSide-geom.SideTop] = append(slots[e.To][e.ToSide-geom.SideTop], endRef{i, true})
	}
	out := make([][2]portEnd, len(b.in.Edges))
	for n := range slots {
		for s := range slots[n] {
			side := geom.SideTop + geom.Side(s)
			list := slots[n][s]
			slices.SortStableFunc(list, func(x, y endRef) int { return b.compareEnds(side, x, y) })
			for k, ref := range list {
				slot := 0
				if ref.to {
					slot = 1
				}
				out[ref.edge][slot] = b.end(n, side, k, len(list))
			}
		}
	}
	return out
}

func (b *archBuilder) compareEnds(side geom.Side, x, y endRef) int {
	return cmp.Or(
		cmp.Compare(b.otherKey(side, x), b.otherKey(side, y)),
		cmp.Compare(x.edge, y.edge),
		cmp.Compare(boolOrder(x.to), boolOrder(y.to)),
	)
}

func boolOrder(v bool) int {
	if v {
		return 1
	}
	return 0
}

func (b *archBuilder) otherKey(side geom.Side, r endRef) int64 {
	e := b.in.Edges[r.edge]
	other := e.To
	if r.to {
		other = e.From
	}
	if side == geom.SideLeft || side == geom.SideRight {
		return b.pos[other].y
	}
	return b.pos[other].x
}

func (b *archBuilder) end(n int, side geom.Side, i, k int) portEnd {
	node := b.in.Nodes[n]
	if node.Junction {
		i, k = 0, 1
	}
	box, icon, c := b.boxes[n], b.icons[n], b.pos[n]
	along := func(length int64) int64 { return geom.FloorDiv(int64(i+1)*length, int64(k+1)) }
	switch side {
	case geom.SideTop:
		p := pt{icon.x0 + along(icon.x1-icon.x0), box.y0}
		return portEnd{p: p, g: pt{p.x, b.hline(c.y)}, line: b.hline(c.y), at: c}
	case geom.SideBottom:
		p := pt{icon.x0 + along(icon.x1-icon.x0), box.y1}
		return portEnd{p: p, g: pt{p.x, b.hline(c.y + 1)}, line: b.hline(c.y + 1), at: c}
	case geom.SideLeft:
		p := pt{box.x0, icon.y0 + along(icon.y1-icon.y0)}
		return portEnd{p: p, g: pt{b.vline(c.x), p.y}, line: b.vline(c.x), vertical: true, at: c}
	}
	p := pt{box.x1, icon.y0 + along(icon.y1-icon.y0)}
	return portEnd{p: p, g: pt{b.vline(c.x + 1), p.y}, line: b.vline(c.x + 1), vertical: true, at: c}
}

func (b *archBuilder) path(a, c portEnd) []pt {
	var points []pt
	switch {
	case a.vertical == c.vertical && a.line == c.line:
		points = []pt{a.p, a.g, c.g, c.p}
	case a.vertical && c.vertical:
		y := b.hline(a.at.y)
		points = []pt{a.p, a.g, {a.line, y}, {c.line, y}, c.g, c.p}
	case !a.vertical && !c.vertical:
		x := b.vline(a.at.x)
		points = []pt{a.p, a.g, {x, a.line}, {x, c.line}, c.g, c.p}
	case a.vertical:
		points = []pt{a.p, a.g, {a.line, c.line}, c.g, c.p}
	default:
		points = []pt{a.p, a.g, {c.line, a.line}, c.g, c.p}
	}
	return slices.CompactFunc(points, func(x, y pt) bool { return x == y })
}

type archSite struct {
	region span
	fixed  []span
	placed []span
}

func (b *archBuilder) content() span {
	all := empty
	for _, group := range [][]span{b.boxes, b.labels, b.frame, b.titles, b.badges} {
		for _, r := range group {
			all = all.union(r)
		}
	}
	for _, route := range b.routes {
		for _, p := range route {
			all = all.union(span{p.x, p.y, p.x, p.y})
		}
	}
	return all
}

func (b *archBuilder) placeLabels(content span) []span {
	margin := int64(b.p.Margin)
	site := &archSite{region: content.inflate(margin)}
	for _, group := range [][]span{b.boxes, b.labels, b.titles, b.badges} {
		site.fixed = append(site.fixed, group...)
	}
	out := make([]span, len(b.in.Edges))
	spillX, spillY := site.region.x1+margin, site.region.y0+margin
	for i, e := range b.in.Edges {
		if e.Label.W == 0 && e.Label.H == 0 {
			continue
		}
		r, ok := b.fit(site, b.routes[i], e.Label)
		if !ok {
			r = sized(spillX, spillY, e.Label)
			spillY += int64(e.Label.H) + margin
			site.region.x1 = max(site.region.x1, r.x1+margin)
			site.region.y1 = max(site.region.y1, spillY)
		}
		out[i] = r
		site.placed = append(site.placed, r)
	}
	return out
}

func (b *archBuilder) fit(site *archSite, route []pt, size geom.Size) (span, bool) {
	for _, r := range b.candidates(route, size) {
		if b.labelClear(site, r) {
			return r, true
		}
	}
	return span{}, false
}

func (b *archBuilder) candidates(route []pt, size geom.Size) []span {
	var order []int
	for i := 0; i+1 < len(route); i++ {
		if route[i] != route[i+1] {
			order = append(order, i)
		}
	}
	slices.SortStableFunc(order, func(i, j int) int {
		return cmp.Compare(length(route[j], route[j+1]), length(route[i], route[i+1]))
	})
	var out []span
	for _, i := range order {
		out = append(out, b.beside(route[i], route[i+1], size)...)
	}
	return out
}

func length(a, c pt) int64 { return max(a.x-c.x, c.x-a.x) + max(a.y-c.y, c.y-a.y) }

func (b *archBuilder) beside(from, to pt, size geom.Size) []span {
	mx, my := geom.FloorDiv(from.x+to.x, 2), geom.FloorDiv(from.y+to.y, 2)
	w, h := int64(size.W), int64(size.H)
	off, thick := int64(b.p.LabelGap), int64(b.p.Thickness)
	if from.y == to.y {
		return []span{
			sized(mx-geom.FloorDiv(w, 2), my-off-h, size),
			sized(mx-geom.FloorDiv(w, 2), my+thick+off, size),
		}
	}
	return []span{
		sized(mx+thick+off, my-geom.FloorDiv(h, 2), size),
		sized(mx-off-w, my-geom.FloorDiv(h, 2), size),
	}
}

func (b *archBuilder) labelClear(site *archSite, r span) bool {
	if !r.strictlyInside(site.region) {
		return false
	}
	for _, f := range b.frame {
		if r.overlaps(f) && !r.strictlyInside(f) {
			return false
		}
	}
	for _, others := range [][]span{site.fixed, site.placed} {
		if slices.ContainsFunc(others, r.overlaps) {
			return false
		}
	}
	thick := int64(b.p.Thickness)
	for _, route := range b.routes {
		for i := 0; i+1 < len(route); i++ {
			if r.overlaps(widened(route[i], route[i+1], thick)) {
				return false
			}
		}
	}
	return true
}

func widened(a, c pt, thick int64) span {
	return span{min(a.x, c.x) - thick, min(a.y, c.y) - thick, max(a.x, c.x) + thick, max(a.y, c.y) + thick}
}

func (b *archBuilder) finish() (ArchLayout, error) {
	all := b.content()
	if all == empty {
		all = span{}
	}
	labels := b.placeLabels(all)
	for _, r := range labels {
		if r.x1 > r.x0 && r.y1 > r.y0 {
			all = all.union(r)
		}
	}
	margin := int64(b.p.Margin)
	t := translation{dx: margin - all.x0, dy: margin - all.y0}
	out := ArchLayout{
		Boxes:      t.rects(b.boxes),
		Icons:      t.rects(b.icons),
		Labels:     t.rects(b.labels),
		Frames:     t.rects(b.frame),
		Titles:     t.rects(b.titles),
		GroupIcons: t.rects(b.badges),
		EdgeLabels: t.rects(labels),
		Budget:     b.budget,
	}
	for _, route := range b.routes {
		out.Routes = append(out.Routes, t.points(route))
	}
	width, height := all.x1-all.x0+2*margin, all.y1-all.y0+2*margin
	t.check(width)
	t.check(height)
	out.Canvas = geom.Size{W: int32(width), H: int32(height)}
	if t.bad {
		return ArchLayout{}, geom.ErrOverflow
	}
	return out, nil
}

type translation struct {
	dx, dy int64
	bad    bool
}

func (t *translation) check(v int64) int32 {
	if v < 0 || v > geom.CoordLimit {
		t.bad = true
		return 0
	}
	return int32(v)
}

func (t *translation) rects(in []span) []geom.Rect {
	out := make([]geom.Rect, len(in))
	for i, r := range in {
		if r.x1 == r.x0 && r.y1 == r.y0 {
			continue
		}
		x, y := t.check(r.x0+t.dx), t.check(r.y0+t.dy)
		w, h := t.check(r.x1-r.x0), t.check(r.y1-r.y0)
		out[i] = geom.Rect{X: x, Y: y, W: w, H: h}
	}
	return out
}

func (t *translation) points(in []pt) []geom.Point {
	out := make([]geom.Point, len(in))
	for i, p := range in {
		out[i] = geom.Point{X: t.check(p.x + t.dx), Y: t.check(p.y + t.dy)}
	}
	return out
}
