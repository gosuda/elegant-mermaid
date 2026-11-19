package tree

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
)

type bone struct {
	x0, t0, x1, t1 int64
	count          int64
	drawn          int64
}

func (f *fish) y(r *rib, t int64) int64 {
	if r.upper {
		return f.spineY - t
	}
	return f.spineY + t
}

func (f *fish) run(rise int64) int64 {
	return geom.FloorDiv(rise*int64(f.p.Cos), int64(f.p.Sin))
}

func (f *fish) slot(r *rib, position int) int64 {
	return geom.FloorDiv(r.length*int64(position+1), int64(len(r.entries))+1)
}

func (f *fish) place(r *rib) error {
	end := spot{x: -f.run(r.length), y: f.y(r, r.length)}
	r.pieces = []piece{{node: r.cause, box: f.causeBox(r, end), route: [2]spot{{x: 0, y: f.spineY}, end}}}
	bones := make([]bone, len(r.entries)+1)
	bones[0] = bone{x1: end.x, t1: r.length, count: int64(len(f.children[r.cause]))}
	times := make([]int64, len(r.entries))
	for position, idx := range r.order {
		times[idx] = f.slot(r, position)
	}
	margin := f.run(r.heights) + marginSlack
	for i, e := range r.entries {
		b, err := f.bone(&bones[e.parent+1], e, times[i], margin)
		if err != nil {
			return err
		}
		bones[i+1] = b
		r.pieces = append(r.pieces, f.entryPiece(r, e, b))
	}
	return nil
}

func (f *fish) causeBox(r *rib, end spot) relBox {
	w, h := int64(f.nodes[r.cause].Width), int64(f.nodes[r.cause].Height)
	top := end.y
	if r.upper {
		top -= h
	}
	return relBox{x: end.x - geom.FloorDiv(w, 2), y: top, w: w, h: h}
}

func (f *fish) entryPiece(r *rib, e entry, b bone) piece {
	w, h := int64(f.nodes[e.node].Width), int64(f.nodes[e.node].Height)
	y := f.y(r, b.t1)
	return piece{
		node:  e.node,
		box:   relBox{x: b.x1 - w, y: y - geom.FloorDiv(h, 2), w: w, h: h},
		route: [2]spot{{x: b.x0, y: f.y(r, b.t0)}, {x: b.x1, y: y}},
	}
}

func (f *fish) bone(par *bone, e entry, t, margin int64) (bone, error) {
	count := int64(len(f.children[e.node]))
	if e.depth%2 != 0 {
		return f.diagonal(par, t, count), nil
	}
	den := par.t1 - par.t0
	if den <= 0 {
		return bone{}, ErrInvalid
	}
	x0 := par.x0 + geom.FloorDiv((par.x1-par.x0)*(t-par.t0), den)
	return bone{x0: x0, t0: t, x1: x0 - f.boneLength(count, margin), t1: t, count: count}, nil
}

func (f *fish) diagonal(par *bone, t, count int64) bone {
	k := par.drawn
	par.drawn++
	x0 := par.x0 + geom.FloorDiv((par.x1-par.x0)*(par.count-k), par.count+1)
	return bone{x0: x0, t0: par.t0, x1: x0 - f.run(t-par.t0), t1: t, count: count}
}

func (f *fish) boneLength(count, margin int64) int64 {
	planned := int64(f.p.BoneStub)
	if count > 0 {
		planned = int64(f.p.BoneBase) + count*int64(f.p.BonePerChild)
	}
	return max(planned, (count+1)*margin)
}

func (r *rib) extent() (left, reach int64) {
	left = r.pieces[0].box.x
	for _, p := range r.pieces {
		left = min(left, p.box.x)
		reach = max(reach, p.box.x+p.box.w)
	}
	return left, reach
}

func (f *fish) assemble() (Layout, error) {
	out := Layout{Boxes: make([]geom.Rect, len(f.nodes)), Routes: make([][]geom.Point, len(f.nodes))}
	head := f.nodes[0]
	box, err := checkedRect(0, f.spineY-geom.FloorDiv(int64(head.Height), 2), int64(head.Width), int64(head.Height))
	if err != nil {
		return Layout{}, err
	}
	out.Boxes[0] = box
	ceiling, previous := -int64(f.p.Inset), int64(0)
	for first := 0; first < len(f.ribs); first += 2 {
		pair := f.ribs[first:min(first+2, len(f.ribs))]
		left, reach := pairExtent(pair)
		attach := min(ceiling, previous-reach)
		for i := range pair {
			if err := f.emit(&out, &pair[i], attach); err != nil {
				return Layout{}, err
			}
		}
		previous = attach + left
		ceiling = previous
	}
	if len(f.ribs) > 0 {
		out.Routes[0], err = checkedRoute([2]spot{{x: previous, y: f.spineY}, {x: 0, y: f.spineY}}, 0)
	}
	return out, err
}

func pairExtent(pair []rib) (left, reach int64) {
	left, _ = pair[0].extent()
	for i := range pair {
		l, r := pair[i].extent()
		left, reach = min(left, l), max(reach, r)
	}
	return left, reach
}

func (f *fish) emit(out *Layout, r *rib, attach int64) error {
	for _, p := range r.pieces {
		box, err := checkedRect(attach+p.box.x, p.box.y, p.box.w, p.box.h)
		if err != nil {
			return err
		}
		route, err := checkedRoute(p.route, attach)
		if err != nil {
			return err
		}
		out.Boxes[p.node], out.Routes[p.node] = box, route
	}
	return nil
}

func checkedRect(x, y, w, h int64) (geom.Rect, error) {
	r, ok := rect(x, y, w, h)
	if !ok {
		return geom.Rect{}, geom.ErrOverflow
	}
	return r, nil
}

func checkedRoute(route [2]spot, dx int64) ([]geom.Point, error) {
	points := make([]geom.Point, len(route))
	for i, s := range route {
		x, y := s.x+dx, s.y
		if x < -geom.CoordLimit || x > geom.CoordLimit || y < -geom.CoordLimit || y > geom.CoordLimit {
			return nil, geom.ErrOverflow
		}
		points[i] = geom.Point{X: int32(x), Y: int32(y)}
	}
	return points, nil
}
