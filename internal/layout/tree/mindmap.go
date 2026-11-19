package tree

import (
	"errors"

	"github.com/gosuda/elegant-mermaid/internal/geom"
)

var ErrInvalid = errors.New("tree layout: invalid input")

const NoParent = -1

type Node struct {
	Parent        int
	Width, Height int32
}

type Gaps struct {
	Level, Sibling int32
}

type Layout struct {
	Boxes  []geom.Rect
	Routes [][]geom.Point
}

type offset struct {
	u, y int64
}

type contour struct {
	u0, u1, top, bottom int64
}

type placer struct {
	nodes    []Node
	gaps     Gaps
	children [][]int
	rel      [][]offset
	dy       []int64
}

func Mindmap(nodes []Node, gaps Gaps) (Layout, error) {
	if len(nodes) == 0 {
		return Layout{}, nil
	}
	p, err := newPlacer(nodes, gaps)
	if err != nil {
		return Layout{}, err
	}
	for v := len(nodes) - 1; v >= 0; v-- {
		p.place(v)
	}
	return p.layout()
}

func newPlacer(nodes []Node, gaps Gaps) (*placer, error) {
	if gaps.Level < 0 || gaps.Sibling < 1 {
		return nil, ErrInvalid
	}
	p := &placer{nodes: nodes, gaps: gaps, children: make([][]int, len(nodes)), rel: make([][]offset, len(nodes)), dy: make([]int64, len(nodes))}
	if err := p.link(); err != nil {
		return nil, err
	}
	return p, nil
}

func (p *placer) link() error {
	var path []int
	for i, n := range p.nodes {
		if n.Width < 1 || n.Height < 1 {
			return ErrInvalid
		}
		if i == 0 {
			if n.Parent != NoParent {
				return ErrInvalid
			}
			path = append(path, 0)
			continue
		}
		path = unwind(path, n.Parent)
		if len(path) == 0 {
			return ErrInvalid
		}
		path = append(path, i)
		p.children[n.Parent] = append(p.children[n.Parent], i)
	}
	return nil
}

func unwind(path []int, parent int) []int {
	for len(path) > 0 && path[len(path)-1] != parent {
		path = path[:len(path)-1]
	}
	return path
}

func (p *placer) place(v int) {
	if v == 0 {
		right, left := sides(p.children[0])
		p.stack(right)
		p.stack(left)
		return
	}
	p.stack(p.children[v])
	step := int64(p.nodes[v].Width) + int64(p.gaps.Level)
	rel := []offset{{}}
	for _, c := range p.children[v] {
		for _, o := range p.rel[c] {
			rel = append(rel, offset{u: step + o.u, y: p.dy[c] + o.y})
		}
		p.rel[c] = nil
	}
	p.rel[v] = rel
}

func sides(children []int) (right, left []int) {
	for i, c := range children {
		if i%2 == 0 {
			right = append(right, c)
		} else {
			left = append(left, c)
		}
	}
	return right, left
}

func (p *placer) stack(list []int) {
	if len(list) == 0 {
		return
	}
	var frame []contour
	ys := make([]int64, len(list))
	for j, c := range list {
		if j > 0 {
			ys[j] = p.separation(frame, c)
		}
		frame = p.extend(frame, c, ys[j])
	}
	centre := geom.FloorDiv(ys[0]+ys[len(ys)-1], 2)
	for j, c := range list {
		p.dy[c] = ys[j] - centre
	}
}

func (p *placer) contourBox(c, k int, o offset) contour {
	node := p.nodes[c+k]
	top := o.y - geom.FloorDiv(int64(node.Height), 2)
	return contour{u0: o.u - int64(p.gaps.Level), u1: o.u + int64(node.Width), top: top, bottom: top + int64(node.Height)}
}

func overlaps(a, b contour) bool { return a.u0 < b.u1 && b.u0 < a.u1 }

func (p *placer) separation(frame []contour, c int) int64 {
	best := int64(0)
	first := true
	for k, o := range p.rel[c] {
		b := p.contourBox(c, k, o)
		for _, a := range frame {
			if !overlaps(a, b) {
				continue
			}
			need := a.bottom - b.top + int64(p.gaps.Sibling)
			if first || need > best {
				best, first = need, false
			}
		}
	}
	return best
}

func (p *placer) extend(frame []contour, c int, y int64) []contour {
	for k, o := range p.rel[c] {
		b := p.contourBox(c, k, o)
		b.top, b.bottom = b.top+y, b.bottom+y
		frame = append(frame, b)
	}
	return frame
}
