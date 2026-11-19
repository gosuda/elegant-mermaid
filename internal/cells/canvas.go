package cells

import (
	"errors"

	"github.com/gosuda/elegant-mermaid/internal/geom"
)

type Charset uint8

const (
	CharsetUnicode Charset = iota
	CharsetASCII
)

type Style uint8

const (
	StyleNone Style = iota
	StyleDotted
	StyleRounded
	StyleLight
	StyleHeavy
	StyleDouble
)

const (
	BitN uint8 = 1
	BitE uint8 = 2
	BitS uint8 = 4
	BitW uint8 = 8
)

var ErrNegativeSize = errors.New("cells: negative canvas size")

type Cell struct {
	Mask     uint8
	Style    Style
	Dots     uint8
	Symbol   rune
	Label    string
	Cont     bool
	Ink      Token
	LabelInk Token
}

type Canvas struct {
	W, H  int
	cells []Cell
}

func New(w, h int) (*Canvas, error) {
	if w < 0 || h < 0 {
		return nil, ErrNegativeSize
	}
	if h != 0 && w > int(^uint(0)>>1)/h {
		return nil, geom.ErrOverflow
	}
	return &Canvas{W: w, H: h, cells: make([]Cell, w*h)}, nil
}

func (c *Canvas) Cell(col, row int) (Cell, bool) {
	if !c.inside(col, row) {
		return Cell{}, false
	}
	return c.cells[row*c.W+col], true
}

func (c *Canvas) inside(col, row int) bool {
	return col >= 0 && col < c.W && row >= 0 && row < c.H
}

func (c *Canvas) Put(col, row int, f func(*Cell)) {
	if !c.inside(col, row) {
		return
	}
	f(&c.cells[row*c.W+col])
}

func (c *Canvas) PutSymbol(col, row int, s rune) {
	c.Put(col, row, func(cell *Cell) {
		if s > cell.Symbol {
			cell.Symbol = s
		}
	})
}

func (c *Canvas) Attach(col, row int, mask uint8, style Style) {
	c.Put(col, row, func(cell *Cell) {
		cell.Mask |= mask
		if style > cell.Style {
			cell.Style = style
		}
	})
}

func (c *Canvas) AttachInk(col, row int, mask uint8, style Style, ink Token) {
	c.Put(col, row, func(cell *Cell) {
		cell.Mask |= mask
		if style > cell.Style {
			cell.Style = style
		}
		if ink > cell.Ink {
			cell.Ink = ink
		}
	})
}

func (c *Canvas) HSegment(x0, x1, y int, style Style) {
	if x0 >= x1 {
		return
	}
	c.Attach(x0, y, BitE, style)
	for x := x0 + 1; x < x1; x++ {
		c.Attach(x, y, BitE|BitW, style)
	}
	c.Attach(x1, y, BitW, style)
}

func (c *Canvas) VSegment(x, y0, y1 int, style Style) {
	if y0 >= y1 {
		return
	}
	c.Attach(x, y0, BitS, style)
	for y := y0 + 1; y < y1; y++ {
		c.Attach(x, y, BitN|BitS, style)
	}
	c.Attach(x, y1, BitN, style)
}

func (c *Canvas) Segment(a, b geom.Point, style Style) {
	switch {
	case a.Y == b.Y:
		c.HSegment(min(int(a.X), int(b.X)), max(int(a.X), int(b.X)), int(a.Y), style)
	case a.X == b.X:
		c.VSegment(int(a.X), min(int(a.Y), int(b.Y)), max(int(a.Y), int(b.Y)), style)
	}
}

func (c *Canvas) Polyline(pts []geom.Point, style Style) {
	for i := 1; i < len(pts); i++ {
		c.Segment(pts[i-1], pts[i], style)
	}
}

func MergeCell(a, b Cell) Cell {
	a.Mask |= b.Mask
	a.Dots |= b.Dots
	a.Style = max(a.Style, b.Style)
	a.Symbol = max(a.Symbol, b.Symbol)
	a.Ink = max(a.Ink, b.Ink)
	return a
}

func (c *Canvas) PutLabel(col, row int, cluster string, width int, ink Token) bool {
	if width < 1 || width > 2 || cluster == "" || !c.inside(col, row) || width > c.W-col {
		return false
	}
	for x := col; x < col+width; x++ {
		if !c.cells[row*c.W+x].labelFree() {
			return false
		}
	}
	c.Put(col, row, func(v *Cell) { v.Label = cluster; v.LabelInk = ink })
	if width == 2 {
		c.Put(col+1, row, func(v *Cell) { v.Cont = true })
	}
	return true
}

func (v Cell) labelFree() bool {
	return v.Mask == 0 && v.Symbol == 0 && v.Label == "" && !v.Cont
}
