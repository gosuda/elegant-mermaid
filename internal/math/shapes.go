package math

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
)

type polyline [][2]int64

var radicalSign = polyline{{0, 600}, {250, 480}, {450, 1000}, {1000, 1000}}

const (
	flattenSteps       = 16
	flattenDenominator = flattenSteps * flattenSteps
	flattenBias        = flattenDenominator / 2
)

func (l *layouter) radical(e *Expr, size int64) (Box, error) {
	radicand, err := l.box(e.Radicand, size)
	if err != nil {
		return Box{}, err
	}
	var index Box
	signX := int64(0)
	if e.Index != nil {
		if index, err = l.box(e.Index, l.scriptSize(size)); err != nil {
			return Box{}, err
		}
		signX = int64(index.W) + l.k.scriptGap
	}
	ascent := max(int64(radicand.A)+l.k.radGap, l.k.supShift+int64(index.A))
	descent := max(int64(radicand.D), int64(index.D)-l.k.supShift, 0)
	radicandX := signX + l.k.radSignW
	box, err := finish(radicandX+int64(radicand.W), ascent, descent)
	if err != nil {
		return Box{}, err
	}
	sign := make(polyline, len(radicalSign))
	height := ascent + descent
	for i, p := range radicalSign {
		sign[i] = [2]int64{roundHalfUp(p[0]*l.k.radSignW, 1000) + signX, height - roundHalfUp(p[1]*height, 1000)}
	}
	if err := addContainerPath(&box, sign); err != nil {
		return Box{}, err
	}
	overbar := polyline{{radicandX, 0}, {radicandX + int64(radicand.W), 0}}
	if err := addOverbar(&box, overbar, l.k.rule); err != nil {
		return Box{}, err
	}
	if err := place(&box, index, 0, l.k.supShift); err != nil {
		return Box{}, err
	}
	return box, place(&box, radicand, radicandX, 0)
}

func addOverbar(box *Box, span polyline, thickness int64) error {
	x, err := narrow(span[0][0])
	if err != nil {
		return err
	}
	w, err := narrow(span[1][0] - span[0][0])
	if err != nil {
		return err
	}
	h, err := narrow(thickness)
	if err != nil {
		return err
	}
	y, err := narrow(span[0][1])
	if err != nil {
		return err
	}
	box.Leaves = append(box.Leaves, Leaf{Kind: LeafRule, Rect: geom.Rect{X: x, Y: y, W: w, H: h}, Container: true})
	return nil
}

func pathLeaf(path polyline) (Leaf, error) {
	flat := make([]geom.Point, len(path))
	for i, p := range path {
		x, err := narrow(p[0])
		if err != nil {
			return Leaf{}, err
		}
		y, err := narrow(p[1])
		if err != nil {
			return Leaf{}, err
		}
		flat[i] = geom.Point{X: x, Y: y}
	}
	return Leaf{Kind: LeafPath, Rect: pointBounds(flat), Points: flat}, nil
}

func addPath(box *Box, path polyline) error {
	leaf, err := pathLeaf(path)
	box.Leaves = append(box.Leaves, leaf)
	return err
}

func addContainerPath(box *Box, path polyline) error {
	leaf, err := pathLeaf(path)
	leaf.Container = true
	box.Leaves = append(box.Leaves, leaf)
	return err
}

func pointBounds(points []geom.Point) geom.Rect {
	lowX, lowY := points[0].X, points[0].Y
	highX, highY := lowX, lowY
	for _, p := range points {
		lowX, highX = min(lowX, p.X), max(highX, p.X)
		lowY, highY = min(lowY, p.Y), max(highY, p.Y)
	}
	return geom.Rect{X: lowX, Y: lowY, W: highX - lowX, H: highY - lowY}
}

func (l *layouter) delimited(e *Expr, size int64) (Box, error) {
	body, err := l.box(e.Body, size)
	if err != nil {
		return Box{}, err
	}
	height := max(int64(body.A)+int64(body.D), l.em)
	left, err := l.delimiterBox(e.Left, height, body)
	if err != nil {
		return Box{}, err
	}
	right, err := l.delimiterBox(e.Right, height, body)
	if err != nil {
		return Box{}, err
	}
	ascent := max(body.A, left.A, right.A)
	descent := max(body.D, left.D, right.D)
	bodyX := int64(left.W)
	rightX := bodyX + int64(body.W)
	box, err := finish(rightX+int64(right.W), int64(ascent), int64(descent))
	if err != nil {
		return Box{}, err
	}
	if err := place(&box, left, 0, int64(ascent-left.A)); err != nil {
		return Box{}, err
	}
	if err := place(&box, body, bodyX, 0); err != nil {
		return Box{}, err
	}
	return box, place(&box, right, rightX, int64(ascent-right.A))
}

func (l *layouter) delimiterBox(d Delimiter, height int64, body Box) (Box, error) {
	if d == DelimInvisible {
		return Box{}, nil
	}
	extra := height - int64(body.A) - int64(body.D)
	ascent := int64(body.A) + roundHalfUp(extra, 2)
	box, err := finish(l.k.delimW, ascent, height-ascent)
	if err != nil {
		return Box{}, err
	}
	return box, addPath(&box, delimiterShape(d, l.k.delimW, height))
}

func delimiterShape(d Delimiter, w, h int64) polyline {
	wh, hh := w/2, h/2
	paren := quadratic([2]int64{w, 0}, [2]int64{0, hh}, [2]int64{w, h})
	brace := polyline{{w, 0}, {wh, 0}, {wh, hh}, {0, hh}, {wh, hh}, {wh, h}, {w, h}}
	switch d {
	case DelimLeftParen:
		return paren
	case DelimRightParen:
		return mirrored(paren, w)
	case DelimLeftBracket:
		return polyline{{w, 0}, {0, 0}, {0, h}, {w, h}}
	case DelimRightBracket:
		return polyline{{0, 0}, {w, 0}, {w, h}, {0, h}}
	case DelimLeftBrace:
		return brace
	case DelimRightBrace:
		return mirrored(brace, w)
	}
	return polyline{{wh, 0}, {wh, h}}
}

func mirrored(path polyline, w int64) polyline {
	out := make(polyline, len(path))
	for i, p := range path {
		out[i] = [2]int64{w - p[0], p[1]}
	}
	return out
}

func quadratic(p0, p1, p2 [2]int64) polyline {
	points := make(polyline, flattenSteps+1)
	for k := int64(0); k <= flattenSteps; k++ {
		inverse := flattenSteps - k
		for axis := range 2 {
			sum := inverse*inverse*p0[axis] + 2*k*inverse*p1[axis] + k*k*p2[axis]
			points[k][axis] = geom.FloorDiv(sum+flattenBias, flattenDenominator)
		}
	}
	return points
}
