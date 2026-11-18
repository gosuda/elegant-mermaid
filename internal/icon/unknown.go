package icon

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const (
	unknownUnitsPerEm = 2048
	opMove            = 0
	opLine            = 1
	opQuad            = 2
)

type glyphCommand struct {
	op             uint8
	x1, y1, x2, y2 int32
}

var unknownGlyph = [...]glyphCommand{
	{0, 383, 449, 0, 0},
	{1, 383, 460, 0, 0},
	{2, 383, 597, 409, 671},
	{2, 436, 746, 486, 789},
	{2, 536, 833, 605, 874},
	{2, 671, 914, 716, 975},
	{2, 761, 1037, 761, 1124},
	{2, 761, 1228, 690, 1289},
	{2, 619, 1351, 518, 1351},
	{2, 430, 1351, 355, 1295},
	{2, 280, 1240, 272, 1115},
	{1, 82, 1115, 0, 0},
	{2, 87, 1241, 146, 1329},
	{2, 206, 1417, 303, 1463},
	{2, 400, 1510, 518, 1510},
	{2, 648, 1510, 743, 1459},
	{2, 839, 1409, 892, 1320},
	{2, 945, 1231, 945, 1117},
	{2, 945, 996, 892, 910},
	{2, 839, 824, 742, 765},
	{2, 678, 726, 638, 689},
	{2, 599, 653, 581, 601},
	{2, 564, 549, 564, 460},
	{1, 564, 449, 0, 0},
	{1, 383, 449, 0, 0},
	{0, 476, -13, 0, 0},
	{2, 420, -13, 380, 26},
	{2, 341, 66, 341, 121},
	{2, 341, 177, 380, 216},
	{2, 420, 256, 476, 256},
	{2, 532, 256, 571, 216},
	{2, 610, 177, 610, 121},
	{2, 610, 66, 571, 26},
	{2, 532, -13, 476, -13},
}

type extent struct{ minX, minY, maxX, maxY int64 }

func scaleGlyph(v int64) int64 {
	return geom.FloorDiv(2*v*boxUnits+unknownUnitsPerEm, 2*unknownUnitsPerEm)
}

func glyphPoints(c glyphCommand) []point {
	points := []point{{scaleGlyph(int64(c.x1)), -scaleGlyph(int64(c.y1))}}
	if c.op == opQuad {
		points = append(points, point{scaleGlyph(int64(c.x2)), -scaleGlyph(int64(c.y2))})
	}
	return points
}

func glyphExtent() extent {
	e := extent{minX: 1 << 40, minY: 1 << 40, maxX: -1 << 40, maxY: -1 << 40}
	for _, c := range unknownGlyph {
		for _, p := range glyphPoints(c) {
			e.minX, e.maxX = min(e.minX, p.x), max(e.maxX, p.x)
			e.minY, e.maxY = min(e.minY, p.y), max(e.maxY, p.y)
		}
	}
	return e
}

func drawUnknownGlyph(at geom.Point) scene.Primitive {
	e := glyphExtent()
	shift := point{
		int64(at.X) + geom.FloorDiv(boxUnits-(e.maxX-e.minX), 2) - e.minX,
		int64(at.Y) + geom.FloorDiv(boxUnits-(e.maxY-e.minY), 2) - e.minY,
	}
	var out []scene.Command
	var cur point
	for _, c := range unknownGlyph {
		points := glyphPoints(c)
		for i := range points {
			points[i] = point{points[i].x + shift.x, points[i].y + shift.y}
		}
		out = append(out, glyphCommands(c.op, cur, points, len(out))...)
		cur = points[len(points)-1]
	}
	out = append(out, &scene.ClosePath{})
	return &scene.Path{Shape: scene.Shape{Style: "ink"}, Commands: out}
}

func glyphCommands(op uint8, cur point, points []point, emitted int) []scene.Command {
	var out []scene.Command
	if op == opMove && emitted > 0 {
		out = append(out, &scene.ClosePath{})
	}
	switch op {
	case opMove:
		out = append(out, &scene.MoveTo{P: unitPoint(points[0])})
	case opLine:
		out = append(out, &scene.LineTo{P: unitPoint(points[0])})
	default:
		out = append(out, quadToCubic(cur, points[0], points[1]))
	}
	return out
}

func unitPoint(p point) geom.Point { return geom.Point{X: int32(p.x), Y: int32(p.y)} }

func quadToCubic(from, control, to point) *scene.CubicTo {
	third := func(a, c int64) int64 { return geom.FloorDiv(2*(a+2*c)+3, 6) }
	return &scene.CubicTo{
		C1: geom.Point{X: int32(third(from.x, control.x)), Y: int32(third(from.y, control.y))},
		C2: geom.Point{X: int32(third(to.x, control.x)), Y: int32(third(to.y, control.y))},
		P:  unitPoint(to),
	}
}
