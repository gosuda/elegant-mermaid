package layout

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const (
	cloudBumps    = 8
	cloudBase     = 27525
	cloudControl  = 35062
	bangSpikes    = 8
	bangInner     = 20316
	unitQ15       = 32768
	turnQ16       = 65536
	polarQ30Shift = 30
)

func (p *mindmapPlan) groups(dump scene.Dump) []*scene.Group {
	groups := make([]*scene.Group, 0, len(dump.Routes)+len(dump.Boxes))
	for _, route := range dump.Routes {
		line := &scene.Polyline{Shape: scene.Shape{Style: "edge"}, Corner: p.c.corner, Points: route.Points}
		groups = append(groups, &scene.Group{Role: scene.GroupRoleEdge, Owner: route.ID, Items: []scene.Primitive{line}})
	}
	for i, box := range dump.Boxes {
		items := p.shape(p.in.Boxes[i].Shape, box.Rect)
		items = append(items, p.text(box.Rect, p.lines[i]))
		groups = append(groups, &scene.Group{Role: scene.GroupRoleNode, Owner: box.ID, Items: items})
	}
	return groups
}

func (p *mindmapPlan) text(rect geom.Rect, lines []measure.StyledLine) *scene.Text {
	height := int32(len(lines)) * p.c.lineHeight
	box := geom.Rect{X: rect.X, Y: rect.Y + int32(geom.FloorDiv(int64(rect.H-height), 2)), W: rect.W, H: height}
	runs := make([][]scene.Run, len(lines))
	for i, line := range lines {
		runs[i] = make([]scene.Run, len(line.Runs))
		for j, run := range line.Runs {
			runs[i][j] = scene.Run{Text: run.Text, Bold: run.Bold, Italic: run.Italic}
		}
	}
	return &scene.Text{Rect: box, Role: scene.TextRoleLabel, Size: 14, Align: scene.AlignMiddle, Style: "text", Lines: runs}
}

func (p *mindmapPlan) shape(name string, rect geom.Rect) []scene.Primitive {
	if p.in.Profile == scene.ProfileCell {
		return mindmapCellShape(name, rect)
	}
	return p.mindmapVectorShape(name, rect)
}

func mindmapCellShape(name string, rect geom.Rect) []scene.Primitive {
	node := scene.Shape{Style: "node"}
	switch name {
	case "defaultMindmapNode":
		return nil
	case "rounded", "mindmapCircle":
		return []scene.Primitive{&scene.RoundRect{Shape: node, Rect: rect}}
	case "cloud":
		node.Line = scene.LineDotted
		return []scene.Primitive{&scene.RoundRect{Shape: node, Rect: rect}}
	case "bang":
		node.Line = scene.LineDouble
	case "hexagon":
		node.Width = scene.Width{Kind: scene.WidthEmphasis}
	}
	return []scene.Primitive{&scene.Rect{Shape: node, Rect: rect}}
}

func (p *mindmapPlan) mindmapVectorShape(name string, rect geom.Rect) []scene.Primitive {
	node := scene.Shape{Style: "node"}
	centre := geom.Point{X: rect.X + rect.W/2, Y: rect.Y + rect.H/2}
	switch name {
	case "defaultMindmapNode":
		return []scene.Primitive{&scene.RoundRect{Shape: scene.Shape{Style: "band"}, Rect: rect, R: p.c.corner}}
	case "rounded":
		return []scene.Primitive{&scene.RoundRect{Shape: node, Rect: rect, R: p.c.corner}}
	case "mindmapCircle":
		return []scene.Primitive{&scene.Ellipse{Shape: node, CX: centre.X, CY: centre.Y, RX: rect.W / 2, RY: rect.H / 2}}
	case "hexagon":
		return []scene.Primitive{&scene.Polygon{Shape: node, Points: hexagonPoints(rect, centre)}}
	case "bang":
		return []scene.Primitive{&scene.Polygon{Shape: node, Points: bangPoints(rect, centre)}}
	case "cloud":
		return []scene.Primitive{&scene.Path{Shape: node, Commands: cloudCommands(rect, centre)}}
	}
	return []scene.Primitive{&scene.Rect{Shape: node, Rect: rect}}
}

func hexagonPoints(rect geom.Rect, centre geom.Point) []geom.Point {
	inset := min(rect.H/4, rect.W/4)
	right, bottom := rect.X+rect.W, rect.Y+rect.H
	return []geom.Point{
		{X: rect.X + inset, Y: rect.Y}, {X: right - inset, Y: rect.Y}, {X: right, Y: centre.Y},
		{X: right - inset, Y: bottom}, {X: rect.X + inset, Y: bottom}, {X: rect.X, Y: centre.Y},
	}
}

func polar(rect geom.Rect, centre geom.Point, angle int32, factor int64) geom.Point {
	rx, ry := int64(rect.W/2), int64(rect.H/2)
	dx := geom.FloorDiv(rx*int64(geom.CosQ15(angle))*factor, 1<<polarQ30Shift)
	dy := geom.FloorDiv(ry*int64(geom.SinQ15(angle))*factor, 1<<polarQ30Shift)
	return geom.Point{X: centre.X + int32(dx), Y: centre.Y + int32(dy)}
}

func bangPoints(rect geom.Rect, centre geom.Point) []geom.Point {
	points := make([]geom.Point, 0, 2*bangSpikes)
	for k := range 2 * bangSpikes {
		factor := int64(unitQ15)
		if k%2 == 1 {
			factor = bangInner
		}
		points = append(points, polar(rect, centre, int32(k*turnQ16/(2*bangSpikes)), factor))
	}
	return points
}

func cloudCommands(rect geom.Rect, centre geom.Point) []scene.Command {
	step := int32(turnQ16 / cloudBumps)
	commands := []scene.Command{&scene.MoveTo{P: polar(rect, centre, 0, cloudBase)}}
	for k := range int32(cloudBumps) {
		from := k * step
		commands = append(commands, &scene.CubicTo{
			C1: polar(rect, centre, from+step/3, cloudControl),
			C2: polar(rect, centre, from+2*step/3, cloudControl),
			P:  polar(rect, centre, from+step, cloudBase),
		})
	}
	return append(commands, &scene.ClosePath{})
}
