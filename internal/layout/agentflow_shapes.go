package layout

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func layoutAgentflow(in Input) (scene.Scene, []diag.Diagnostic, error) {
	input := familyInput(in)
	options := resolveOptions(in.Options)
	options.Profile, options.Direction = in.Profile, in.Direction
	var budget bool
	s, err := layered.LayoutFamily(input, layered.Options{Scene: options, BudgetExhausted: &budget})
	if err != nil {
		return s, nil, err
	}
	s, err = agentflowShapeScene(in, s)
	if err != nil {
		return s, nil, err
	}
	var ds []diag.Diagnostic
	if budget {
		ds = append(ds, diag.Diagnostic{Code: "layout/budget-exhausted", Severity: diag.SeverityInfo, Message: "layout stopped at its iteration cap"})
	}
	diag.Sort(ds)
	return s, ds, err
}

func agentflowRaiseCollapsedLabel(profile scene.Profile, text *scene.Text) error {
	padding, err := agentflowConstant(profile, "padding")
	if err != nil {
		return err
	}
	text.Rect.Y -= (agentflowLineHeight(profile) + padding) / 2
	return nil
}

func agentflowDressGroup(in Input, s scene.Scene, group *scene.Group) error {
	node, bounds, ok := agentflowNodeBounds(in, s, group.Owner)
	if !ok {
		return nil
	}
	shapes, err := agentflowOutline(node.Shape, bounds, in.Profile)
	if err != nil {
		return err
	}
	for _, item := range group.Items {
		text, isText := item.(*scene.Text)
		if !isText {
			continue
		}
		if node.Shape == "collapsedGroup" {
			if err := agentflowRaiseCollapsedLabel(in.Profile, text); err != nil {
				return err
			}
		}
		shapes = append(shapes, text)
	}
	group.Items = shapes
	return nil
}

func agentflowShapeScene(in Input, s scene.Scene) (scene.Scene, error) {
	for _, group := range s.Groups {
		if err := agentflowDressGroup(in, s, group); err != nil {
			return s, err
		}
	}
	return s, nil
}

func agentflowNodeBounds(in Input, s scene.Scene, owner string) (Box, geom.Rect, bool) {
	for i := range in.Boxes {
		if in.Boxes[i].ID == owner && in.Boxes[i].Role == scene.RoleNode {
			for j := range s.Boxes {
				if s.Boxes[j].ID == owner {
					return in.Boxes[i], s.Boxes[j].Rect, true
				}
			}
		}
	}
	return Box{}, geom.Rect{}, false
}

func agentflowOutline(name string, rect geom.Rect, profile scene.Profile) ([]scene.Primitive, error) {
	shape := scene.Shape{Style: "node"}
	right := rect.X + rect.W
	bottom := rect.Y + rect.H
	centre := geom.Point{X: rect.X + rect.W/2, Y: rect.Y + rect.H/2}
	polygon := func(points []geom.Point) []scene.Primitive {
		return []scene.Primitive{&scene.Polygon{Shape: shape, Points: points}}
	}
	point := func(x, y int32) geom.Point { return geom.Point{X: x, Y: y} }
	switch name {
	case "diamond":
		return polygon([]geom.Point{point(centre.X, rect.Y), point(right, centre.Y), point(centre.X, bottom), point(rect.X, centre.Y)}), nil
	case "hexagon", "hex":
		inset := min(rect.H/4, rect.W/4)
		return polygon([]geom.Point{
			point(rect.X+inset, rect.Y), point(right-inset, rect.Y), point(right, centre.Y),
			point(right-inset, bottom), point(rect.X+inset, bottom), point(rect.X, centre.Y),
		}), nil
	case "lean-right":
		inset := min(rect.H/2, rect.W/3)
		return polygon([]geom.Point{
			point(rect.X+inset, rect.Y), point(right, rect.Y),
			point(right-inset, bottom), point(rect.X, bottom),
		}), nil
	case "subroutine", "subprocess", "subproc", "framed-rectangle":
		return agentflowFramed(rect, profile)
	case "lin-doc", "lined-document":
		return agentflowDocumentOutline(rect)
	case "connector":
		return []scene.Primitive{&scene.Ellipse{Shape: shape, CX: centre.X, CY: centre.Y, RX: rect.W / 2, RY: rect.H / 2}}, nil
	default:
		return agentflowRoundedOutline(name, rect, profile)
	}
}

func agentflowFramed(rect geom.Rect, profile scene.Profile) ([]scene.Primitive, error) {
	padding, err := agentflowConstant(profile, "padding")
	if err != nil {
		return nil, err
	}
	inset := min(padding, rect.W/3)
	right, bottom := rect.X+rect.W, rect.Y+rect.H
	items := []scene.Primitive{&scene.Rect{Shape: scene.Shape{Style: "node"}, Rect: rect}}
	for _, x := range []int32{rect.X + inset, right - inset} {
		items = append(items, &scene.Polyline{
			Shape:  scene.Shape{Style: "rule"},
			Points: []geom.Point{{X: x, Y: rect.Y}, {X: x, Y: bottom}},
		})
	}
	return items, nil
}

func agentflowDocumentOutline(rect geom.Rect) ([]scene.Primitive, error) {
	right, bottom := rect.X+rect.W, rect.Y+rect.H
	amplitude := rect.H / 8
	baseline := bottom - amplitude
	points := []geom.Point{{X: rect.X, Y: rect.Y}, {X: rect.X, Y: baseline}}
	for index := range int64(33) {
		x, err := agentflowCheckedI32(int64(rect.X) + geom.FloorDiv(int64(rect.W)*index, 32))
		if err != nil {
			return nil, err
		}
		y, err := agentflowCheckedI32(int64(baseline) + geom.FloorDiv(int64(amplitude)*int64(geom.SinQ15(int32(index*2048))), 32768))
		if err != nil {
			return nil, err
		}
		points = append(points, geom.Point{X: x, Y: y})
	}
	points = append(points, geom.Point{X: right, Y: rect.Y})
	lineX := rect.X + rect.W/22
	return []scene.Primitive{
		&scene.Polygon{Shape: scene.Shape{Style: "node"}, Points: points},
		&scene.Polyline{Shape: scene.Shape{Style: "rule"}, Points: []geom.Point{{X: lineX, Y: rect.Y}, {X: lineX, Y: baseline}}},
	}, nil
}

func agentflowCornerRadius(profile scene.Profile) (int32, error) {
	key := profile.String() + ".corner_radius"
	for i := range gen.LayoutConst {
		if gen.LayoutConst[i].Name == key {
			return gen.LayoutConst[i].Value, nil
		}
	}
	return 0, geom.ErrDomain
}

func agentflowRoundedOutline(name string, rect geom.Rect, profile scene.Profile) ([]scene.Primitive, error) {
	radius, err := agentflowCornerRadius(profile)
	if err != nil {
		return nil, err
	}
	style := "node"
	if name == "collapsedGroup" {
		style = "group"
	}
	items := []scene.Primitive{&scene.RoundRect{Shape: scene.Shape{Style: style}, Rect: rect, R: radius}}
	if name != "collapsedGroup" {
		return items, nil
	}
	indicator, err := agentflowCollapsedIndicator(rect, profile)
	if err != nil {
		return nil, err
	}
	return append(items, indicator...), nil
}

func agentflowCollapsedIndicator(rect geom.Rect, profile scene.Profile) ([]scene.Primitive, error) {
	padding, err := agentflowConstant(profile, "padding")
	if err != nil {
		return nil, err
	}
	right, bottom := rect.X+rect.W, rect.Y+rect.H
	lineHeight := agentflowLineHeight(profile)
	y := bottom - padding - 2*lineHeight
	items := []scene.Primitive{&scene.Polyline{
		Shape:  scene.Shape{Style: "rule", Line: scene.LineDotted},
		Points: []geom.Point{{X: rect.X + padding, Y: y}, {X: right - padding, Y: y}},
	}}
	centre := rect.X + rect.W/2
	for _, offset := range []int32{-padding, 0, padding} {
		cy := y + lineHeight
		if profile == scene.ProfileCell {
			items = append(items, &scene.SymbolRef{Symbol: "disc", At: geom.Point{X: centre + offset, Y: cy}, Style: "ink"})
			continue
		}
		radius := padding * 5 / 16
		items = append(items, &scene.Ellipse{Shape: scene.Shape{Style: "ink"}, CX: centre + offset, CY: cy, RX: radius, RY: radius})
	}
	return items, nil
}
