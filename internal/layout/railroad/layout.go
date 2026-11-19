package railroad

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const kindName = "railroad"

type layouter struct {
	p      Params
	k      Constants
	dump   scene.Dump
	groups []*scene.Group
	edges  []*scene.Group
	nodes  []*scene.Group
}

func Layout(rules []Rule, p Params) (scene.Scene, error) {
	l := &layouter{p: p, k: p.Constants, dump: scene.Dump{Kind: kindName, Options: p.Options}}
	if len(rules) == 0 {
		return l.finish(l.k.EmptyWidth, l.k.EmptyHeight)
	}
	y, widest := l.k.Margin, int64(0)
	for _, rule := range rules {
		height, width, err := l.placeRule(rule, l.k.Margin, y)
		if err != nil {
			return scene.Scene{}, err
		}
		y += height + l.k.Vsep
		widest = max(widest, width)
	}
	return l.finish(widest+2*l.k.Margin, y+l.k.Margin)
}

func (l *layouter) finish(width, height int64) (scene.Scene, error) {
	w, err := fit(width)
	if err != nil {
		return scene.Scene{}, err
	}
	h, err := fit(height)
	if err != nil {
		return scene.Scene{}, err
	}
	l.dump.Canvas = geom.Size{W: w, H: h}
	groups := append(append(l.groups, l.edges...), l.nodes...)
	return scene.Scene{Dump: l.dump, Groups: groups}, nil
}

type ruleGeometry struct {
	title, nameW, defX, baseline, defY int64
	width, height                      int64
}

func (l *layouter) ruleGeometry(rule Rule, root *shape) (ruleGeometry, error) {
	c := l.k
	title, err := l.p.Metric.TextWidth(rule.Title)
	if err != nil {
		return ruleGeometry{}, err
	}
	g := ruleGeometry{title: int64(title)}
	g.nameW = g.title + c.RuleNameGap
	g.defX = g.nameW + c.RuleNameGap
	g.baseline = max(c.RuleMinBaseline, root.up)
	g.defY = g.baseline - root.up
	g.width = g.defX + root.w + c.RuleEndGap + c.MarkerRadius
	g.height = max(c.RuleMinHeight, g.defY+root.height()+2*c.Margin)
	return g, nil
}

func (l *layouter) placeRule(rule Rule, x, y int64) (height, width int64, err error) {
	if rule.Root == nil {
		return 0, 0, ErrArity
	}
	root, err := l.measure(rule.Root)
	if err != nil {
		return 0, 0, err
	}
	g, err := l.ruleGeometry(rule, root)
	if err != nil {
		return 0, 0, err
	}
	if _, err = fit(x + g.width + l.k.Margin); err != nil {
		return 0, 0, err
	}
	if _, err = fit(y + g.height); err != nil {
		return 0, 0, err
	}
	if rule.ID != "" {
		l.dump.Boxes = append(l.dump.Boxes, scene.Box{ID: rule.ID, Role: scene.RoleGroup, Rect: rectOf(x-l.k.Margin, y, g.width+2*l.k.Margin, g.height)})
		l.groups = append(l.groups, &scene.Group{Role: scene.GroupRoleGroup, Owner: rule.ID, Items: l.ruleItems(rule, root, g, x, y)})
	}
	l.placeNode(root, x+g.defX, y+g.defY, rule.ID)
	return g.height, g.width, nil
}

func rectOf(x, y, w, h int64) geom.Rect {
	return geom.Rect{X: int32(x), Y: int32(y), W: int32(w), H: int32(h)}
}

func pointOf(p point) geom.Point { return geom.Point{X: int32(p.x), Y: int32(p.y)} }

func (l *layouter) textItem(rect geom.Rect, text string, align scene.Align) *scene.Text {
	return &scene.Text{Rect: rect, Role: scene.TextRoleLabel, Size: 14, Align: align, Style: "text", Lines: [][]scene.Run{{{Text: text}}}}
}

func (l *layouter) ruleItems(rule Rule, root *shape, g ruleGeometry, x, y int64) []scene.Primitive {
	c := l.k
	base := y + g.baseline
	defRight := x + g.defX + root.w
	items := []scene.Primitive{
		l.rail([]point{{x + g.nameW + c.MarkerRadius, base}, {x + g.defX, base}}),
		l.rail([]point{{l.rightStart(root, defRight), base}, {defRight + c.RuleEndGap - c.MarkerRadius, base}}),
		l.marker(x+g.nameW, base),
		l.marker(defRight+c.RuleEndGap, base),
	}
	label := rectOf(x, base-geom.FloorDiv(c.LineHeight, 2), g.title, c.LineHeight)
	l.dump.Labels = append(l.dump.Labels, scene.Label{ID: rule.ID + ".label", Owner: rule.ID, Text: rule.Title, Rect: label, Lines: []string{rule.Title}})
	return append(items, l.textItem(label, rule.Title, scene.AlignStart))
}

func (l *layouter) marker(cx, cy int64) scene.Primitive {
	r := int32(l.k.MarkerRadius)
	return &scene.Ellipse{Shape: scene.Shape{Style: "ink"}, CX: int32(cx), CY: int32(cy), RX: r, RY: r}
}

func (l *layouter) placeNode(s *shape, x, y int64, parent string) {
	n := s.node
	rect := rectOf(x, y, s.w, s.height())
	leaf := n.Kind.leaf()
	role := scene.RoleGroup
	if leaf {
		role = scene.RoleNode
	}
	l.dump.Boxes = append(l.dump.Boxes, scene.Box{ID: n.ID, Role: role, Rect: rect, Parent: parent, Exclusive: leaf})
	if leaf {
		l.nodes = append(l.nodes, &scene.Group{Role: scene.GroupRoleNode, Owner: n.ID, Items: l.leafItems(n, rect)})
		return
	}
	l.groups = append(l.groups, &scene.Group{Role: scene.GroupRoleGroup, Owner: n.ID, Items: l.rails(s, x, y)})
	if n.Kind == KindSequence {
		l.joins(s, x, y)
	}
	for i, kid := range s.kids {
		l.placeNode(kid, x+s.offsets[i].x, y+s.offsets[i].y, n.ID)
	}
}

func (l *layouter) leafItems(n *Node, rect geom.Rect) []scene.Primitive {
	shape := scene.Shape{Style: "node"}
	var outline scene.Primitive
	switch n.Kind {
	case KindTerminal:
		outline = &scene.RoundRect{Shape: shape, Rect: rect, R: int32(l.k.TerminalRadius)}
	case KindSpecial:
		shape.Line = scene.LineDashed
		outline = &scene.Rect{Shape: shape, Rect: rect}
	default:
		outline = &scene.Rect{Shape: shape, Rect: rect}
	}
	line := int32(l.k.LineHeight)
	text := geom.Rect{X: rect.X, Y: rect.Y + (rect.H-line)/2, W: rect.W, H: line}
	return []scene.Primitive{outline, l.textItem(text, n.Text, scene.AlignMiddle)}
}

func (l *layouter) joins(s *shape, x, y int64) {
	line := y + s.up
	for i := 0; i+1 < len(s.kids); i++ {
		from, to := s.kids[i], s.kids[i+1]
		start := point{x + s.offsets[i].x + from.w, line}
		end := point{x + s.offsets[i+1].x, line}
		id := RouteID(len(l.dump.Routes))
		points := []geom.Point{pointOf(start), pointOf(end)}
		l.dump.Routes = append(l.dump.Routes, scene.Route{ID: id, From: from.node.ID, To: to.node.ID, Orthogonal: true, Points: points, Stroke: "normal"})
		l.edges = append(l.edges, &scene.Group{Role: scene.GroupRoleEdge, Owner: id, Items: []scene.Primitive{&scene.Polyline{Shape: scene.Shape{Style: "edge"}, Points: points}}})
	}
}
