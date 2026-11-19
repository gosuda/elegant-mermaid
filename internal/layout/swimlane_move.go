package layout

import (
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type laneAxis uint8

const (
	laneAxisX laneAxis = iota
	laneAxisY
)

func crossAxis(direction scene.Direction) laneAxis {
	if direction == scene.DirectionLR || direction == scene.DirectionRL {
		return laneAxisY
	}
	return laneAxisX
}

func (a laneAxis) point(p *geom.Point) *int32 {
	if a == laneAxisX {
		return &p.X
	}
	return &p.Y
}

func (a laneAxis) start(r *geom.Rect) *int32 {
	if a == laneAxisX {
		return &r.X
	}
	return &r.Y
}

func (a laneAxis) length(r *geom.Rect) *int32 {
	if a == laneAxisX {
		return &r.W
	}
	return &r.H
}

func (a laneAxis) size(s *geom.Size) *int32 {
	if a == laneAxisX {
		return &s.W
	}
	return &s.H
}

type laneBoxDelta struct {
	id    string
	delta int64
}

type laneRouteDelta struct {
	id          string
	from, to    int64
	first, last int32
}

type lanePin struct {
	axis   laneAxis
	boxes  []laneBoxDelta
	routes []laneRouteDelta
}

func (p *lanePin) boxDelta(id string) int64 {
	for i := range p.boxes {
		if p.boxes[i].id == id {
			return p.boxes[i].delta
		}
	}
	return 0
}

func (p *lanePin) route(id string) (laneRouteDelta, bool) {
	for i := range p.routes {
		if p.routes[i].id == id {
			return p.routes[i], true
		}
	}
	return laneRouteDelta{}, false
}

func (p *lanePin) labelDelta(owner string) int64 {
	route, ok := p.route(owner)
	if !ok {
		return p.boxDelta(owner)
	}
	if route.from == route.to {
		return route.from
	}
	return 0
}

type laneMove struct {
	axis  laneAxis
	delta int64
	ends  *laneRouteDelta
}

func constantMove(axis laneAxis, delta int64) laneMove {
	return laneMove{axis: axis, delta: delta}
}

func routeMove(axis laneAxis, route laneRouteDelta) laneMove {
	if route.from == route.to {
		return constantMove(axis, route.from)
	}
	return laneMove{axis: axis, ends: &route}
}

func (m laneMove) offset(value int32) int64 {
	if m.ends == nil {
		return m.delta
	}
	switch value {
	case m.ends.first:
		return m.ends.from
	case m.ends.last:
		return m.ends.to
	}
	return 0
}

func (m laneMove) apply(value *int32) error {
	sum, err := laneAdd(int64(*value), m.offset(*value))
	if err != nil {
		return err
	}
	if *value, err = laneNarrow(sum); err != nil {
		return err
	}
	return nil
}

func (m laneMove) rect(r *geom.Rect) error {
	return m.apply(m.axis.start(r))
}

func (m laneMove) points(points []geom.Point) error {
	for i := range points {
		if err := m.apply(m.axis.point(&points[i])); err != nil {
			return err
		}
	}
	return nil
}

func (m laneMove) primitive(p scene.Primitive) error {
	rects, values := primitiveCoordinates(p, m.axis)
	for _, r := range rects {
		if err := m.rect(r); err != nil {
			return err
		}
	}
	for _, v := range values {
		if err := m.apply(v); err != nil {
			return err
		}
	}
	return nil
}

func primitiveCoordinates(p scene.Primitive, axis laneAxis) (rects []*geom.Rect, values []*int32) {
	switch shape := p.(type) {
	case *scene.Rect:
		rects = append(rects, &shape.Rect)
	case *scene.RoundRect:
		rects = append(rects, &shape.Rect)
	case *scene.Text:
		rects = append(rects, &shape.Rect)
	case *scene.Ellipse:
		values = append(values, ellipseCentre(shape, axis))
	case *scene.Polygon:
		values = pointValues(shape.Points, axis)
	case *scene.Polyline:
		values = pointValues(shape.Points, axis)
	case *scene.Path:
		values = commandValues(shape.Commands, axis)
	case *scene.MarkerRef:
		values = append(values, axis.point(&shape.At))
	case *scene.SymbolRef:
		values = append(values, axis.point(&shape.At))
	}
	return rects, values
}

func ellipseCentre(shape *scene.Ellipse, axis laneAxis) *int32 {
	if axis == laneAxisX {
		return &shape.CX
	}
	return &shape.CY
}

func pointValues(points []geom.Point, axis laneAxis) []*int32 {
	values := make([]*int32, len(points))
	for i := range points {
		values[i] = axis.point(&points[i])
	}
	return values
}

func commandValues(commands []scene.Command, axis laneAxis) []*int32 {
	var values []*int32
	for _, command := range commands {
		switch c := command.(type) {
		case *scene.MoveTo:
			values = append(values, axis.point(&c.P))
		case *scene.LineTo:
			values = append(values, axis.point(&c.P))
		case *scene.CubicTo:
			values = append(values, axis.point(&c.C1), axis.point(&c.C2), axis.point(&c.P))
		case *scene.ArcTo:
			values = append(values, arcCentre(c, axis))
		}
	}
	return values
}

func arcCentre(c *scene.ArcTo, axis laneAxis) *int32 {
	if axis == laneAxisX {
		return &c.CX
	}
	return &c.CY
}

func buildLanePin(axis laneAxis, bands []laneBand, s *scene.Scene) lanePin {
	pin := lanePin{axis: axis}
	for i := range bands {
		pin.boxes = append(pin.boxes, laneBoxDelta{bands[i].id, bands[i].shift})
		for _, member := range bands[i].members {
			pin.boxes = append(pin.boxes, laneBoxDelta{member, bands[i].shift})
		}
	}
	for i := range s.Routes {
		route := &s.Routes[i]
		if len(route.Points) == 0 {
			continue
		}
		pin.routes = append(pin.routes, laneRouteDelta{
			id:    route.ID,
			from:  bandDelta(bands, route.From),
			to:    bandDelta(bands, route.To),
			first: *axis.point(&route.Points[0]),
			last:  *axis.point(&route.Points[len(route.Points)-1]),
		})
	}
	return pin
}

func bandDelta(bands []laneBand, id string) int64 {
	for i := range bands {
		if bands[i].id == id {
			return bands[i].shift
		}
		for _, member := range bands[i].members {
			if member == id {
				return bands[i].shift
			}
		}
	}
	return 0
}

func applyLanePin(s *scene.Scene, pin *lanePin, bands []laneBand) error {
	if err := moveDump(s, pin); err != nil {
		return err
	}
	for _, group := range s.Groups {
		if err := moveGroup(group, pin); err != nil {
			return err
		}
	}
	for i := range bands {
		if err := replaceFrame(s, &bands[i], pin.axis); err != nil {
			return err
		}
	}
	return nil
}

func moveDump(s *scene.Scene, pin *lanePin) error {
	for i := range s.Boxes {
		if err := constantMove(pin.axis, pin.boxDelta(s.Boxes[i].ID)).rect(&s.Boxes[i].Rect); err != nil {
			return err
		}
	}
	for i := range s.Labels {
		if err := constantMove(pin.axis, pin.labelDelta(s.Labels[i].Owner)).rect(&s.Labels[i].Rect); err != nil {
			return err
		}
	}
	for i := range s.Routes {
		route, ok := pin.route(s.Routes[i].ID)
		if !ok {
			continue
		}
		if err := routeMove(pin.axis, route).points(s.Routes[i].Points); err != nil {
			return err
		}
	}
	return nil
}

func moveGroup(group *scene.Group, pin *lanePin) error {
	move := constantMove(pin.axis, pin.boxDelta(group.Owner))
	if group.Role == scene.GroupRoleEdge {
		route, _ := pin.route(group.Owner)
		move = routeMove(pin.axis, route)
	}
	for _, item := range group.Items {
		if err := move.primitive(item); err != nil {
			return err
		}
	}
	return nil
}

func replaceFrame(s *scene.Scene, band *laneBand, axis laneAxis) error {
	index := sceneBoxIndex(s, band.id)
	if index < 0 {
		return nil
	}
	start, err := laneNarrow(band.start)
	if err != nil {
		return err
	}
	thickness, err := laneNarrow(band.thickness)
	if err != nil {
		return err
	}
	place := func(r *geom.Rect) {
		*axis.start(r), *axis.length(r) = start, thickness
	}
	place(&s.Boxes[index].Rect)
	for _, group := range s.Groups {
		if group.Owner != band.id {
			continue
		}
		for _, item := range group.Items {
			if frame, ok := item.(*scene.Rect); ok {
				place(&frame.Rect)
			}
		}
		return nil
	}
	return nil
}

func shiftCrossAxis(s *scene.Scene, axis laneAxis, delta int64) error {
	move := constantMove(axis, delta)
	for i := range s.Boxes {
		if err := move.rect(&s.Boxes[i].Rect); err != nil {
			return err
		}
	}
	for i := range s.Labels {
		if err := move.rect(&s.Labels[i].Rect); err != nil {
			return err
		}
	}
	for i := range s.Routes {
		if err := move.points(s.Routes[i].Points); err != nil {
			return err
		}
	}
	for _, group := range s.Groups {
		for _, item := range group.Items {
			if err := move.primitive(item); err != nil {
				return err
			}
		}
	}
	return nil
}

func detachGeometry(s *scene.Scene) {
	for i := range s.Routes {
		s.Routes[i].Points = slices.Clone(s.Routes[i].Points)
	}
	groups := make([]*scene.Group, len(s.Groups))
	for i, group := range s.Groups {
		detached := *group
		detached.Items = make([]scene.Primitive, len(group.Items))
		for j, item := range group.Items {
			detached.Items[j] = clonePrimitive(item)
		}
		groups[i] = &detached
	}
	s.Groups = groups
}

func copyOf[T any](value *T) *T {
	clone := *value
	return &clone
}

func clonePrimitive(p scene.Primitive) scene.Primitive {
	switch shape := p.(type) {
	case *scene.Polygon:
		clone := copyOf(shape)
		clone.Points = slices.Clone(shape.Points)
		return clone
	case *scene.Polyline:
		clone := copyOf(shape)
		clone.Points = slices.Clone(shape.Points)
		return clone
	case *scene.Path:
		clone := copyOf(shape)
		clone.Commands = make([]scene.Command, len(shape.Commands))
		for i, command := range shape.Commands {
			clone.Commands[i] = cloneCommand(command)
		}
		return clone
	}
	return clonePlain(p)
}

func clonePlain(p scene.Primitive) scene.Primitive {
	switch shape := p.(type) {
	case *scene.Rect:
		return copyOf(shape)
	case *scene.RoundRect:
		return copyOf(shape)
	case *scene.Ellipse:
		return copyOf(shape)
	case *scene.Text:
		return copyOf(shape)
	case *scene.MarkerRef:
		return copyOf(shape)
	case *scene.SymbolRef:
		return copyOf(shape)
	}
	return p
}

func cloneCommand(command scene.Command) scene.Command {
	switch c := command.(type) {
	case *scene.MoveTo:
		return copyOf(c)
	case *scene.LineTo:
		return copyOf(c)
	case *scene.CubicTo:
		return copyOf(c)
	case *scene.ArcTo:
		return copyOf(c)
	}
	return command
}
