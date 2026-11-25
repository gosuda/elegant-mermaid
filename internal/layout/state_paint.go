package layout

import (
	"errors"
	"math"

	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

var errStateDomain = errors.New("state layout: invalid geometry")

func paintState(in Input, s *scene.Scene) error {
	for _, group := range s.Groups {
		if group.Role != scene.GroupRoleNode {
			continue
		}
		node := stateNode(in.Boxes, group.Owner)
		if node == nil || !isStateSymbol(node.Shape) {
			continue
		}
		bounds, ok := stateBoxRect(s, group.Owner)
		if !ok {
			return errStateDomain
		}
		if node.Shape == "note" {
			group.Items = noteItems(group.Items, bounds)
			continue
		}
		items, err := symbolItems(node.Shape, bounds, in.Profile)
		if err != nil {
			return err
		}
		group.Items = items
	}
	return paintRegions(in, s)
}

func stateNode(boxes []Box, id string) *Box {
	for i := range boxes {
		if boxes[i].ID == id {
			return &boxes[i]
		}
	}
	return nil
}

func isStateSymbol(shape string) bool {
	switch shape {
	case "sm-circ", "fr-circ", "fork", "choice", "note":
		return true
	}
	return false
}

func stateBoxRect(s *scene.Scene, id string) (geom.Rect, bool) {
	for _, box := range s.Boxes {
		if box.ID == id {
			return box.Rect, true
		}
	}
	return geom.Rect{}, false
}

func noteItems(existing []scene.Primitive, bounds geom.Rect) []scene.Primitive {
	items := []scene.Primitive{&scene.Rect{Shape: scene.Shape{Style: "note"}, Rect: bounds}}
	for _, item := range existing {
		if text, ok := item.(*scene.Text); ok {
			items = append(items, text)
		}
	}
	return items
}

func stateCoordinate(value int64) (int32, error) {
	if value < math.MinInt32 || value > math.MaxInt32 {
		return 0, geom.ErrOverflow
	}
	return int32(value), nil
}

func layoutConstant(profile scene.Profile, name string) (int32, bool) {
	key := profile.String() + "." + name
	for _, c := range gen.LayoutConst {
		if c.Name == key {
			return c.Value, true
		}
	}
	return 0, false
}

func symbolItems(shape string, rect geom.Rect, profile scene.Profile) ([]scene.Primitive, error) {
	if rect.W <= 0 || rect.H <= 0 {
		return nil, errStateDomain
	}
	if profile == scene.ProfileCell && shape != "fork" {
		return cellSymbol(shape, rect)
	}
	centre := geom.Point{X: rect.X + rect.W/2, Y: rect.Y + rect.H/2}
	switch shape {
	case "fork":
		return []scene.Primitive{&scene.Rect{Shape: scene.Shape{Style: "ink"}, Rect: rect}}, nil
	case "choice":
		return diamondItems(rect, centre)
	case "sm-circ", "fr-circ":
		return circleItems(shape, rect, centre)
	}
	return nil, errStateDomain
}

func diamondItems(rect geom.Rect, centre geom.Point) ([]scene.Primitive, error) {
	right, err := stateCoordinate(int64(rect.X) + int64(rect.W))
	if err != nil {
		return nil, err
	}
	bottom, err := stateCoordinate(int64(rect.Y) + int64(rect.H))
	if err != nil {
		return nil, err
	}
	points := []geom.Point{{X: centre.X, Y: rect.Y}, {X: right, Y: centre.Y}, {X: centre.X, Y: bottom}, {X: rect.X, Y: centre.Y}}
	return []scene.Primitive{&scene.Polygon{Shape: scene.Shape{Style: "node"}, Points: points}}, nil
}

func cellSymbol(shape string, rect geom.Rect) ([]scene.Primitive, error) {
	names := map[string][2]string{"sm-circ": {"disc", "ink"}, "fr-circ": {"bullseye", "ink"}, "choice": {"diamond-hollow", "node"}}
	pair, ok := names[shape]
	if !ok {
		return nil, errStateDomain
	}
	return []scene.Primitive{&scene.SymbolRef{Symbol: pair[0], At: geom.Point{X: rect.X, Y: rect.Y}, Style: pair[1]}}, nil
}

func circleItems(shape string, rect geom.Rect, centre geom.Point) ([]scene.Primitive, error) {
	outer := "ink"
	if shape == "fr-circ" {
		outer = "ink-line"
	}
	items := []scene.Primitive{&scene.Ellipse{Shape: scene.Shape{Style: outer}, CX: centre.X, CY: centre.Y, RX: rect.W / 2, RY: rect.H / 2}}
	if shape != "fr-circ" {
		return items, nil
	}
	diameter, ok := layoutConstant(scene.ProfileVector, "state.end_inner_size")
	if !ok || diameter <= 0 || diameter > rect.W || diameter > rect.H {
		return nil, errStateDomain
	}
	return append(items, &scene.Ellipse{Shape: scene.Shape{Style: "ink"}, CX: centre.X, CY: centre.Y, RX: diameter / 2, RY: diameter / 2}), nil
}

func paintRegions(in Input, s *scene.Scene) error {
	if len(in.RegionSets) == 0 {
		return nil
	}
	inset, ok := layoutConstant(in.Profile, "cluster_pad")
	if !ok {
		return errStateDomain
	}
	for _, set := range in.RegionSets {
		if err := paintRegionSet(in, s, set, inset); err != nil {
			return err
		}
	}
	return nil
}

func paintRegionSet(in Input, s *scene.Scene, set layered.RegionSet, inset int32) error {
	parentRect, err := regionRect(in, s, set.Parent)
	if err != nil {
		return err
	}
	for _, region := range set.Regions {
		group, err := regionGroup(in, s, region)
		if err != nil {
			return err
		}
		group.Items = nil
	}
	parent, err := regionGroup(in, s, set.Parent)
	if err != nil {
		return err
	}
	dividers := make([]scene.Primitive, 0, len(set.Regions))
	for i := 0; i+1 < len(set.Regions); i++ {
		divider, err := regionDivider(in, s, regionPair{parent: parentRect, a: set.Regions[i], b: set.Regions[i+1]}, inset)
		if err != nil {
			return err
		}
		dividers = append(dividers, divider)
	}
	insertion := len(parent.Items)
	for i, item := range parent.Items {
		if !isShapePrimitive(item) {
			insertion = i
			break
		}
	}
	items := make([]scene.Primitive, 0, len(parent.Items)+len(dividers))
	items = append(items, parent.Items[:insertion]...)
	items = append(items, dividers...)
	items = append(items, parent.Items[insertion:]...)
	parent.Items = items
	return nil
}

type regionPair struct {
	parent geom.Rect
	a, b   int
}

func regionDivider(in Input, s *scene.Scene, pair regionPair, inset int32) (scene.Primitive, error) {
	a, err := regionRect(in, s, pair.a)
	if err != nil {
		return nil, err
	}
	b, err := regionRect(in, s, pair.b)
	if err != nil {
		return nil, err
	}
	points, err := regionSeparator(pair.parent, a, b, inset)
	if err != nil {
		return nil, err
	}
	return &scene.Polyline{Shape: scene.Shape{Style: "rule", Line: scene.LineDashed}, Points: points[:]}, nil
}

func regionGroup(in Input, s *scene.Scene, index int) (*scene.Group, error) {
	if index < 0 || index >= len(in.Groups) {
		return nil, errStateDomain
	}
	for _, group := range s.Groups {
		if group.Role == scene.GroupRoleGroup && group.Owner == in.Groups[index].ID {
			return group, nil
		}
	}
	return nil, errStateDomain
}

func isShapePrimitive(item scene.Primitive) bool {
	switch item.(type) {
	case *scene.Rect, *scene.RoundRect, *scene.Ellipse, *scene.Polygon, *scene.Polyline, *scene.Path:
		return true
	}
	return false
}

func regionRect(in Input, s *scene.Scene, index int) (geom.Rect, error) {
	if index < 0 || index >= len(in.Groups) {
		return geom.Rect{}, errStateDomain
	}
	rect, ok := stateBoxRect(s, in.Groups[index].ID)
	if !ok {
		return geom.Rect{}, errStateDomain
	}
	return rect, nil
}

type regionBounds struct{ left, top, right, bottom int32 }

func insetRegionBounds(parent geom.Rect, inset int32) (regionBounds, error) {
	var out regionBounds
	for _, edge := range []struct {
		dst   *int32
		value int64
	}{
		{&out.left, int64(parent.X) + int64(inset)},
		{&out.top, int64(parent.Y) + int64(inset)},
		{&out.right, int64(parent.X) + int64(parent.W) - int64(inset)},
		{&out.bottom, int64(parent.Y) + int64(parent.H) - int64(inset)},
	} {
		v, err := stateCoordinate(edge.value)
		if err != nil {
			return regionBounds{}, err
		}
		*edge.dst = v
	}
	return out, nil
}

func positiveExtent(r geom.Rect) bool { return r.W > 0 && r.H > 0 }

func regionSeparatorUsable(bounds regionBounds, inset int32, a, b geom.Rect) bool {
	return inset >= 0 && bounds.left <= bounds.right && bounds.top <= bounds.bottom && positiveExtent(a) && positiveExtent(b)
}

func regionBodyBounds(parent, a, b geom.Rect, inset int32) (regionBounds, error) {
	outer, err := insetRegionBounds(parent, inset)
	if err != nil {
		return regionBounds{}, err
	}
	first, err := insetRegionBounds(a, 0)
	if err != nil {
		return regionBounds{}, err
	}
	second, err := insetRegionBounds(b, 0)
	if err != nil {
		return regionBounds{}, err
	}
	return regionBounds{
		left:   max(outer.left, min(first.left, second.left)),
		top:    max(outer.top, min(first.top, second.top)),
		right:  min(outer.right, max(first.right, second.right)),
		bottom: min(outer.bottom, max(first.bottom, second.bottom)),
	}, nil
}

func regionSeparator(parent, a, b geom.Rect, inset int32) ([2]geom.Point, error) {
	bounds, err := regionBodyBounds(parent, a, b, inset)
	if err != nil {
		return [2]geom.Point{}, err
	}
	if !regionSeparatorUsable(bounds, inset, a, b) {
		return [2]geom.Point{}, errStateDomain
	}
	x, found, err := regionGap(a.X, a.W, b.X, b.W)
	if err != nil {
		return [2]geom.Point{}, err
	}
	if found {
		return bounds.verticalSeparator(x)
	}
	y, found, err := regionGap(a.Y, a.H, b.Y, b.H)
	if err != nil {
		return [2]geom.Point{}, err
	}
	if found {
		return bounds.horizontalSeparator(y)
	}
	return [2]geom.Point{}, errStateDomain
}

func (bounds regionBounds) verticalSeparator(x int32) ([2]geom.Point, error) {
	if x < bounds.left || x > bounds.right {
		return [2]geom.Point{}, errStateDomain
	}
	return [2]geom.Point{{X: x, Y: bounds.top}, {X: x, Y: bounds.bottom}}, nil
}

func (bounds regionBounds) horizontalSeparator(y int32) ([2]geom.Point, error) {
	if y < bounds.top || y > bounds.bottom {
		return [2]geom.Point{}, errStateDomain
	}
	return [2]geom.Point{{X: bounds.left, Y: y}, {X: bounds.right, Y: y}}, nil
}

func regionGap(aStart, aSize, bStart, bSize int32) (int32, bool, error) {
	aEnd, err := stateCoordinate(int64(aStart) + int64(aSize))
	if err != nil {
		return 0, false, err
	}
	bEnd, err := stateCoordinate(int64(bStart) + int64(bSize))
	if err != nil {
		return 0, false, err
	}
	switch {
	case aEnd <= bStart:
		mid, err := stateCoordinate(geom.FloorDiv(int64(aEnd)+int64(bStart), 2))
		return mid, true, err
	case bEnd <= aStart:
		mid, err := stateCoordinate(geom.FloorDiv(int64(bEnd)+int64(aStart), 2))
		return mid, true, err
	}
	return 0, false, nil
}
