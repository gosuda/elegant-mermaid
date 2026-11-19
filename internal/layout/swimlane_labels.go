package layout

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type geometrySink struct {
	boxRect  func(start, end int64)
	itemRect func(start, end int64)
	value    func(int64)
}

func originSink(extent *laneExtent) geometrySink {
	return geometrySink{
		boxRect:  func(start, _ int64) { extent.extend(start) },
		itemRect: func(start, end int64) { extent.extend(start); extent.extend(end) },
		value:    extent.extend,
	}
}

func extentSink(extent *laneExtent) geometrySink {
	both := func(start, end int64) { extent.extend(start); extent.extend(end) }
	return geometrySink{boxRect: both, itemRect: both, value: extent.extend}
}

func walkGeometry(s *scene.Scene, axis laneAxis, sink geometrySink) {
	span := func(r geom.Rect) (int64, int64) {
		return int64(*axis.start(&r)), int64(*axis.start(&r)) + int64(*axis.length(&r))
	}
	for i := range s.Boxes {
		sink.boxRect(span(s.Boxes[i].Rect))
	}
	for i := range s.Routes {
		for j := range s.Routes[i].Points {
			sink.value(int64(*axis.point(&s.Routes[i].Points[j])))
		}
	}
	for i := range s.Labels {
		sink.boxRect(span(s.Labels[i].Rect))
	}
	for _, group := range s.Groups {
		for _, item := range group.Items {
			rects, values := primitiveCoordinates(item, axis)
			for _, r := range rects {
				sink.itemRect(span(*r))
			}
			for _, v := range values {
				sink.value(int64(*v))
			}
		}
	}
}

func geometryMax(s *scene.Scene, axis laneAxis) int64 {
	var extent laneExtent
	walkGeometry(s, axis, extentSink(&extent))
	return max(0, extent.hi)
}

func meetsInterior(outer, inner geom.Rect) bool {
	return max(int64(outer.X), int64(inner.X)) < min(int64(outer.X)+int64(outer.W), int64(inner.X)+int64(inner.W)) &&
		max(int64(outer.Y), int64(inner.Y)) < min(int64(outer.Y)+int64(outer.H), int64(inner.Y)+int64(inner.H))
}

func strictlyInside(outer, inner geom.Rect) bool {
	return int64(outer.X) < int64(inner.X) &&
		int64(inner.X)+int64(inner.W) < int64(outer.X)+int64(outer.W) &&
		int64(outer.Y) < int64(inner.Y) &&
		int64(inner.Y)+int64(inner.H) < int64(outer.Y)+int64(outer.H)
}

type labelScopes struct {
	parents map[string]string
	routes  map[string][2]string
}

func newLabelScopes(s *scene.Scene) *labelScopes {
	scopes := &labelScopes{parents: make(map[string]string, len(s.Boxes)), routes: make(map[string][2]string, len(s.Routes))}
	for i := range s.Boxes {
		scopes.parents[s.Boxes[i].ID] = s.Boxes[i].Parent
	}
	for i := range s.Routes {
		scopes.routes[s.Routes[i].ID] = [2]string{s.Routes[i].From, s.Routes[i].To}
	}
	return scopes
}

func (l *labelScopes) addAncestors(id string, into map[string]struct{}) {
	current, ok := l.parents[id]
	for ok {
		if _, seen := into[current]; seen {
			return
		}
		into[current] = struct{}{}
		current, ok = l.parents[current]
	}
}

func (l *labelScopes) ownerAncestors(label *scene.Label) map[string]struct{} {
	ancestors := map[string]struct{}{}
	ends, isRoute := l.routes[label.Owner]
	if !isRoute {
		l.addAncestors(label.Owner, ancestors)
		return ancestors
	}
	l.addAncestors(ends[0], ancestors)
	l.addAncestors(ends[1], ancestors)
	return ancestors
}

func overlapsForeignFrame(frame *scene.Box, label *scene.Label) bool {
	return frame.Role == scene.RoleGroup && meetsInterior(frame.Rect, label.Rect) && !strictlyInside(frame.Rect, label.Rect)
}

func hitsUnrelatedNode(node *scene.Box, label *scene.Label, ancestors map[string]struct{}) bool {
	if !node.Exclusive || node.ID == label.Owner {
		return false
	}
	if _, related := ancestors[node.ID]; related {
		return false
	}
	return meetsInterior(node.Rect, label.Rect)
}

func needsRelocation(s *scene.Scene, label *scene.Label, scopes *labelScopes) bool {
	ancestors := scopes.ownerAncestors(label)
	for i := range s.Boxes {
		if overlapsForeignFrame(&s.Boxes[i], label) || hitsUnrelatedNode(&s.Boxes[i], label, ancestors) {
			return true
		}
	}
	return false
}

func relocateLabels(s *scene.Scene, axis laneAxis, gap int64) error {
	sum, err := laneAdd(geometryMax(s, axis), gap)
	if err != nil {
		return err
	}
	strip, err := laneNarrow(sum)
	if err != nil {
		return err
	}
	moved := moveOffendingLabels(s, axis, strip)
	moveMatchingTexts(s, axis, strip, moved)
	return nil
}

func moveOffendingLabels(s *scene.Scene, axis laneAxis, strip int32) map[geom.Rect]struct{} {
	scopes := newLabelScopes(s)
	var offenders []int
	for i := range s.Labels {
		if needsRelocation(s, &s.Labels[i], scopes) {
			offenders = append(offenders, i)
		}
	}
	moved := make(map[geom.Rect]struct{}, len(offenders))
	for _, index := range offenders {
		label := &s.Labels[index]
		moved[label.Rect] = struct{}{}
		*axis.start(&label.Rect) = strip
	}
	return moved
}

func moveMatchingTexts(s *scene.Scene, axis laneAxis, strip int32, moved map[geom.Rect]struct{}) {
	for _, group := range s.Groups {
		for _, item := range group.Items {
			text, ok := item.(*scene.Text)
			if !ok {
				continue
			}
			if _, hit := moved[text.Rect]; hit {
				*axis.start(&text.Rect) = strip
			}
		}
	}
}
