package layered

import (
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func groupText(in Input, id string) string {
	for i, b := range in.Boxes {
		if b.ID == id {
			return inputBoxText(in, i)
		}
	}
	return id
}

type fixedContents struct {
	scene   scene.Scene
	packing packingReservations
}

func frameSubgraph(in Input, id string, contents fixedContents, o scene.Options) (FixedGroup, error) {
	s := contents.scene
	titles, err := unorientedTitles(s)
	if err != nil {
		return FixedGroup{}, err
	}
	lines, err := wrapLabel(groupText(in, id), in.Kind, o)
	if err != nil {
		return FixedGroup{}, err
	}
	titleSize, err := measuredTitle(lines, o)
	if err != nil {
		return FixedGroup{}, err
	}
	unorientScene(&s)
	pad := constant(o.Profile, "cluster_pad")
	w, err := coordinate(max(int64(s.Canvas.W), int64(titleSize.W)) + 2*int64(pad))
	if err != nil {
		return FixedGroup{}, err
	}
	h, err := coordinate(int64(s.Canvas.H) + int64(titleSize.H) + 2*int64(pad))
	if err != nil {
		return FixedGroup{}, err
	}
	if err := shiftScene(&s, int64(pad), int64(titleSize.H)+int64(pad)); err != nil {
		return FixedGroup{}, err
	}
	title := geom.Rect{X: (w - titleSize.W) / 2, Y: pad, W: titleSize.W, H: titleSize.H}
	s.Canvas = geom.Size{W: w, H: h}
	s.Options.Direction = o.Direction
	title = orientRect(title, o.Direction, h)
	orientScene(&s)
	transform := frameTransform{dx: int64(pad), dy: int64(titleSize.H) + int64(pad), direction: o.Direction, height: h}
	packing, err := framePacking(contents.packing, transform)
	if err != nil {
		return FixedGroup{}, err
	}
	titles, err = transform.boxes(titles)
	if err != nil {
		return FixedGroup{}, err
	}
	return FixedGroup{ID: id, Scene: s, W: s.Canvas.W, H: s.Canvas.H, Title: title, Titles: titles, packing: packing}, nil
}

func unorientScene(s *scene.Scene) {
	direction := s.Options.Direction
	switch direction {
	case scene.DirectionBT:
		s.Options.Direction = scene.DirectionBT
		orientScene(s)
	case scene.DirectionLR:
		s.Options.Direction = scene.DirectionLR
		orientScene(s)
	case scene.DirectionRL:
		s.Options.Direction = scene.DirectionLR
		orientScene(s)
		s.Options.Direction = scene.DirectionBT
		orientScene(s)
	}
	s.Options.Direction = direction
}

func inverseRect(r geom.Rect, d scene.Direction, w, h int32) geom.Rect {
	switch d {
	case scene.DirectionBT:
		return orientRect(r, d, h)
	case scene.DirectionLR:
		return orientRect(r, d, h)
	case scene.DirectionRL:
		r = orientRect(r, scene.DirectionLR, h)
		return orientRect(r, scene.DirectionBT, w)
	}
	return r
}

func cloneSceneDump(s scene.Scene) scene.Scene {
	s.Boxes = slices.Clone(s.Boxes)
	s.Labels = slices.Clone(s.Labels)
	s.Routes = slices.Clone(s.Routes)
	for i := range s.Routes {
		s.Routes[i].Points = slices.Clone(s.Routes[i].Points)
	}
	return s
}

func expandComponentFixed(g *Graph, part *Layout) error {
	for _, f := range g.Fixed {
		box := findBox(part.Boxes, f.ID)
		child := cloneSceneDump(f.Scene)
		child.Options.Direction = g.Direction
		title := inverseRect(f.Title, g.Direction, f.W, f.H)
		unorientScene(&child)
		if err := shiftScene(&child, int64(box.X), int64(box.Y)); err != nil {
			return err
		}
		rootTitle := Box{ID: f.ID, Rect: title}
		if err := translateBox(&rootTitle, int64(box.X), int64(box.Y)); err != nil {
			return err
		}
		part.Titles = append(part.Titles, rootTitle)
		inner := Layout{}
		appendFixedGeometry(&inner, child)
		if err := embedPacking(&inner, f, g.Direction, box); err != nil {
			return err
		}
		area, err := itemArea(inner)
		if err != nil {
			return err
		}
		part.fixedArea += area
		mergeFixedInner(part, inner)
	}
	return nil
}

func mergeFixedInner(part *Layout, inner Layout) {
	part.Boxes = append(part.Boxes, inner.Boxes...)
	part.Routes = append(part.Routes, inner.Routes...)
	part.Labels = append(part.Labels, inner.Labels...)
	part.Titles = append(part.Titles, inner.Titles...)
	part.Extents = append(part.Extents, inner.Extents...)
	part.LabelReservations = append(part.LabelReservations, inner.LabelReservations...)
}

func appendFixedGeometry(part *Layout, s scene.Scene) {
	for _, b := range s.Boxes {
		part.Boxes = append(part.Boxes, Box{ID: b.ID, Rect: b.Rect, Role: b.Role})
	}
	for _, r := range s.Routes {
		part.Routes = append(part.Routes, EdgeRoute{ID: r.ID, Original: -1, Points: r.Points})
	}
	for _, l := range s.Labels {
		if !sceneGroupOwner(s, l.Owner) {
			part.Labels = append(part.Labels, Box{ID: l.ID, Rect: l.Rect})
		}
	}
}

func sceneGroupOwner(s scene.Scene, id string) bool {
	for _, b := range s.Boxes {
		if b.ID == id {
			return b.Role == scene.RoleGroup
		}
	}
	return false
}

type frameTransform struct {
	dx, dy    int64
	direction scene.Direction
	height    int32
}

func (t frameTransform) boxes(boxes []Box) ([]Box, error) {
	for i := range boxes {
		if err := translateBox(&boxes[i], t.dx, t.dy); err != nil {
			return nil, err
		}
		boxes[i].Rect = orientRect(boxes[i].Rect, t.direction, t.height)
	}
	return boxes, nil
}

func framePacking(packing packingReservations, t frameTransform) (packingReservations, error) {
	loops, err := t.boxes(packing.loops)
	if err != nil {
		return packingReservations{}, err
	}
	labels, err := t.reservations(packing.labels)
	if err != nil {
		return packingReservations{}, err
	}
	return packingReservations{loops: loops, labels: labels}, nil
}

func embedBoxes(boxes []Box, f FixedGroup, d scene.Direction, at geom.Rect) ([]Box, error) {
	out := slices.Clone(boxes)
	for i := range out {
		out[i].Rect = inverseRect(out[i].Rect, d, f.W, f.H)
		if err := translateBox(&out[i], int64(at.X), int64(at.Y)); err != nil {
			return nil, err
		}
	}
	return out, nil
}

func embedPacking(part *Layout, f FixedGroup, d scene.Direction, at geom.Rect) error {
	loops, err := embedBoxes(f.packing.loops, f, d, at)
	if err != nil {
		return err
	}
	labels, err := embedReservations(f.packing.labels, f, d, at)
	if err != nil {
		return err
	}
	titles, err := embedBoxes(f.Titles, f, d, at)
	if err != nil {
		return err
	}
	part.Titles = append(part.Titles, titles...)
	part.Extents = append(part.Extents, loops...)
	part.LabelReservations = append(part.LabelReservations, labels...)
	return nil
}

func (t frameTransform) reservations(source []LabelReservation) ([]LabelReservation, error) {
	for i := range source {
		rect, err := rectangle(int64(source[i].Rect.X)+t.dx, int64(source[i].Rect.Y)+t.dy, int64(source[i].Rect.W), int64(source[i].Rect.H))
		if err != nil {
			return nil, err
		}
		source[i].Rect = orientRect(rect, t.direction, t.height)
	}
	return source, nil
}

func embedReservations(source []LabelReservation, f FixedGroup, d scene.Direction, at geom.Rect) ([]LabelReservation, error) {
	out := slices.Clone(source)
	for i := range out {
		rect := inverseRect(out[i].Rect, d, f.W, f.H)
		translated, err := rectangle(int64(rect.X)+int64(at.X), int64(rect.Y)+int64(at.Y), int64(rect.W), int64(rect.H))
		if err != nil {
			return nil, err
		}
		out[i].Rect = translated
	}
	return out, nil
}
