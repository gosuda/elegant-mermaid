package layered

import (
	"math"

	"github.com/gosuda/elegant-mermaid/internal/geom"
)

type layoutBoundary struct {
	rect geom.Rect
	have bool
}

func (bound *layoutBoundary) add(rect geom.Rect) error {
	if !bound.have {
		checked, err := rectangle(int64(rect.X), int64(rect.Y), int64(rect.W), int64(rect.H))
		if err != nil {
			return err
		}
		bound.rect = checked
		bound.have = true
		return nil
	}
	next, err := geom.Union(bound.rect, rect)
	bound.rect = next
	return err
}
func (bound *layoutBoundary) boxes(boxes []Box) error {
	for _, box := range boxes {
		if err := bound.add(box.Rect); err != nil {
			return err
		}
	}
	return nil
}
func (bound *layoutBoundary) routes(routes []EdgeRoute) error {
	for _, route := range routes {
		for _, point := range route.Points {
			if err := bound.add(geom.Rect{X: point.X, Y: point.Y}); err != nil {
				return err
			}
		}
	}
	return nil
}
func layoutBounds(part Layout) (geom.Rect, error) {
	var bound layoutBoundary
	for _, boxes := range [4][]Box{part.Boxes, part.Labels, part.Extents, part.Titles} {
		if err := bound.boxes(boxes); err != nil {
			return bound.rect, err
		}
	}
	for _, reserved := range part.LabelReservations {
		if err := bound.add(reserved.Rect); err != nil {
			return bound.rect, err
		}
	}
	if err := bound.routes(part.Routes); err != nil {
		return bound.rect, err
	}
	return bound.rect, nil
}

type packingArea struct{ total int64 }

func (area *packingArea) rectangle(rect geom.Rect) error {
	if rect.W < 0 || rect.H < 0 {
		return ErrGraph
	}
	value := int64(rect.W) * int64(rect.H)
	if area.total > math.MaxInt64-value {
		return geom.ErrOverflow
	}
	area.total += value
	return nil
}
func (area *packingArea) boxes(boxes []Box) error {
	for _, box := range boxes {
		if err := area.rectangle(box.Rect); err != nil {
			return err
		}
	}
	return nil
}
func (area *packingArea) labels(part Layout) error {
	reserved := make(map[string]struct{})
	for _, envelope := range part.LabelReservations {
		if envelope.Label == nil {
			return ErrGraph
		}
		if err := area.rectangle(envelope.Rect); err != nil {
			return err
		}
		for _, item := range envelope.Label.Items {
			reserved[item.ID] = struct{}{}
		}
	}
	for _, label := range part.Labels {
		if _, covered := reserved[label.ID]; covered {
			continue
		}
		if err := area.rectangle(label.Rect); err != nil {
			return err
		}
	}
	return nil
}
func (area *packingArea) routes(routes []EdgeRoute) error {
	for _, route := range routes {
		bounds, err := layoutBounds(Layout{Routes: []EdgeRoute{route}})
		if err != nil {
			return err
		}
		if err := area.rectangle(bounds); err != nil {
			return err
		}
	}
	return nil
}
func itemArea(part Layout) (int64, error) {
	var area packingArea
	for _, boxes := range [3][]Box{part.Boxes, part.Extents, part.Titles} {
		if err := area.boxes(boxes); err != nil {
			return 0, err
		}
	}
	if err := area.labels(part); err != nil {
		return 0, err
	}
	if err := area.routes(part.Routes); err != nil {
		return 0, err
	}
	return area.total, nil
}
func packingTarget(parts []Layout, opts PackOptions) (int64, error) {
	if opts.MaxWidth > 0 {
		return int64(opts.MaxWidth), nil
	}
	if opts.AspectNum <= 0 || opts.AspectDen <= 0 {
		return 0, ErrGraph
	}
	var area int64
	for _, part := range parts {
		value, err := itemArea(part)
		if err != nil {
			return 0, err
		}
		if area > math.MaxInt64-value {
			return 0, geom.ErrOverflow
		}
		area += value
	}
	if area > math.MaxInt64/int64(opts.AspectNum) {
		return 0, geom.ErrOverflow
	}
	aspect, err := geom.Isqrt(area * int64(opts.AspectNum) / int64(opts.AspectDen))
	if err != nil || len(parts) < 2 {
		return aspect, err
	}
	return minAreaTarget(parts, int64(opts.Gap), aspect)
}

type shelf struct {
	gap, target, x, y, rowHeight, width int64
	items                               int
}

func (s *shelf) place(w, h int64) (int64, int64) {
	if s.items > 0 && s.x+w > s.target {
		s.x = 0
		s.y += s.rowHeight + s.gap
		s.rowHeight = 0
		s.items = 0
	}
	x, y := s.x, s.y
	s.x += w + s.gap
	s.width = max(s.width, x+w)
	s.rowHeight = max(s.rowHeight, h)
	s.items++
	return x, y
}
func (s *shelf) area() (int64, error) {
	height := s.y + s.rowHeight
	if s.width != 0 && height > math.MaxInt64/s.width {
		return 0, geom.ErrOverflow
	}
	return s.width * height, nil
}
func shelfArea(sizes []geom.Size, gap, target int64) (int64, error) {
	s := shelf{gap: gap, target: target}
	for _, size := range sizes {
		s.place(int64(size.W), int64(size.H))
	}
	return s.area()
}
func minAreaTarget(parts []Layout, gap, aspect int64) (int64, error) {
	sizes := make([]geom.Size, len(parts))
	for i, part := range parts {
		bounds, err := layoutBounds(part)
		if err != nil {
			return 0, err
		}
		sizes[i] = geom.Size{W: bounds.W, H: bounds.H}
	}
	best := aspect
	bestArea, err := shelfArea(sizes, gap, aspect)
	if err != nil {
		return 0, err
	}
	prefix := -gap
	for _, size := range sizes {
		prefix += int64(size.W) + gap
		area, err := shelfArea(sizes, gap, prefix)
		if err != nil {
			return 0, err
		}
		if area < bestArea {
			best, bestArea = prefix, area
		}
	}
	return best, nil
}
func Pack(parts []Layout, opts PackOptions) (Layout, error) {
	if opts.MaxWidth < 0 || opts.Gap < 0 {
		return Layout{}, ErrGraph
	}
	target, err := packingTarget(parts, opts)
	if err != nil {
		return Layout{}, err
	}
	var out Layout
	sh := shelf{gap: int64(opts.Gap), target: target}
	for _, part := range parts {
		bounds, err := layoutBounds(part)
		if err != nil {
			return out, err
		}
		x, y := sh.place(int64(bounds.W), int64(bounds.H))
		if err := translateLayout(&part, x-int64(bounds.X), y-int64(bounds.Y)); err != nil {
			return out, err
		}
		out.Boxes = append(out.Boxes, part.Boxes...)
		out.Routes = append(out.Routes, part.Routes...)
		out.Labels = append(out.Labels, part.Labels...)
		out.Extents = append(out.Extents, part.Extents...)
		out.Titles = append(out.Titles, part.Titles...)
		out.LabelReservations = append(out.LabelReservations, part.LabelReservations...)
		out.BudgetExhausted = out.BudgetExhausted || part.BudgetExhausted
	}
	bounds, err := layoutBounds(out)
	out.Width = bounds.W
	out.Height = bounds.H
	return out, err
}
func translateLayout(part *Layout, dx, dy int64) error {
	for _, boxes := range [4][]Box{part.Boxes, part.Labels, part.Extents, part.Titles} {
		if err := translateBoxes(boxes, dx, dy); err != nil {
			return err
		}
	}
	if err := translateReservations(part.LabelReservations, dx, dy); err != nil {
		return err
	}
	for _, route := range part.Routes {
		if err := translatePoints(route.Points, dx, dy); err != nil {
			return err
		}
	}
	return nil
}
func translateBox(box *Box, dx, dy int64) error {
	rect, err := rectangle(int64(box.Rect.X)+dx, int64(box.Rect.Y)+dy, int64(box.Rect.W), int64(box.Rect.H))
	if err != nil {
		return err
	}
	box.Rect = rect
	return nil
}
func translateBoxes(boxes []Box, dx, dy int64) error {
	for i := range boxes {
		if err := translateBox(&boxes[i], dx, dy); err != nil {
			return err
		}
	}
	return nil
}
func translateReservations(reservations []LabelReservation, dx, dy int64) error {
	for i := range reservations {
		rect := reservations[i].Rect
		translated, err := rectangle(int64(rect.X)+dx, int64(rect.Y)+dy, int64(rect.W), int64(rect.H))
		if err != nil {
			return err
		}
		reservations[i].Rect = translated
	}
	return nil
}
func translatePoints(points []geom.Point, dx, dy int64) error {
	for i := range points {
		x, err := coordinate(int64(points[i].X) + dx)
		if err != nil {
			return err
		}
		y, err := coordinate(int64(points[i].Y) + dy)
		if err != nil {
			return err
		}
		points[i].X = x
		points[i].Y = y
	}
	return nil
}
