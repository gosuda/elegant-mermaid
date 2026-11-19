package layered

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type attachmentFootprint struct {
	size   geom.Size
	target geom.Rect
	notes  []geom.Rect
}

type attachmentNoteSize struct {
	size geom.Size
	side AttachmentSide
}

type footprintInput struct {
	target    geom.Size
	notes     []attachmentNoteSize
	direction scene.Direction
	gap       int32
}

func attachmentFootprintOf(in footprintInput) (attachmentFootprint, error) {
	target := orientedSize(in.target, in.direction)
	notes := make([]geom.Size, len(in.notes))
	left, right := int64(in.gap), int64(in.gap)
	height := target.H
	for i, note := range in.notes {
		notes[i] = orientedSize(note.size, in.direction)
		extent := int64(notes[i].W) + int64(in.gap)
		if note.side == AttachLeft {
			left += extent
		} else {
			right += extent
		}
		height = max(height, notes[i].H)
	}
	width, err := coordinate(left + int64(target.W) + right)
	if err != nil {
		return attachmentFootprint{}, err
	}
	total, err := coordinate(int64(height) + 2*int64(in.gap))
	if err != nil {
		return attachmentFootprint{}, err
	}
	x, err := coordinate(left)
	if err != nil {
		return attachmentFootprint{}, err
	}
	extent := geom.Size{W: width, H: total}
	placed := geom.Rect{X: x, Y: (total - target.H) / 2, W: target.W, H: target.H}
	rects, err := placeFootprintNotes(in, notes, placed, extent)
	if err != nil {
		return attachmentFootprint{}, err
	}
	return attachmentFootprint{
		size:   orientedSize(extent, in.direction),
		target: inverseFootprintRect(placed, extent, in.direction),
		notes:  rects,
	}, nil
}

func placeFootprintNotes(in footprintInput, notes []geom.Size, target geom.Rect, extent geom.Size) ([]geom.Rect, error) {
	left := int64(in.gap)
	right := int64(target.X) + int64(target.W) + int64(in.gap)
	rects := make([]geom.Rect, 0, len(notes))
	for i, size := range notes {
		cursor := &right
		if in.notes[i].side == AttachLeft {
			cursor = &left
		}
		x, err := coordinate(*cursor)
		if err != nil {
			return nil, err
		}
		rect := geom.Rect{X: x, Y: (extent.H - size.H) / 2, W: size.W, H: size.H}
		*cursor += int64(size.W) + int64(in.gap)
		rects = append(rects, inverseFootprintRect(rect, extent, in.direction))
	}
	return rects, nil
}

func orientedSize(size geom.Size, direction scene.Direction) geom.Size {
	if direction == scene.DirectionLR || direction == scene.DirectionRL {
		return geom.Size{W: size.H, H: size.W}
	}
	return size
}

func inverseFootprintRect(rect geom.Rect, extent geom.Size, direction scene.Direction) geom.Rect {
	switch direction {
	case scene.DirectionBT:
		rect.Y = extent.H - rect.Y - rect.H
		return rect
	case scene.DirectionLR:
		return geom.Rect{X: rect.Y, Y: rect.X, W: rect.H, H: rect.W}
	case scene.DirectionRL:
		return geom.Rect{X: rect.Y, Y: extent.W - rect.X - rect.W, W: rect.H, H: rect.W}
	}
	return rect
}

func translatedRect(rect geom.Rect, offset geom.Point) (geom.Rect, error) {
	x, err := coordinate(int64(rect.X) + int64(offset.X))
	if err != nil {
		return geom.Rect{}, err
	}
	y, err := coordinate(int64(rect.Y) + int64(offset.Y))
	if err != nil {
		return geom.Rect{}, err
	}
	rect.X, rect.Y = x, y
	return rect, nil
}
