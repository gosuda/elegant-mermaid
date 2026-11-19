package layout

import (
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type laneFrame struct {
	id           string
	near, length int64
}

func laneFrames(axis laneAxis, bands []laneBand, s *scene.Scene) []laneFrame {
	frames := make([]laneFrame, 0, len(bands))
	for i := range bands {
		index := sceneBoxIndex(s, bands[i].id)
		if index < 0 {
			continue
		}
		rect := s.Boxes[index].Rect
		frames = append(frames, laneFrame{
			id:     bands[i].id,
			near:   int64(*axis.start(&rect)) + bands[i].shift - bands[i].start,
			length: int64(*axis.length(&rect)),
		})
	}
	return frames
}

func frameOf(frames []laneFrame, id string) (laneFrame, bool) {
	for _, frame := range frames {
		if frame.id == id {
			return frame, true
		}
	}
	return laneFrame{}, false
}

func attachEnd(s *scene.Scene, axis laneAxis, frames []laneFrame, id string, p geom.Point) (geom.Point, bool, error) {
	frame, ok := frameOf(frames, id)
	if !ok {
		return p, false, nil
	}
	index := sceneBoxIndex(s, id)
	if index < 0 {
		return p, false, nil
	}
	rect := s.Boxes[index].Rect
	start := int64(*axis.start(&rect))
	lo := start + frame.near
	hi := lo + frame.length
	switch cross := int64(*axis.point(&p)); cross {
	case hi:
		end, err := laneNarrow(start + int64(*axis.length(&rect)))
		if err != nil {
			return p, false, err
		}
		moved := p
		*axis.point(&moved) = end
		return moved, true, nil
	case lo:
		moved := p
		*axis.point(&moved) = int32(start)
		return moved, true, nil
	default:
		return p, false, nil
	}
}

func attachLaneEnds(s *scene.Scene, axis laneAxis, frames []laneFrame) error {
	for i := range s.Routes {
		route := &s.Routes[i]
		if len(route.Points) == 0 {
			continue
		}
		head, headMoved, err := attachEnd(s, axis, frames, route.From, route.Points[0])
		if err != nil {
			return err
		}
		tail, tailMoved, err := attachEnd(s, axis, frames, route.To, route.Points[len(route.Points)-1])
		if err != nil {
			return err
		}
		if !headMoved && !tailMoved {
			continue
		}
		raw := make([]geom.Point, 0, len(route.Points)+2)
		if headMoved {
			raw = append(raw, head)
		}
		raw = append(raw, route.Points...)
		if tailMoved {
			raw = append(raw, tail)
		}
		next := simplifyPolyline(raw)
		if slices.Equal(next, route.Points) {
			continue
		}
		previous := route.Points
		route.Points = next
		retargetEdgeItems(s, route.ID, previous, next)
	}
	return nil
}

func retargetEdgeItems(s *scene.Scene, owner string, previous, points []geom.Point) {
	for _, group := range s.Groups {
		if group.Role != scene.GroupRoleEdge || group.Owner != owner {
			continue
		}
		for _, item := range group.Items {
			switch shape := item.(type) {
			case *scene.Polyline:
				shape.Points = slices.Clone(points)
			case *scene.MarkerRef:
				switch {
				case shape.At == previous[0]:
					shape.At = points[0]
					neighbour := points[0]
					if len(points) > 1 {
						neighbour = points[1]
					}
					shape.Axis = layered.MarkerAxis(neighbour, points[0])
				case shape.At == previous[len(previous)-1]:
					shape.At = points[len(points)-1]
					neighbour := points[len(points)-1]
					if len(points) > 1 {
						neighbour = points[len(points)-2]
					}
					shape.Axis = layered.MarkerAxis(neighbour, points[len(points)-1])
				}
			}
		}
	}
}
