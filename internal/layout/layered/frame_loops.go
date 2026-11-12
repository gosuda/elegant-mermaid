package layered

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func frameLoopGraph(g *Graph, id string, box Box) (*Graph, []int32) {
	frame := &Graph{Nodes: []Node{{ID: id, W: box.Rect.W, H: box.Rect.H}}, Params: g.Params}
	var indices []int32
	for i, e := range g.Edges {
		if e.FrameLoop != id {
			continue
		}
		e.Tail = 0
		e.Head = 0
		e.FrameLoop = ""
		frame.Edges = append(frame.Edges, e)
		indices = append(indices, int32(i))
	}
	return frame, indices
}
func sizeFrameLoops(g *Graph) error {
	for i := range g.Clusters {
		c := &g.Clusters[i]
		frame, _ := frameLoopGraph(g, c.ID, Box{})
		if err := sizeLoops(frame); err != nil {
			return err
		}
		c.Extent = frame.Nodes[0].Extent
		c.LoopHeight = frame.Nodes[0].H
	}
	for i, n := range g.Nodes {
		if n.Role != scene.RoleGroup || n.Border != BorderNone {
			continue
		}
		frame, _ := frameLoopGraph(g, n.ID, Box{Rect: geom.Rect{W: n.W, H: n.H}})
		if err := sizeLoops(frame); err != nil {
			return err
		}
		g.Nodes[i].H = frame.Nodes[0].H
		g.Nodes[i].Extent = frame.Nodes[0].Extent
	}
	return nil
}
func componentFrameLoops(g *Graph, part *Layout) error {
	for _, box := range part.Boxes {
		frame, indices := frameLoopGraph(g, box.ID, box)
		if len(indices) == 0 {
			continue
		}
		if err := sizeLoops(frame); err != nil {
			return err
		}
		loops, err := Loops(frame, []Box{box})
		if err != nil {
			return err
		}
		for _, route := range loops {
			part.Routes[indices[route.Original]] = route
		}
		labels, err := loopLabels(frame, []Box{box})
		if err != nil {
			return err
		}
		part.Labels = append(part.Labels, labels.boxes...)
		part.LabelReservations = append(part.LabelReservations, labels.reservations...)
		extents, err := loopExtents(frame, []Box{box})
		if err != nil {
			return err
		}
		part.Extents = append(part.Extents, extents...)
	}
	return nil
}
