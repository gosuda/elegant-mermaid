package layered

import "github.com/gosuda/elegant-mermaid/internal/geom"

func AddLabelNodes(p *Proper) error {
	if p == nil || len(p.Original) != len(p.Chains) {
		return ErrGraph
	}
	for i, e := range p.Original {
		if e.Label == nil || e.SelfLoop() || e.Synthetic {
			continue
		}
		chain := p.Chains[i]
		if len(chain) < 3 {
			return ErrRanking
		}
		v := chain[(len(chain)-1)/2]
		width, err := coordinate(int64(e.Label.W) + int64(p.LabelGutter))
		if err != nil {
			return err
		}
		p.Nodes[v].W = width
		p.Nodes[v].H = e.Label.H
		p.Nodes[v].Label = e.Label
	}
	return nil
}

type labelPlacement struct {
	boxes        []Box
	reservations []LabelReservation
}

func placedLabels(p *Proper, x, y []int32) (labelPlacement, error) {
	var out labelPlacement
	for i, node := range p.Nodes {
		if node.Label == nil || p.Original[node.Edge].Reversed {
			continue
		}
		reserved, err := rectangle(int64(x[i])-int64(node.W)/2, int64(y[i]), int64(node.W), int64(node.H))
		if err != nil {
			return out, err
		}
		actual, err := rectangle(int64(reserved.X)+int64(p.LabelGutter), int64(reserved.Y), int64(node.Label.W), int64(node.Label.H))
		if err != nil {
			return out, err
		}
		if err := out.stack(node.Label, actual, reserved, p.Slot); err != nil {
			return out, err
		}
	}
	return out, nil
}
func commonParent(p *Proper, a, b int32) string {
	parent := p.Nodes[a].Parent
	for fuel := len(p.Clusters) + 1; parent != "" && fuel > 0; fuel-- {
		if insideCluster(p.Clusters, p.Nodes[b].Parent, parent) {
			return parent
		}
		parent = parentOf(p.Clusters, parent)
	}
	return ""
}
func addOrderingBorders(p *Proper) error {
	for _, c := range p.Clusters {
		if c.Top < 0 || c.Bottom < 0 {
			return ErrGraph
		}
		if err := addTitleReservation(p, c); err != nil {
			return err
		}
		addClusterOrderingBorders(p, c)
	}
	return nil
}
func addClusterOrderingBorders(p *Proper, c Cluster) {
	previous := [2]int32{-1, -1}
	for r := p.Rank[c.Top]; r <= p.Rank[c.Bottom]; r++ {
		for side, border := range []Border{BorderLeft, BorderRight} {
			v := int32(len(p.Nodes))
			p.Nodes = append(p.Nodes, ProperNode{Node: Node{Decl: c.Decl, W: p.ClusterBorder, Parent: c.ID, Border: border}, Edge: -1})
			if border == BorderRight {
				p.Nodes[v].Extent = c.Extent
			}
			p.Rank = append(p.Rank, r)
			if previous[side] >= 0 {
				p.Edges = append(p.Edges, ProperEdge{Tail: previous[side], Head: v, Decl: c.Decl, Original: -1})
			}
			previous[side] = v
		}
	}
}

func addTitleReservation(p *Proper, c Cluster) error {
	width := c.TitleSize.W
	h, err := coordinate(int64(c.TitleSize.H) + int64(p.ClusterPad))
	if err != nil {
		return err
	}
	h = max(h, c.LoopHeight)
	p.Nodes = append(p.Nodes, ProperNode{Node: Node{Decl: c.Decl, W: width, H: h, Parent: c.ID, Border: BorderTitle}, Edge: -1})
	p.Rank = append(p.Rank, p.Rank[c.Top])
	return nil
}

func placedTitles(p *Proper, x, y []int32) ([]Box, error) {
	var titles []Box
	for _, c := range p.Clusters {
		for i, n := range p.Nodes {
			if n.Border != BorderTitle || n.Parent != c.ID {
				continue
			}
			top, err := coordinate(int64(y[c.Top]) + int64(p.ClusterPad))
			if err != nil {
				return nil, err
			}
			titles = append(titles, Box{ID: c.ID, Rect: geom.Rect{X: x[i] - n.W/2, Y: top, W: c.TitleSize.W, H: c.TitleSize.H}})
		}
	}
	return titles, nil
}

func (out *labelPlacement) stack(label *EdgeLabel, actual, reserved geom.Rect, slot int32) error {
	prefix := int64(0)
	for _, item := range label.Items {
		rect, err := rectangle(int64(actual.X), int64(actual.Y)+prefix, int64(item.W), int64(item.H))
		if err != nil {
			return err
		}
		out.boxes = append(out.boxes, Box{ID: item.ID, Rect: rect})
		prefix += int64(item.H) + int64(slot)
	}
	out.reservations = append(out.reservations, LabelReservation{Label: label, Rect: reserved})
	return nil
}
