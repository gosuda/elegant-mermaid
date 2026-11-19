package layered

import (
	"math"
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
)

type Border uint8

const (
	BorderNone Border = iota
	BorderTop
	BorderBottom
	BorderLeft
	BorderRight
	BorderTitle
)

type Cluster struct {
	ID, Parent         string
	Decl               int32
	Top, Bottom        int32
	Lines              []measure.StyledLine
	Extent, LoopHeight int32
	TitleSize          geom.Size
}
type MeasuredLabel struct {
	ID, Text string
	W, H     int32
	Lines    []measure.StyledLine
}
type EdgeLabel struct {
	W, H  int32
	Items []MeasuredLabel
}
type LabelReservation struct {
	Label *EdgeLabel
	Rect  geom.Rect
}
type Layout struct {
	Boxes             []Box
	Routes            []EdgeRoute
	Labels            []Box
	Extents           []Box
	Titles            []Box
	LabelReservations []LabelReservation
	BudgetExhausted   bool
	fixedArea         int64
	Width, Height     int32
}
type PackOptions struct{ MaxWidth, Gap, AspectNum, AspectDen int32 }

func coordinate(n int64) (int32, error) {
	if n < math.MinInt32 || n > math.MaxInt32 {
		return 0, geom.ErrOverflow
	}
	return int32(n), nil
}

func parentOf(clusters []Cluster, id string) string {
	for _, c := range clusters {
		if c.ID == id {
			return c.Parent
		}
	}
	return ""
}

func insideCluster(clusters []Cluster, parent, id string) bool {
	for fuel := len(clusters) + 1; parent != "" && fuel > 0; fuel-- {
		if parent == id {
			return true
		}
		parent = parentOf(clusters, parent)
	}
	return false
}

func clusterBorders(g *Graph) {
	clusterRankNodes(g)
	clusterRankEdges(g)
}

func clusterRankNodes(g *Graph) {
	for i := range g.Clusters {
		c := &g.Clusters[i]
		c.Top = int32(len(g.Nodes))
		c.Bottom = c.Top + 1
		g.Nodes = append(g.Nodes, Node{ID: c.ID + ".top", Decl: c.Decl, Parent: c.ID, Border: BorderTop}, Node{ID: c.ID + ".bottom", Decl: c.Decl, Parent: c.ID, Border: BorderBottom})
	}
}

func clusterRankEdges(g *Graph) {
	for _, c := range g.Clusters {
		addClusterEdges(g, c)
		addHierarchyEdges(g, c)
	}
}

func addClusterEdges(g *Graph, c Cluster) {
	count := 0
	for i, n := range g.Nodes {
		if n.Border != BorderNone || !insideCluster(g.Clusters, n.Parent, c.ID) {
			continue
		}
		appendBorderEdge(g, c.Top, int32(i))
		appendBorderEdge(g, int32(i), c.Bottom)
		count++
	}
	for _, child := range g.Clusters {
		if child.Parent == c.ID {
			count++
		}
	}
	if count == 0 {
		appendBorderEdge(g, c.Top, c.Bottom)
	}
}

func addHierarchyEdges(g *Graph, parent Cluster) {
	for _, child := range g.Clusters {
		if child.Parent != parent.ID {
			continue
		}
		appendBorderEdge(g, parent.Top, child.Top)
		appendBorderEdge(g, child.Bottom, parent.Bottom)
	}
}

func appendBorderEdge(g *Graph, a, b int32) {
	g.Edges = append(g.Edges, Edge{Tail: a, Head: b, MinLen: 1, Decl: int32(len(g.Edges)), Synthetic: true})
}

func cloneGraph(g *Graph) *Graph {
	out := *g
	out.Nodes = slices.Clone(g.Nodes)
	out.Edges = slices.Clone(g.Edges)
	out.Clusters = slices.Clone(g.Clusters)
	return &out
}

func declaredNodes(g *Graph) []int32 {
	nodes := make([]int32, len(g.Nodes))
	for i := range nodes {
		nodes[i] = int32(i)
	}
	slices.SortStableFunc(nodes, func(a, b int32) int {
		if earlierNode(g, a, b) {
			return -1
		}
		if earlierNode(g, b, a) {
			return 1
		}
		return 0
	})
	return nodes
}

func declaredReady(g *Graph, degree []int, done []bool) int {
	best := int32(-1)
	for i, d := range degree {
		if d == 0 && !done[i] && earlierNode(g, int32(i), best) {
			best = int32(i)
		}
	}
	return int(best)
}

func rectangle(x, y, w, h int64) (geom.Rect, error) {
	if w < 0 || h < 0 {
		return geom.Rect{}, ErrGraph
	}
	for _, value := range [4]int64{x, y, w, h} {
		if _, err := coordinate(value); err != nil {
			return geom.Rect{}, err
		}
	}
	if _, err := coordinate(x + w); err != nil {
		return geom.Rect{}, err
	}
	if _, err := coordinate(y + h); err != nil {
		return geom.Rect{}, err
	}
	return geom.Rect{X: int32(x), Y: int32(y), W: int32(w), H: int32(h)}, nil
}
