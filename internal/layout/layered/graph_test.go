package layered

import "testing"

func TestRankDenseOracle(t *testing.T) {
	s := uint32(17)
	for range 300 {
		g := &Graph{Nodes: []Node{{Decl: 0}, {Decl: 1}, {Decl: 2}, {Decl: 3}, {Decl: 4}}}
		for a := range 5 {
			for b := a + 1; b < 5; b++ {
				s ^= s << 13
				s ^= s >> 17
				s ^= s << 5
				if s%3 == 0 {
					continue
				}
				g.Edges = append(g.Edges, Edge{Tail: int32(a), Head: int32(b), MinLen: int32(1 + s%2), Decl: int32(len(g.Edges))})
			}
		}
		assertOptimal(t, g)
	}
}
