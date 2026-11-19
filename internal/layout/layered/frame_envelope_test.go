package layered

import (
	"reflect"
	"slices"
	"testing"
)

type markingFixture struct {
	name   string
	nodes  []ProperNode
	rank   []int32
	edges  [][2]int32
	layers [][]int32
	want   []bool
}

func chainNode(parent string) ProperNode {
	return ProperNode{Node: Node{Parent: parent, Border: BorderLeft}, Edge: -1}
}

func markingProper(f markingFixture) (*Proper, []int32) {
	p := &Proper{Nodes: f.nodes, Rank: f.rank}
	for _, e := range f.edges {
		p.Edges = append(p.Edges, ProperEdge{Tail: e[0], Head: e[1], Original: -1})
	}
	return p, orderPositions32(f.layers, len(f.nodes))
}

func orderPositions32(layers [][]int32, n int) []int32 {
	pos := make([]int32, n)
	for _, layer := range layers {
		for i, v := range layer {
			pos[v] = int32(i)
		}
	}
	return pos
}

func TestBorderChainPriorityInConflictMarking(t *testing.T) {
	dummy := ProperNode{Node: Node{}, Dummy: true, Edge: 0}
	plain := ProperNode{Edge: -1}
	cases := []markingFixture{
		{
			name:   "real segment crossing a border chain",
			nodes:  []ProperNode{chainNode("C"), chainNode("C"), plain, plain},
			rank:   []int32{0, 1, 0, 1},
			edges:  [][2]int32{{0, 1}, {2, 3}},
			layers: [][]int32{{0, 2}, {3, 1}},
			want:   []bool{false, true},
		},
		{
			name:   "inner segment crossing a border chain",
			nodes:  []ProperNode{chainNode("C"), chainNode("C"), dummy, dummy},
			rank:   []int32{0, 1, 0, 1},
			edges:  [][2]int32{{0, 1}, {2, 3}},
			layers: [][]int32{{0, 2}, {3, 1}},
			want:   []bool{false, true},
		},
		{
			name:   "border chain crossing an inner segment stays unmarked",
			nodes:  []ProperNode{chainNode("C"), chainNode("C"), dummy, dummy},
			rank:   []int32{0, 1, 0, 1},
			edges:  [][2]int32{{2, 3}, {0, 1}},
			layers: [][]int32{{2, 0}, {1, 3}},
			want:   []bool{true, false},
		},
		{
			name:   "segments that do not cross stay unmarked",
			nodes:  []ProperNode{chainNode("C"), chainNode("C"), plain, plain},
			rank:   []int32{0, 1, 0, 1},
			edges:  [][2]int32{{0, 1}, {2, 3}},
			layers: [][]int32{{0, 2}, {1, 3}},
			want:   []bool{false, false},
		},
		{
			name:   "real segment crossing an inner segment is still marked",
			nodes:  []ProperNode{plain, plain, dummy, dummy},
			rank:   []int32{0, 1, 0, 1},
			edges:  [][2]int32{{0, 1}, {2, 3}},
			layers: [][]int32{{0, 2}, {3, 1}},
			want:   []bool{true, false},
		},
		{
			name:   "border chains of two clusters are never marked even when they cross",
			nodes:  []ProperNode{chainNode("C"), chainNode("C"), chainNode("D"), chainNode("D")},
			rank:   []int32{0, 1, 0, 1},
			edges:  [][2]int32{{0, 1}, {2, 3}},
			layers: [][]int32{{0, 2}, {3, 1}},
			want:   []bool{false, false},
		},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			p, pos := markingProper(c)
			if got := typeOneConflicts(p, pos); !reflect.DeepEqual(got, c.want) {
				t.Fatalf("marks %v, want %v", got, c.want)
			}
		})
	}
}

type siblingFixture struct {
	p      *Proper
	left   map[string][]int32
	right  map[string][]int32
	layers [][]int32
}

func newSiblingFixture(ranks int, clusters ...Cluster) *siblingFixture {
	f := &siblingFixture{p: &Proper{Clusters: clusters}, left: map[string][]int32{}, right: map[string][]int32{}}
	for _, c := range clusters {
		for r := range ranks {
			f.left[c.ID] = append(f.left[c.ID], f.node(c.ID, BorderLeft, int32(r)))
			f.right[c.ID] = append(f.right[c.ID], f.node(c.ID, BorderRight, int32(r)))
		}
	}
	f.layers = make([][]int32, ranks)
	return f
}

func (f *siblingFixture) node(parent string, border Border, rank int32) int32 {
	f.p.Nodes = append(f.p.Nodes, ProperNode{Node: Node{Parent: parent, Border: border}, Edge: -1})
	f.p.Rank = append(f.p.Rank, rank)
	return int32(len(f.p.Nodes) - 1)
}

func (f *siblingFixture) block(rank int, id string) []int32 {
	return []int32{f.left[id][rank], f.right[id][rank]}
}

func (f *siblingFixture) set(rank int, parts ...[]int32) {
	f.layers[rank] = slices.Concat(parts...)
}

func (f *siblingFixture) normalise(t *testing.T) {
	t.Helper()
	if err := (orderGraph{p: f.p}).siblingNormalise(f.layers); err != nil {
		t.Fatal(err)
	}
}

func TestSiblingNormaliseFlipsTheMinorityRank(t *testing.T) {
	f := newSiblingFixture(3, Cluster{ID: "A", Decl: 0}, Cluster{ID: "B", Decl: 1})
	f.set(0, f.block(0, "A"), f.block(0, "B"))
	f.set(1, f.block(1, "A"), f.block(1, "B"))
	f.set(2, f.block(2, "B"), f.block(2, "A"))
	f.normalise(t)
	for r := range 3 {
		if want := slices.Concat(f.block(r, "A"), f.block(r, "B")); !slices.Equal(f.layers[r], want) {
			t.Fatalf("rank %d: %v, want %v", r, f.layers[r], want)
		}
	}
}

func TestSiblingNormaliseTieGoesToTheLowerDeclaration(t *testing.T) {
	f := newSiblingFixture(2, Cluster{ID: "A", Decl: 4}, Cluster{ID: "B", Decl: 2})
	f.set(0, f.block(0, "A"), f.block(0, "B"))
	f.set(1, f.block(1, "B"), f.block(1, "A"))
	f.normalise(t)
	for r := range 2 {
		if want := slices.Concat(f.block(r, "B"), f.block(r, "A")); !slices.Equal(f.layers[r], want) {
			t.Fatalf("rank %d: %v, want %v", r, f.layers[r], want)
		}
	}
}

func TestSiblingNormaliseKeepsLooseNodesInPlace(t *testing.T) {
	f := newSiblingFixture(3, Cluster{ID: "A", Decl: 0}, Cluster{ID: "B", Decl: 1})
	loose := f.node("", BorderNone, 2)
	f.set(0, f.block(0, "A"), f.block(0, "B"))
	f.set(1, f.block(1, "A"), f.block(1, "B"))
	f.set(2, f.block(2, "B"), []int32{loose}, f.block(2, "A"))
	f.normalise(t)
	want := slices.Concat(f.block(2, "A"), []int32{loose}, f.block(2, "B"))
	if !slices.Equal(f.layers[2], want) {
		t.Fatalf("rank 2: %v, want %v", f.layers[2], want)
	}
}

func TestSiblingNormaliseRecursesIntoParentBlocks(t *testing.T) {
	f := newSiblingFixture(3, Cluster{ID: "P", Decl: 0}, Cluster{ID: "Q", Parent: "P", Decl: 1}, Cluster{ID: "R", Parent: "P", Decl: 2})
	inside := func(r int, a, b string) []int32 {
		return slices.Concat([]int32{f.left["P"][r]}, f.block(r, a), f.block(r, b), []int32{f.right["P"][r]})
	}
	f.set(0, inside(0, "Q", "R"))
	f.set(1, inside(1, "Q", "R"))
	f.set(2, inside(2, "R", "Q"))
	f.normalise(t)
	for r := range 3 {
		if want := inside(r, "Q", "R"); !slices.Equal(f.layers[r], want) {
			t.Fatalf("rank %d: %v, want %v", r, f.layers[r], want)
		}
	}
}

func TestSiblingNormaliseCycleTakesTheSmallestKey(t *testing.T) {
	f := newSiblingFixture(3, Cluster{ID: "A", Decl: 0}, Cluster{ID: "B", Decl: 1}, Cluster{ID: "C", Decl: 2})
	f.set(0, f.block(0, "A"), f.block(0, "B"), f.block(0, "C"))
	f.set(1, f.block(1, "B"), f.block(1, "C"), f.block(1, "A"))
	f.set(2, f.block(2, "C"), f.block(2, "A"), f.block(2, "B"))
	f.normalise(t)
	for r := range 3 {
		if want := slices.Concat(f.block(r, "A"), f.block(r, "B"), f.block(r, "C")); !slices.Equal(f.layers[r], want) {
			t.Fatalf("rank %d: %v, want %v", r, f.layers[r], want)
		}
	}
}

func TestSiblingNormaliseCycleKeyOutranksDeclaration(t *testing.T) {
	f := newSiblingFixture(3, Cluster{ID: "A", Decl: 5}, Cluster{ID: "B", Decl: 1}, Cluster{ID: "C", Decl: 0})
	loose := f.node("", BorderNone, 0)
	f.set(0, f.block(0, "A"), []int32{loose}, f.block(0, "B"), f.block(0, "C"))
	f.set(1, f.block(1, "B"), f.block(1, "C"), f.block(1, "A"))
	f.set(2, f.block(2, "C"), f.block(2, "A"), f.block(2, "B"))
	f.normalise(t)
	want := [][]int32{
		slices.Concat(f.block(0, "A"), []int32{loose}, f.block(0, "B"), f.block(0, "C")),
		slices.Concat(f.block(1, "A"), f.block(1, "B"), f.block(1, "C")),
		slices.Concat(f.block(2, "A"), f.block(2, "B"), f.block(2, "C")),
	}
	if !reflect.DeepEqual(f.layers, want) {
		t.Fatalf("layers %v, want %v", f.layers, want)
	}
}

func TestSiblingNormaliseKeepsConsistentOrder(t *testing.T) {
	f := newSiblingFixture(2, Cluster{ID: "A", Decl: 5}, Cluster{ID: "B", Decl: 1})
	f.set(0, f.block(0, "A"), f.block(0, "B"))
	f.set(1, f.block(1, "A"), f.block(1, "B"))
	before := [][]int32{slices.Clone(f.layers[0]), slices.Clone(f.layers[1])}
	f.normalise(t)
	if !reflect.DeepEqual(f.layers, before) {
		t.Fatalf("consistent order changed: %v, was %v", f.layers, before)
	}
}

func TestSiblingNormaliseWithoutClustersIsANoOp(t *testing.T) {
	p := &Proper{Nodes: []ProperNode{{}, {}}, Rank: []int32{0, 0}}
	layers := [][]int32{{1, 0}}
	if err := (orderGraph{p: p}).siblingNormalise(layers); err != nil || !slices.Equal(layers[0], []int32{1, 0}) {
		t.Fatalf("%v %v", layers, err)
	}
}
