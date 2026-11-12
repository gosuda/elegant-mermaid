package layered

import (
	"cmp"
	"errors"
	"fmt"
	"math"
	"reflect"
	"slices"
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	random "github.com/gosuda/elegant-mermaid/tools/randgraph/gen"
)

func TestNestedBorderPaddingIsSymmetric(t *testing.T) {
	p := &Proper{
		Nodes: []ProperNode{
			{Node: Node{W: 2, Parent: "inner", Border: BorderRight}},
			{Node: Node{W: 2, Parent: "outer", Border: BorderRight}},
		},
		Clusters: []Cluster{{ID: "outer"}, {ID: "inner", Parent: "outer"}},
		Params:   Params{ClusterPad: 1},
	}
	c := coordinatePass{p: p, gap: 2}
	for _, pair := range [][2]int32{{0, 1}, {1, 0}} {
		if got := c.separation(pair[0], pair[1]); got != 3 {
			t.Fatalf("separation(%d, %d) = %d, want widths plus cluster_pad = 3", pair[0], pair[1], got)
		}
	}
}

func coordinateCase(t *testing.T, index int) (*Proper, [][]int32) {
	t.Helper()
	src, err := random.Source("layered", index)
	if err != nil {
		t.Fatal(err)
	}
	params, err := DefaultParams(scene.ProfileVector)
	if err != nil {
		t.Fatal(err)
	}
	g := &Graph{Params: params}
	for _, line := range strings.Split(src, "\n")[1:] {
		coordinateStatement(g, line)
	}
	if _, err := BreakCycles(g); err != nil {
		t.Fatal(err)
	}
	rank, err := Rank(g)
	if err != nil {
		t.Fatal(err)
	}
	p, err := Normalize(g, rank)
	if err != nil {
		t.Fatal(err)
	}
	layers := make([][]int32, int(slices.Max(p.Rank))+1)
	for v, r := range p.Rank {
		layers[r] = append(layers[r], int32(v))
	}
	for _, layer := range layers {
		slices.SortStableFunc(layer, func(a, b int32) int {
			if d := cmp.Compare(p.Nodes[a].Decl, p.Nodes[b].Decl); d != 0 {
				return d
			}
			return cmp.Compare(a, b)
		})
	}
	return p, layers
}
func coordinateStatement(g *Graph, line string) {
	var a, b int
	if _, err := fmt.Sscanf(line, "n%d --> n%d", &a, &b); err == nil {
		g.Edges = append(g.Edges, Edge{Tail: int32(a), Head: int32(b), MinLen: 1, Decl: int32(len(g.Edges))})
		return
	}
	if strings.Contains(line, "[") {
		g.Nodes = append(g.Nodes, Node{Decl: int32(len(g.Nodes)), W: 2048 + int32(len(line))*64, H: 2304})
	}
}

type oracleCoordinate struct {
	root, align, sink map[int32]int32
	x, shift          map[int32]int64
	pos, rank         map[int32]int
	layers            [][]int32
	p                 *Proper
	blocked           map[[2]int32]bool
}

func oraclePass(p *Proper, layers [][]int32, pass int) []int64 {
	o := oracleCoordinate{root: map[int32]int32{}, align: map[int32]int32{}, sink: map[int32]int32{}, x: map[int32]int64{}, shift: map[int32]int64{}, pos: map[int32]int{}, rank: map[int32]int{}, p: p, blocked: map[[2]int32]bool{}}
	o.initialize(layers, pass)
	o.conflicts()
	o.alignLayers()
	for _, l := range o.layers {
		for _, v := range l {
			if o.root[v] == v {
				o.place(v)
			}
		}
	}
	o.offsets()
	out := make([]int64, len(p.Nodes))
	for v := range out {
		out[v] = o.x[int32(v)] + o.shift[o.sink[int32(v)]]
		if pass%2 == 1 {
			out[v] = -out[v]
		}
	}
	lo := slices.Min(out)
	for i := range out {
		out[i] -= lo
	}
	return out
}
func (o *oracleCoordinate) alignLayers() {
	for _, layer := range o.layers {
		o.alignLayer(layer)
	}
}
func (o *oracleCoordinate) neighbours(v int32) []int32 {
	var ns []int32
	for _, e := range o.p.Edges {
		a, b := e.Tail, e.Head
		if a == v {
			a, b = b, a
		}
		if b == v && o.rank[a] < o.rank[v] {
			ns = append(ns, a)
		}
	}
	slices.SortStableFunc(ns, func(a, b int32) int { return cmp.Compare(o.pos[a], o.pos[b]) })
	return ns
}
func (o *oracleCoordinate) alignLayer(layer []int32) {
	last := -1
	for _, v := range layer {
		ns := o.neighbours(v)
		if len(ns) == 0 {
			continue
		}
		for _, k := range []int{(len(ns) - 1) / 2, len(ns) / 2} {
			w := ns[k]
			if o.align[v] != v || o.pos[w] <= last || o.blocked[[2]int32{w, v}] {
				continue
			}
			o.align[w] = v
			o.align[v] = o.root[w]
			o.root[v] = o.root[w]
			last = o.pos[w]
		}
	}
}
func (o *oracleCoordinate) sep(a, b int32) int64 {
	return int64(o.p.Nodes[a].W)/2 + int64(o.p.Nodes[b].W)/2 + int64(o.p.NodeGap)
}
func (o *oracleCoordinate) place(v int32) {
	if _, ok := o.x[v]; ok {
		return
	}
	o.x[v] = 0
	w := v
	for {
		if o.pos[w] > 0 {
			pred := o.layers[o.rank[w]][o.pos[w]-1]
			u := o.root[pred]
			o.place(u)
			if o.sink[v] == v {
				o.sink[v] = o.sink[u]
			}
			if o.sink[v] == o.sink[u] {
				o.x[v] = max(o.x[v], o.x[u]+o.sep(pred, w))
			}
		}
		w = o.align[w]
		if w == v {
			break
		}
	}
	for m := o.align[v]; m != v; m = o.align[m] {
		o.x[m] = o.x[v]
		o.sink[m] = o.sink[v]
	}
}
func (o *oracleCoordinate) offsets() {
	for r, l := range o.layers {
		if len(l) == 0 {
			continue
		}
		s := l[0]
		if _, ok := o.shift[s]; !ok && o.sink[s] == s {
			o.shift[s] = 0
		}
		o.offsetRank(r)
	}
}
func (o *oracleCoordinate) offsetRank(r int) {
	for _, row := range o.layers {
		for j := 1; j < len(row); j++ {
			o.offsetPair(r, row[j-1], row[j])
		}
	}
}
func (o *oracleCoordinate) offsetPair(r int, a, b int32) {
	sa, sb := o.sink[a], o.sink[b]
	if sa == sb || o.rank[sb] != r {
		return
	}
	d := o.shift[sb] + o.x[b] - o.x[a] - o.sep(a, b)
	old, ok := o.shift[sa]
	if !ok || d < old {
		o.shift[sa] = d
	}
}
func (o *oracleCoordinate) initialize(layers [][]int32, pass int) {
	for r := range layers {
		i := r
		if pass >= 2 {
			i = len(layers) - 1 - r
		}
		l := slices.Clone(layers[i])
		if pass%2 == 1 {
			slices.Reverse(l)
		}
		o.layers = append(o.layers, l)
		for j, v := range l {
			o.pos[v] = j
			o.rank[v] = r
			o.root[v] = v
			o.align[v] = v
			o.sink[v] = v
		}
	}
}
func (o *oracleCoordinate) conflicts() {
	for _, e := range o.p.Edges {
		if o.p.Nodes[e.Tail].Dummy && o.p.Nodes[e.Head].Dummy {
			continue
		}
		o.markCrossings(e)
	}
}
func (o *oracleCoordinate) markCrossings(e ProperEdge) {
	for _, f := range o.p.Edges {
		if !o.p.Nodes[f.Tail].Dummy || !o.p.Nodes[f.Head].Dummy || o.p.Rank[e.Tail] != o.p.Rank[f.Tail] {
			continue
		}
		if (o.pos[e.Tail]-o.pos[f.Tail])*(o.pos[e.Head]-o.pos[f.Head]) >= 0 {
			continue
		}
		o.blocked[[2]int32{e.Tail, e.Head}] = true
		o.blocked[[2]int32{e.Head, e.Tail}] = true
	}
}
func oracleCoordinates(p *Proper, layers [][]int32) []int32 {
	var passes [4][]int64
	width := [4]int64{}
	best := 0
	for k := range passes {
		passes[k] = oraclePass(p, layers, k)
		width[k] = slices.Max(passes[k])
		if width[k] < width[best] {
			best = k
		}
	}
	lo := int64(0)
	for k := 1; k < 4; k += 2 {
		d := width[best] - width[k]
		lo = min(lo, d)
		for v := range passes[k] {
			passes[k][v] += d
		}
	}
	out := make([]int32, len(p.Nodes))
	for v := range out {
		values := []int64{passes[0][v], passes[1][v], passes[2][v], passes[3][v]}
		slices.Sort(values)
		out[v] = int32((values[1] + values[2] - 2*lo) / 2)
	}
	return out
}
func TestCoordinatesOracle(t *testing.T) {
	for i := range 200 {
		t.Run(fmt.Sprint(i), func(t *testing.T) {
			p, layers := coordinateCase(t, i)
			x, err := CrossCoords(p, layers)
			if err != nil {
				t.Fatal(err)
			}
			want := oracleCoordinates(p, layers)
			if !reflect.DeepEqual(x, want) {
				t.Fatalf("got %v want %v", x, want)
			}
			checkCoordinateSeparation(t, p, layers, x)
		})
	}
}
func checkCoordinateSeparation(t *testing.T, p *Proper, layers [][]int32, x []int32) {
	t.Helper()
	for _, layer := range layers {
		for j := 1; j < len(layer); j++ {
			a, b := layer[j-1], layer[j]
			sep := int64(p.Nodes[a].W)/2 + int64(p.Nodes[b].W)/2 + int64(p.NodeGap)
			if int64(x[b])-int64(x[a]) < sep {
				t.Fatalf("separation %d %d: %v", a, b, x)
			}
		}
	}
}
func TestCoordinateOverflow(t *testing.T) {
	p, layers := handProper(t, 3, nil)
	for i := range p.Nodes {
		p.Nodes[i].W = math.MaxInt32
	}
	if _, err := CrossCoords(p, layers); !errors.Is(err, geom.ErrOverflow) {
		t.Fatalf("coordinate overflow: %v", err)
	}
	p, layers = handProper(t, 2, [][2]int32{{0, 1}})
	p.Nodes[0].H = math.MaxInt32
	r, err := Route(p, layers, []int32{0, 0})
	if err != nil {
		t.Fatal(err)
	}
	if _, _, err := RankCoords(p, layers, r); !errors.Is(err, geom.ErrOverflow) {
		t.Fatalf("rank overflow: %v", err)
	}
}
