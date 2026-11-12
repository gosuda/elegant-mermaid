package layered

import (
	"errors"
	"testing"
)

func proxySpanGraph() (*Proper, []int32) {
	p := &Proper{Clusters: []Cluster{{ID: "G", Top: 0, Bottom: 1}}, Rank: []int32{0, 1, 0, 0, 1, 1}, Nodes: []ProperNode{{}, {}, {Node: Node{Parent: "G", Border: BorderLeft, W: 2}}, {Node: Node{Parent: "G", Border: BorderRight, W: 2}}, {Node: Node{Parent: "G", Border: BorderLeft, W: 2}}, {Node: Node{Parent: "G", Border: BorderRight, W: 2}}}}
	return p, []int32{0, 0, 1, 9, 3, 19}
}

func TestProxyRankSpan(t *testing.T) {
	p, x := proxySpanGraph()
	got, err := clusterRankBounds(p, x, "G", 0)
	if err != nil || got != (horizontalSpan{Lo: 0, Hi: 10}) {
		t.Fatalf("local span: %v %v", got, err)
	}
	global, err := clusterBounds(p, x)
	if err != nil || global[0] != (horizontalSpan{Lo: 0, Hi: 20}) {
		t.Fatalf("frame span: %v %v", global, err)
	}
}

func TestProxyPortUsesRankSpan(t *testing.T) {
	p, x := proxySpanGraph()
	p.Nodes = append(p.Nodes, ProperNode{})
	p.Rank = append(p.Rank, 2)
	x = append(x, 5)
	p.Original = []Edge{{Tail: 0, Head: 6, SourceGroup: "G"}}
	p.Edges = []ProperEdge{{Tail: 0, Head: 6, Original: 0}}
	p.Chains = [][]int32{{0, 6}}
	p.Out = make([][]int32, len(p.Nodes))
	p.In = make([][]int32, len(p.Nodes))
	p.Out[0] = []int32{0}
	p.In[6] = []int32{0}
	r := &Routing{SourceX: make([]int32, 1), TargetX: make([]int32, 1)}
	if err := groupProxyPorts(p, x, r); err != nil {
		t.Fatal(err)
	}
	if r.SourceX[0] != 5 {
		t.Fatalf("proxy port = %d, want local midpoint 5", r.SourceX[0])
	}
}

func TestProxyMissingRankBorder(t *testing.T) {
	p, x := proxySpanGraph()
	p.Nodes[3].Border = BorderNone
	if _, err := clusterRankBounds(p, x, "G", 0); !errors.Is(err, ErrGraph) {
		t.Fatalf("missing border: %v", err)
	}
}
