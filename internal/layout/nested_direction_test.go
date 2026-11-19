package layout

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	model "github.com/gosuda/elegant-mermaid/internal/model/flowchart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/flowchart"
)

const nestedDirectionSource = "flowchart TB\n" +
	"  subgraph outer[Outer]\n" +
	"    a1[A1] --> a2[A2]\n" +
	"    subgraph inner[Inner]\n" +
	"      direction LR\n" +
	"      b1[B1] --> b2[B2] --> b3[B3]\n" +
	"    end\n" +
	"    a2 --> a3[A3]\n" +
	"  end\n" +
	"  s[Start] --> a1\n" +
	"  a3 --> e[End]\n"

func nestedNoErrors(t *testing.T, ds []diag.Diagnostic) {
	t.Helper()
	for _, d := range ds {
		if d.Severity == diag.SeverityError {
			t.Fatalf("unexpected error diagnostic %s: %s", d.Code, d.Message)
		}
	}
}

func nestedDirectionScene(t *testing.T, profile scene.Profile) scene.Scene {
	t.Helper()
	src := []byte(nestedDirectionSource)
	p := syntax.Preprocess(src)
	f, parsed := parser.Parse(src, p.Removed)
	nestedNoErrors(t, parsed)
	m, resolved := model.Resolve(src, f)
	nestedNoErrors(t, resolved)
	in, adapted := FromFlowchart(m, profile, scene.Options{})
	nestedNoErrors(t, adapted)
	return step14Scene(t, in)
}

func nestedSceneRect(t *testing.T, s scene.Scene, id string) geom.Rect {
	t.Helper()
	for _, b := range s.Boxes {
		if b.ID == id {
			return b.Rect
		}
	}
	for _, l := range s.Labels {
		if l.ID == id {
			return l.Rect
		}
	}
	t.Fatalf("%q missing from scene", id)
	return geom.Rect{}
}

func TestNestedDirectionSubgraphIsRankedMemberOfParentCluster(t *testing.T) {
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		s := nestedDirectionScene(t, profile)
		outer, inner := nestedSceneRect(t, s, "outer"), nestedSceneRect(t, s, "inner")
		title := nestedSceneRect(t, s, "outer.label")
		if inner.Y < title.Y+title.H {
			t.Fatalf("profile %v: inner frame %+v starts above the outer title %+v", profile, inner, title)
		}
		if contains, err := geom.Contains(outer, inner); err != nil || !contains {
			t.Fatalf("profile %v: outer %+v does not contain inner %+v", profile, outer, inner)
		}
		if a1 := nestedSceneRect(t, s, "a1"); inner.Y >= a1.Y+a1.H || a1.Y >= inner.Y+inner.H {
			t.Fatalf("profile %v: fixed inner node %+v shares no rank with its peer %+v", profile, inner, a1)
		}
	}
	s := nestedDirectionScene(t, scene.ProfileCell)
	want := map[string]geom.Rect{
		"outer": {X: 1, Y: 1, W: 41, H: 31},
		"inner": {X: 10, Y: 8, W: 31, H: 5},
		"b1":    {X: 16, Y: 9, W: 6, H: 3},
		"a1":    {X: 2, Y: 9, W: 6, H: 3},
	}
	for id, rect := range want {
		if got := nestedSceneRect(t, s, id); got != rect {
			t.Fatalf("cell %s = %+v, want %+v", id, got, rect)
		}
	}
}
