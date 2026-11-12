package layout

import (
	"strings"
	"testing"
)

func TestModelRouteStyles(t *testing.T) {
	cases := []struct{ source, route string }{
		{"A --- B", `{"id":"e0","from":"A","to":"B","orthogonal":true,"marker_end":"none"}`},
		{"A <--> B", `{"id":"e0","from":"A","to":"B","orthogonal":true,"marker_start":"point"}`},
		{"A o--o B", `{"id":"e0","from":"A","to":"B","orthogonal":true,"marker_start":"circle","marker_end":"circle"}`},
		{"A x--x B", `{"id":"e0","from":"A","to":"B","orthogonal":true,"marker_start":"cross","marker_end":"cross"}`},
		{"A -.-> B", `{"id":"e0","from":"A","to":"B","orthogonal":true,"stroke":"dotted"}`},
		{"A ==> B", `{"id":"e0","from":"A","to":"B","orthogonal":true,"stroke":"thick"}`},
		{"A --> B", `{"id":"e0","from":"A","to":"B","orthogonal":true}`},
	}
	for _, c := range cases {
		t.Run(c.source, func(t *testing.T) {
			in, ok := inputSource(t, []byte("flowchart\n"+c.source+"\n"))
			if !ok {
				t.Fatal("source rejected")
			}
			dump := string(dumpInput(t, in))
			want := `"routes":[` + c.route + `]`
			if !strings.Contains(dump, want) {
				t.Fatalf("expected %s in\n%s", want, dump)
			}
		})
	}
}
