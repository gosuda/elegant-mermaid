package lint

import (
	"testing"

	model "github.com/gosuda/elegant-mermaid/internal/model/packet"
	"github.com/gosuda/elegant-mermaid/internal/source"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/packet"
)

func TestPacketNoFields(t *testing.T) {
	for i, text := range []string{"packet\n", "packet\n0: \"a\"\n"} {
		document, _ := parser.Parse([]byte(text), nil)
		m, _ := model.Resolve([]byte(text), document)
		row := Row{Code: "packet/no-fields", Summary: "expected", Help: "help"}
		ds := packetNoFields(m, source.Span{Start: 0, End: 6}, row)
		want := 0
		if i == 0 {
			want = 1
		}
		if len(ds) != want {
			t.Fatalf("case %d: got %d diagnostics, want %d", i, len(ds), want)
		}
		for _, d := range ds {
			if d.Code != row.Code || d.Message != row.Summary || d.Help != row.Help || d.Span.Start < 0 || d.Span.End > len(text) {
				t.Fatalf("unexpected diagnostic: %+v", d)
			}
		}
	}
}

func TestPacketEmptyLabels(t *testing.T) {
	for i, text := range []string{"packet\n0: \"\"\n", "packet\n0: \"a\"\n"} {
		document, _ := parser.Parse([]byte(text), nil)
		m, _ := model.Resolve([]byte(text), document)
		row := Row{Code: "packet/empty-labels", Summary: "expected", Help: "help"}
		ds := packetEmptyLabels(m, row)
		want := 0
		if i == 0 {
			want = 1
		}
		if len(ds) != want {
			t.Fatalf("case %d: got %d diagnostics, want %d", i, len(ds), want)
		}
		for _, d := range ds {
			if d.Code != row.Code || d.Message != row.Summary || d.Help != row.Help || d.Span.Start < 0 || d.Span.End > len(text) {
				t.Fatalf("unexpected diagnostic: %+v", d)
			}
		}
	}
}
