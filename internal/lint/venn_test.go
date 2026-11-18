package lint

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/model/venn"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/venn"
)

func TestVennRulePredicates(t *testing.T) {
	cases := []struct{ code, trigger, clean string }{
		{"venn/duplicate-set", "venn-beta\nset A\nset A\n", "venn-beta\nset A\nset B\n"},
		{"venn/non-positive-size", "venn-beta\nset A:0\n", "venn-beta\nset A:1\n"},
		{"venn/single-set", "venn-beta\nset A\n", "venn-beta\nset A\nset B\n"},
		{"venn/self-union", "venn-beta\nset A\nunion A,A\n", "venn-beta\nset A\nset B\nunion A,B\n"},
		{"venn/duplicate-union", "venn-beta\nset A\nset B\nunion A,B\nunion B,A\n", "venn-beta\nset A\nset B\nunion A,B\n"},
		{"venn/non-positive-size", "venn-beta\nset A:0.000\n", "venn-beta\nset A:0.0001\n"},
		{"venn/non-positive-size", "venn-beta\nset A\nunion A,Z:0\n", "venn-beta\nset A\nunion A,Z\n"},
		{"venn/duplicate-union", "venn-beta\nset A\nunion A,Z\nunion Z,A\n", "venn-beta\nset A\nunion A,A,Z\nunion A,Z\n"},
	}
	for _, tc := range cases {
		t.Run(tc.code, func(t *testing.T) {
			for _, input := range []struct {
				text string
				want int
			}{{tc.trigger, 1}, {tc.clean, 0}} {
				checkVennRuleCase(t, tc.code, input.text, input.want)
			}
		})
	}
}

func checkVennRuleCase(t *testing.T, code, text string, want int) {
	t.Helper()
	document, parseDiags := syn.Parse([]byte(text), nil)
	if len(parseDiags) != 0 {
		t.Fatalf("parse: %+v", parseDiags)
	}
	m, _ := venn.Resolve([]byte(text), document)
	row := Row{Code: code, Summary: "finding", Help: "help"}
	got := vennRules(m, row)
	if len(got) != want {
		t.Fatalf("%s: got %+v", text, got)
	}
	for _, d := range got {
		if d.Code != code || d.Message != "finding" || d.Help != "help" || d.Span.End > len(text) {
			t.Fatalf("bad finding: %+v", d)
		}
	}
}
