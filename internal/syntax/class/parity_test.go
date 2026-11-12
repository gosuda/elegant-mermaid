package class_test

import (
	"strings"
	"testing"

	parser "github.com/gosuda/elegant-mermaid/internal/syntax/class"
)

func TestQuotedMultiplicityIsNotMarker(t *testing.T) {
	f, ds := parser.Parse([]byte("classDiagram\nUser \"1\" -- \"*\" Order : places\n"), nil)
	if len(ds) != 0 || len(f.Statements) != 1 {
		t.Fatal(f, ds)
	}
	r := f.Statements[0].Relation
	if r == nil || r.Relation.End != "" || r.ToMultiplicity != "*" {
		t.Fatal(r)
	}
}

func TestRejectedStatementRecoversOnce(t *testing.T) {
	for _, body := range []string{"A -> B", "namespace \"quoted\" {", "class \"quoted\""} {
		_, ds := parser.Parse([]byte("classDiagram\n"+body+"\nclass Next\n"), nil)
		if len(ds) != 1 {
			t.Fatal(body, ds)
		}
		if strings.Contains(body, "quoted") && !strings.Contains(ds[0].Message, "\"quoted\"") {
			t.Fatal(ds)
		}
	}
}
