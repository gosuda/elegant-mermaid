package c4_test

import (
	"testing"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/c4"
	"github.com/gosuda/elegant-mermaid/internal/source"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/c4"
)

func FuzzC4(f *testing.F) {
	for _, s := range []string{
		"C4Context\nPerson(a,\"A\")",
		"C4Context\ntitle Demo\nSystem_Boundary(b,\"B\") {\nSystem(a,\"A\")\nRel(a,b,\"uses\")\n}",
		"C4Container\nContainerDb(a,\"A\",\"SQL\",$descr=\"store\")\nRelIndex(1,a,b,\"go\")",
		"C4Component\nComponentQueue_Ext(a,\"A\",,\"\",$tags=\"x\")",
		"C4Dynamic\naccDescr { one\ntwo }\nBiRel(a,b,\"x\")\nRel_Back(b,a,\"y\")",
		"C4Deployment\nDeployment_Node(n,\"N\") {\nNode_L(l,\"L\") {\nPerson(p,\"P\")\n}\n}",
		"direction LR",
		"C4Context\nUpdateElementStyle(a,$bgColor=\"blue\")\nUpdateRelStyle(a,b,$offsetX=\"-2px\")\nUpdateLayoutConfig(\"3\",\"2\")",
		"C4Context\nPerson(",
		"C4Context\nBoundary(b,\"B\") {",
	} {
		f.Add([]byte(s))
	}
	f.Fuzz(func(t *testing.T, src []byte) {
		document, _ := source.RepairUTF8(src)
		start, ds := parser.Parse(document, nil)
		checkC4Diagnostics(t, document, ds)
		if start == nil {
			t.Fatal("nil start")
		}
		_, more := model.Resolve(document, start)
		checkC4Diagnostics(t, document, more)
	})
}

func checkC4Diagnostics(t *testing.T, src []byte, ds []diag.Diagnostic) {
	t.Helper()
	for _, d := range ds {
		checkC4DiagSpan(t, src, d)
	}
	for i := 1; i < len(ds); i++ {
		checkC4DiagOrder(t, ds[i-1], ds[i])
	}
}

func checkC4DiagSpan(t *testing.T, src []byte, d diag.Diagnostic) {
	t.Helper()
	if d.Span.Start < 0 || d.Span.End < d.Span.Start || d.Span.End > len(src) {
		t.Fatalf("diagnostic span outside source: %+v", d)
	}
	if !onRuneBoundary(src, d.Span.Start) || !onRuneBoundary(src, d.Span.End) {
		t.Fatalf("diagnostic span not on a UTF-8 boundary: %+v", d)
	}
}

func checkC4DiagOrder(t *testing.T, previous, d diag.Diagnostic) {
	t.Helper()
	if d.Span.Start < previous.Span.Start || d.Span.Start == previous.Span.Start && d.Code < previous.Code {
		t.Fatalf("diagnostics unsorted: %+v then %+v", previous, d)
	}
}

func onRuneBoundary(src []byte, offset int) bool {
	return offset == 0 || offset == len(src) || utf8.RuneStart(src[offset])
}
