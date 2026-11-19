package usecase_test

import (
	"testing"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/usecase"
	"github.com/gosuda/elegant-mermaid/internal/source"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/usecase"
)

func FuzzUsecase(f *testing.F) {
	for _, s := range []string{
		"usecase-beta\nactor A\nA --> B",
		"usecase-beta\nactor A(\"Customer\")@{type:hollow,business:true} <<Staff>>:::x\nA -- \"pays\" --> (Pay)",
		"usecase-beta\nsystemBoundary S[Shop]@{type:package}\n  actor C\n  U(\"Buy\")\nend\nC --> U",
		"usecase-beta\njson J@{\"a\":[1,{\"b\":null}],\"c\":\"\\u0041\"}:::data\nnote for J \"memo\"",
		"usecase-beta\nclassDef hot fill:#f00,stroke-width:2px\nclass A hot\nstyle A stroke:rgb(1\\,2\\,3)",
		"usecase-beta\nA e@..>:include B\nB --|> C\nC o-- \"x\" -- D\ne@{animate:true}",
		"usecase-beta\naccTitle: T\naccDescr {\nbody\n}\ndirection LR",
		"usecase-beta\nA(",
		"usecase-beta\nsystemBoundary S\nA\n",
		"usecase-beta\nA <<",
		"usecase-beta\njson J@{",
	} {
		f.Add([]byte(s))
	}
	f.Fuzz(func(t *testing.T, src []byte) {
		document, _ := source.RepairUTF8(src)
		start, ds := parser.Parse(document, nil)
		if start == nil {
			t.Fatal("nil start")
		}
		checkDiagnostics(t, document, ds)
		_, more := model.Resolve(document, start)
		checkDiagnostics(t, document, more)
	})
}

func checkDiagnostics(t *testing.T, src []byte, ds []diag.Diagnostic) {
	t.Helper()
	for i, d := range ds {
		if !spanWithin(d.Span, len(src)) {
			t.Fatalf("diagnostic span outside source: %+v", d)
		}
		if !onRuneBoundary(src, d.Span.Start) || !onRuneBoundary(src, d.Span.End) {
			t.Fatalf("diagnostic span not on a UTF-8 boundary: %+v", d)
		}
		if i > 0 && outOfOrder(ds[i-1], d) {
			t.Fatalf("diagnostics unsorted: %+v then %+v", ds[i-1], d)
		}
	}
}

func spanWithin(span source.Span, size int) bool {
	return span.Start >= 0 && span.End >= span.Start && span.End <= size
}

func outOfOrder(previous, next diag.Diagnostic) bool {
	return next.Span.Start < previous.Span.Start || next.Span.Start == previous.Span.Start && next.Code < previous.Code
}

func onRuneBoundary(src []byte, offset int) bool {
	return offset == 0 || offset == len(src) || utf8.RuneStart(src[offset])
}
