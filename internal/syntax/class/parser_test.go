package class_test

import (
	"encoding/json"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/class"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/class"
)

func TestNewlineSeparatesRelationTarget(t *testing.T) {
	for _, ending := range []string{"\n", "\r\n", "\r"} {
		src := []byte("classDiagram" + ending + "Foo ->" + ending + "Bar : x" + ending)
		_, diagnostics := parser.Parse(src, nil)
		if len(diagnostics) != 1 {
			t.Fatalf("ending %q: expected one incomplete-relation diagnostic, got %v", ending, diagnostics)
		}
		d := diagnostics[0]
		if d.Code != "class/unexpected-token" || d.Message != "unexpected "+ending+", expected one of: DOTTED_LINE, LINE" {
			t.Fatalf("ending %q: unexpected diagnostic: %v", ending, d)
		}
		start := len("classDiagram") + len(ending) + len("Foo ->")
		want := source.Span{Start: start, End: start + len(ending)}
		if d.Span != want || string(src[d.Span.Start:d.Span.End]) != ending {
			t.Fatalf("ending %q: diagnostic must cover only the separating newline: %v, want %v", ending, d.Span, want)
		}
	}
}

func TestNamespaceRecoveryExpectedStatements(t *testing.T) {
	src := []byte("classDiagram\nnamespace N {\nA --> B\nclass C\n}\n")
	_, diagnostics := parser.Parse(src, nil)
	if len(diagnostics) != 1 || diagnostics[0].Message != "unexpected A, expected one of: CLASS, NAMESPACE, NOTE, NOTE_FOR" {
		t.Fatalf("unexpected namespace recovery: %v", diagnostics)
	}
}

func TestStatements(t *testing.T) {
	for _, body := range []string{
		"class Animal", "class Animal {\n+String name\n+eat() void\n}",
		"Animal <|-- Dog : inherits", "A\"1\"o--\"many\"B", "A..>B",
		"namespace Animals {\nclass Dog\n}", "note for Animal \"hello\"",
		"class Box~T~[\"Container\"]", "class A\n<<interface>> A", "class A\nA : +run()",
		"classDef default fill:red", "class A\ncssClass \"A\" red",
		"class A\nlink A \"https://example.com\"", "class A\nclick A call invoke(\"a,b\", c) \"tooltip\"",
		"direction LR", "accTitle: Diagram", "accDescr {\nDescription\n}", "title harmless",
	} {
		t.Run(body, func(t *testing.T) {
			_, ds := parser.Parse([]byte("classDiagram\n"+body+"\n"), nil)
			if len(ds) > 0 {
				t.Fatal(ds)
			}
		})
	}
}

func TestDiagnostics(t *testing.T) {
	cases := []struct{ body, code string }{
		{"@ nonsense", "class/unknown-statement"},
		{"A -> B", "class/unexpected-token"},
		{"class A {\n+f()", "class/unterminated"},
		{"note \"broken", "class/unterminated"},
		{"class A {\n{bad}\n}", "class/nested-member-block"},
		{"class A {}; class B", "class/unexpected-token"},
		{"namespace N {\nA --> B\n}", "class/unexpected-token"},
		{"class A:::red {}", "class/unexpected-token"},
	}
	for _, c := range cases {
		t.Run(c.body, func(t *testing.T) {
			src := []byte("classDiagram\n" + c.body)
			_, ds := parser.Parse(src, nil)
			assertDiagnostic(t, src, ds, c.code)
		})
	}
}

func TestLabelTextAcceptsEveryCharacterButColonAndSemicolon(t *testing.T) {
	for _, body := range []string{
		"A : \u0301x", "A : ★ y", "A : x \u0301 y", "A : x\x01y",
		"A --> B : \u0301x", "A --> B : ★ y", "A --> B : x \u0301 y",
	} {
		t.Run(body, func(t *testing.T) {
			_, ds := parser.Parse([]byte("classDiagram\n"+body+"\n"), nil)
			if len(ds) > 0 {
				t.Fatal(ds)
			}
		})
	}
	for _, body := range []string{"A : x : y", "A : x ; y", "A --> B : x : y", "A --> B : x ; y"} {
		t.Run(body, func(t *testing.T) {
			src := []byte("classDiagram\n" + body + "\n")
			_, ds := parser.Parse(src, nil)
			assertDiagnostic(t, src, ds, "class/unexpected-token")
		})
	}
}

func assertDiagnostic(t *testing.T, src []byte, ds []diag.Diagnostic, code string) {
	t.Helper()
	found := false
	for _, d := range ds {
		found = found || d.Code == code
		if d.Span.Start < 0 || d.Span.End > len(src) || d.Span.End < d.Span.Start {
			t.Fatal(d)
		}
	}
	if !found {
		t.Fatal(code, ds)
	}
}

func TestStatementSpans(t *testing.T) {
	src := []byte("classDiagram\nclass A {\n+x\n}\nA --> B : relates\n")
	f, ds := parser.Parse(src, nil)
	if len(ds) > 0 {
		t.Fatal(ds)
	}
	if f.Statements[0].Span != (source.Span{Start: 13, End: 27}) {
		t.Fatal(f.Statements[0].Span)
	}
	if f.Statements[0].Class.Members.Tokens[0].Span != (source.Span{Start: 23, End: 25}) {
		t.Fatal(f.Statements[0].Class.Members)
	}
	if f.Statements[1].Relation.To.Span != (source.Span{Start: 34, End: 35}) {
		t.Fatal(f.Statements[1].Relation.To)
	}
}

type verdict struct {
	Accept bool `json:"accept"`
}

func TestCorpus(t *testing.T) {
	var verdicts map[string]verdict
	readJSON(t, "corpus/verdicts.json", &verdicts)
	var divergences []struct {
		Path string `json:"path"`
	}
	readJSON(t, "corpus/divergences.json", &divergences)
	skip := make(map[string]bool)
	for _, row := range divergences {
		skip[row.Path] = true
	}
	var paths []string
	for path := range verdicts {
		if strings.HasPrefix(path, "corpus/class/") && !skip[path] {
			paths = append(paths, path)
		}
	}
	slices.Sort(paths)
	for _, path := range paths {
		checkCorpusFile(t, path, verdicts[path])
	}
	t.Logf("compared %d class fixtures", len(paths))
}

func readJSON(t *testing.T, path string, target any) {
	t.Helper()
	raw, err := os.ReadFile(filepath.Join("../../..", path))
	if err != nil {
		t.Fatal(err)
	}
	if err = json.Unmarshal(raw, target); err != nil {
		t.Fatal(err)
	}
}

func checkCorpusFile(t *testing.T, path string, expected verdict) {
	t.Helper()
	src, err := os.ReadFile(filepath.Join("../../..", path))
	if err != nil {
		t.Fatal(err)
	}
	p := syntax.Preprocess(src)
	f, ds := parser.Parse(src, p.Removed)
	_, semantic := model.Resolve(src, f)
	ds = append(ds, semantic...)
	ds = append(ds, p.Diags...)
	accept := true
	for _, d := range ds {
		if d.Severity == diag.SeverityError {
			accept = false
		}
	}
	if accept != expected.Accept {
		t.Errorf("%s: accept=%v want=%v diagnostics=%v", path, accept, expected.Accept, ds)
	}
}
