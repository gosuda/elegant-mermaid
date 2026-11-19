package block_test

import (
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/block"
)

func parse(src string) (*parser.Start, []diag.Diagnostic) {
	document, _ := source.RepairUTF8([]byte(src))
	return parser.Parse(document, syntax.Preprocess(document).Removed)
}

func TestCorpusAccepted(t *testing.T) {
	paths, err := filepath.Glob(filepath.Join("..", "..", "..", "corpus", "block", "*", "*.mmd"))
	if err != nil || len(paths) == 0 {
		t.Fatalf("corpus glob: %v, %d files", err, len(paths))
	}
	for _, path := range paths {
		src, err := os.ReadFile(path)
		if err != nil {
			t.Fatal(err)
		}
		if _, ds := parse(string(src)); len(ds) != 0 {
			t.Errorf("%s: %s: %s", path, ds[0].Code, ds[0].Message)
		}
	}
}

func TestAcceptedForms(t *testing.T) {
	for name, src := range map[string]string{
		"size on first node":    "block\n  A:2 --> B\n",
		"chain":                 "block\n  A-->B-->C\n",
		"keyword prefixed ids":  "block\n  blockchain\n  block1\n  endpoint\n  default1\n",
		"composite with size":   "block\n  columns 3\n  block:g:2\n    A\n  end\n",
		"labelled composite":    "block\n  block:g[\"T\"]:2\n    A\n  end\n",
		"nested anonymous":      "block\n  block\n    block\n      A\n    end\n  end\n",
		"all arrow spellings":   "block\n  A --- B\n  C --x D\n  G <--> H\n  I ===> J\n  K -.-> L\n",
		"marker letters as ids": "block\n  E o--o F\n",
		"tilde as identifier":   "block\n  M ~~~ N\n",
		"labelled edges":        "block\n  A -- \"hello\" --> B\n  C == \"x\" ==> D\n  E -. \"y\" .-> F\n",
		"empty multiline desc":  "block\n  accDescr {}\n  A\n",
		"class statements":      "block\n  A B\n  classDef foo fill:#f96,color:#fff;\n  class A,B foo\n  style A fill:#00f\n",
		"lowercase default":     "block\n  A\n  classDef default fill:#f96\n",
		"mismatched pair":       "block\n  a(\"1\"] b[\"2\")\n",
		"stray bracket in id":   "block\n  a]\n",
		"huge size":             "block\n  a:99999999999\n",
		"arrow directions":      "block\n  A<[\"x\"]>(x)\n  B<[\"y\"]>(y, up)\n  C<[\"z\"]>(right,left,down)\n",
		"block-beta header":     "block-beta\n  A\n",
		"style at end of input": "block\n  A\n  style A",
	} {
		if _, ds := parse(src); len(ds) != 0 {
			t.Errorf("%s: %s: %s", name, ds[0].Code, ds[0].Message)
		}
	}
}

func TestRejectedForms(t *testing.T) {
	for name, tc := range map[string]struct{ src, code string }{
		"empty label":            {"block\n  A[\"\"]\n", "block/unexpected-token"},
		"unquoted label":         {"block\n  A[foo]\n", "block/unexpected-token"},
		"space inside shape":     {"block\n  A[ \"x\" ]\n", "block/unexpected-token"},
		"size on link target":    {"block\n  A --> B:2\n", "block/unexpected-token"},
		"double size":            {"block\n  A:2:3\n", "block/unexpected-token"},
		"upper case default":     {"block\n  A\n  classDef DEFAULT fill:#f96\n", "block/unexpected-token"},
		"stray end":              {"block\n  A\n  end\n", "block/unknown-statement"},
		"unknown direction":      {"block\n  A<[\"x\"]>(sideways)\n", "block/unexpected-token"},
		"empty direction list":   {"block\n  A<[\"x\"]>()\n", "block/unexpected-token"},
		"markdown label":         {"block\n  A[\"`x`\"]\n", "block/unexpected-token"},
		"colon identifier":       {"block\n  a:b\n", "block/unknown-statement"},
		"empty document":         {"block\n", "block/unexpected-token"},
		"empty composite":        {"block\n  block\n  end\n", "block/unexpected-token"},
		"accessibility title":    {"block\n  accTitle: x\n  A\n", "block/unknown-statement"},
		"unterminated composite": {"block\n  block\n    A\n", "block/unterminated"},
		"unterminated string":    {"block\n  A[\"x\n", "block/unterminated"},
		"unterminated shape":     {"block\n  A[", "block/unterminated"},
		"unterminated arrow":     {"block\n  A<[\"x\"]>(right\n", "block/unterminated"},
		"unterminated link":      {"block\n  A -- \"x\n", "block/unterminated"},
	} {
		_, ds := parse(tc.src)
		if len(ds) == 0 || ds[0].Code != tc.code {
			t.Errorf("%s: want %s, got %v", name, tc.code, ds)
		}
	}
}

func TestUnexpectedTokenMessage(t *testing.T) {
	_, ds := parse("block\n  A[foo]\n")
	if len(ds) != 1 {
		t.Fatalf("want one diagnostic, got %v", ds)
	}
	if want := "unexpected f, expected one of: STR"; ds[0].Message != want {
		t.Errorf("message %q, want %q", ds[0].Message, want)
	}
	if ds[0].Span.Start != 10 {
		t.Errorf("span %v, want start 10", ds[0].Span)
	}
}

func TestRecoveryKeepsLaterStatements(t *testing.T) {
	start, ds := parse("block\n  A[foo]\n  B\n  C\n")
	if len(ds) == 0 {
		t.Fatal("want a diagnostic")
	}
	if got := len(start.Document.Statements); got != 2 {
		t.Errorf("recovered %d statements, want 2", got)
	}
}

func TestRecoveryStopsBeforeEnd(t *testing.T) {
	start, ds := parse("block\n  block\n    A[foo] end\n  B\n")
	if len(ds) != 1 {
		t.Fatalf("diagnostics %v", ds)
	}
	if got := len(start.Document.Statements); got != 2 {
		t.Errorf("root statements %d, want 2", got)
	}
}

func TestNestingLimit(t *testing.T) {
	src := "block\n" + strings.Repeat("block\n", 70) + "A\n" + strings.Repeat("end\n", 70)
	_, ds := parse(src)
	if len(ds) != 1 || ds[0].Code != "limit/nesting-depth" {
		t.Fatalf("diagnostics %v", ds)
	}
}

func TestSpansStayOnTokens(t *testing.T) {
	start, ds := parse("block\n  A[\"x\"]:2 --> B\n")
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	node := start.Document.Statements[0].Kind.(*parser.NodeStatement)
	if got := node.Size.Span; got != (source.Span{Start: 14, End: 16}) {
		t.Errorf("size span %v", got)
	}
	if got := node.Links[0].Link.End.Span; got != (source.Span{Start: 17, End: 20}) {
		t.Errorf("link span %v", got)
	}
}
