package treeview_test

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/treeview"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/treeview"
)

func TestBareCommentIndentationPreservesResolvedTree(t *testing.T) {
	for _, ending := range []struct{ name, text string }{
		{"LF", "\n"}, {"CRLF", "\r\n"}, {"CR", "\r"},
	} {
		for _, indent := range []struct{ name, text string }{
			{"none", ""}, {"SP", " "}, {"HT", "\t"}, {"SPHT", " \t"},
		} {
			t.Run(ending.name+"/"+indent.name, func(t *testing.T) {
				nl := ending.text
				comment := indent.text + "%%"
				src := "treeView-beta" + nl + comment + nl +
					"    \"packages\"" + nl + " \t" + nl + comment + nl +
					"        \"mermaid\"" + nl + comment + nl +
					"            \"src\"" + nl + "        \"parser\"" + nl + comment
				checkResolvedCommentTree(t, src)
			})
		}
	}
}

func checkResolvedCommentTree(t *testing.T, src string) {
	t.Helper()
	tv, m := resolveCommentTree(t, src)
	if len(tv.Nodes) != 4 || len(m.Nodes) != 5 {
		t.Fatalf("got %d parsed and %d resolved nodes", len(tv.Nodes), len(m.Nodes))
	}
	wantNames := []string{"packages", "mermaid", "src", "parser"}
	wantParents := []int{0, 1, 2, 1}
	wantLevels := []int{4, 8, 12, 8}
	wantDepths := []int{1, 2, 3, 2}
	for i, name := range wantNames {
		node := m.Nodes[i+1]
		if node.Name != name || node.Parent != wantParents[i] ||
			node.Level != wantLevels[i] || node.Depth != wantDepths[i] {
			t.Fatalf("node %d: %+v", i, node)
		}
		checkCommentNodeSpans(t, src, tv, m, i)
	}
}

func resolveCommentTree(t *testing.T, src string) (*parser.TreeView, *model.Model) {
	t.Helper()
	document := []byte(src)
	prep := syntax.Preprocess(document)
	tv, parsed := parser.Parse(document, prep.Removed)
	if len(prep.Diags) != 0 || len(parsed) != 0 {
		t.Fatalf("preprocess: %v; parse: %v", prep.Diags, parsed)
	}
	m, resolved := model.Resolve(document, tv)
	if len(resolved) != 0 {
		t.Fatalf("resolve: %v", resolved)
	}
	return tv, m
}

func checkCommentNodeSpans(t *testing.T, src string, tv *parser.TreeView, m *model.Model, i int) {
	t.Helper()
	node := m.Nodes[i+1]
	quoted := `"` + node.Name + `"`
	start := strings.Index(src, quoted)
	wantName := source.Span{Start: start, End: start + len(quoted)}
	wantNode := source.Span{Start: start - node.Level, End: wantName.End}
	if tv.Nodes[i].Name.Span != wantName || tv.Nodes[i].Span != wantNode ||
		node.Span != wantNode {
		t.Fatalf("node %d spans: name %v, parsed %v, resolved %v; want %v, %v",
			i, tv.Nodes[i].Name.Span, tv.Nodes[i].Span, node.Span, wantName, wantNode)
	}
	if tv.Nodes[i].Indent == nil ||
		tv.Nodes[i].Indent.Span != (source.Span{Start: wantNode.Start, End: start}) {
		t.Fatalf("node %d indentation: %+v", i, tv.Nodes[i].Indent)
	}
}

func FuzzTreeview(f *testing.F) {
	seedCorpus(f)
	f.Fuzz(func(t *testing.T, src []byte) {
		document, _ := source.RepairUTF8(src)
		prep := syntax.Preprocess(document)
		tv, parsed := parser.Parse(document, prep.Removed)
		_, resolved := model.Resolve(document, tv)
		checkSpans(t, "parser", document, parsed)
		checkSpans(t, "resolver", document, resolved)
		checkTree(t, document, tv)
	})
}

func seedCorpus(f *testing.F) {
	paths, err := filepath.Glob(filepath.Join("..", "..", "..", "corpus", "treeview", "*", "*.mmd"))
	if err != nil {
		f.Fatal(err)
	}
	for _, path := range paths {
		src, err := os.ReadFile(path)
		if err != nil {
			f.Fatal(err)
		}
		f.Add(src)
	}
	for _, s := range []string{
		"treeView-beta",
		"treeView-beta\n  \"never closed",
		"treeView-beta\naccDescr {\nnever closed",
		"treeView-beta\n├──\n",
		"treeView-beta\n├── a\n  b\n",
		"treeView-beta\n  ├── a\n  │   └── b ## d :::x icon(p:q)\n",
		"---\nconfig:\n  treeView:\n    rowIndent: 3\n---\n%% c\ntreeView-beta\r\n title t\r\n a\r b\n\ta :::x\n",
		"treeView-beta\n\u00a0a\u2028\n\t\tb icon()\n",
	} {
		f.Add([]byte(s))
	}
}

func checkSpans(t *testing.T, stage string, document []byte, ds []diag.Diagnostic) {
	t.Helper()
	for _, d := range ds {
		if d.Span.Start < 0 || d.Span.End < d.Span.Start || d.Span.End > len(document) {
			t.Fatalf("%s diagnostic %s has span %v for %d bytes", stage, d.Code, d.Span, len(document))
		}
		if !onBoundary(document, d.Span.Start) || !onBoundary(document, d.Span.End) {
			t.Fatalf("%s diagnostic %s span %v splits a UTF-8 sequence", stage, d.Code, d.Span)
		}
	}
}

func checkTree(t *testing.T, document []byte, tv *parser.TreeView) {
	t.Helper()
	for _, node := range tv.Nodes {
		span := node.Span
		if span.Start < 0 || span.End < span.Start || span.End > len(document) {
			t.Fatalf("node span %v for %d bytes", span, len(document))
		}
		if !onBoundary(document, span.Start) || !onBoundary(document, span.End) {
			t.Fatalf("node span %v splits a UTF-8 sequence", span)
		}
	}
}

func onBoundary(text []byte, at int) bool {
	return at == len(text) || utf8.RuneStart(text[at])
}
