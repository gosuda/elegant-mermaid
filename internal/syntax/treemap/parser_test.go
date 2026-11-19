package treemap

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
)

func parse(src string) (*Treemap, []diag.Diagnostic) {
	return Parse([]byte(src), nil)
}

func codes(ds []diag.Diagnostic) []string {
	out := make([]string, len(ds))
	for i, d := range ds {
		out[i] = d.Code
	}
	return out
}

var oracleVerdicts = []struct {
	name   string
	source string
	accept bool
}{
	{"trailing-space-section", "treemap-beta\n\"A\"  \n  \"B\": 1\n", false},
	{"trailing-space-leaf", "treemap-beta\n\"A\"\n  \"B\": 1  \n  \"C\": 2\n", false},
	{"tab-indent", "treemap-beta\n\"A\"\n\t\"B\": 1\n", true},
	{"empty", "treemap-beta\n", true},
	{"no-newline-eof", "treemap-beta\n\"A\"\n  \"B\": 1", true},
	{"space-before-colon", "treemap-beta\n\"A\"\n  \"B\" : 1\n", true},
	{"comma-sep", "treemap-beta\n\"A\"\n  \"B\", 1\n", true},
	{"two-roots", "treemap-beta\n\"A\"\n\"B\"\n", true},
	{"indented-roots", "treemap-beta\n  \"A\"\n  \"B\"\n", true},
	{"indented-roots2", "treemap-beta\n  \"A\"\n \"B\"\n", true},
	{"indent-first-then-none", "treemap-beta\n  \"A\"\n\"B\"\n", true},
	{"single-quote", "treemap-beta\n'A'\n  'B': 3\n", true},
	{"title", "treemap-beta\ntitle My T\n\"A\"\n  \"B\": 3\n", true},
	{"title-indent", "treemap-beta\n  title My T\n\"A\"\n  \"B\": 3\n", true},
	{"accTitle", "treemap-beta\naccTitle: x\naccDescr: y\n\"A\"\n  \"B\": 3\n", true},
	{"comma-number", "treemap-beta\n\"A\"\n  \"B\": 1,234.5\n", true},
	{"underscore-number", "treemap-beta\n\"A\"\n  \"B\": 1_2\n", true},
	{"bad-number", "treemap-beta\n\"A\"\n  \"B\": _\n", false},
	{"dots-number", "treemap-beta\n\"A\"\n  \"B\": ...\n", true},
	{"dots-number2", "treemap-beta\n\"A\"\n  \"B\": 1.2.3\n", true},
	{"two-newlines", "treemap-beta\n\n\n\"A\"\n\n  \"B\": 3\n", true},
	{"semicolon", "treemap-beta\n\"A\"; \"B\"\n", false},
	{"leaf-no-number", "treemap-beta\n\"A\"\n  \"B\":\n", false},
	{"classdef-1char", "treemap-beta\n\"A\"\nclassDef c fill:red\n", false},
	{"classdef-2char", "treemap-beta\n\"A\"\nclassDef cc fill:red\n", true},
	{"selector-1char", "treemap-beta\n\"A\":::c\n", true},
	{"multi-selector", "treemap-beta\n\"A\":::c:::d\n", false},
	{"same-line", "treemap-beta \"A\"\n", true},
	{"trailing-comment", "treemap-beta\n\"A\" %% x\n  \"B\": 3\n", false},
	{"leaf-child", "treemap-beta\n\"A\"\n  \"B\": 3\n    \"C\": 4\n", true},
	{"zero", "treemap-beta\n\"A\"\n  \"B\": 0\n", true},
	{"multiline-name", "treemap-beta\n\"A\nB\"\n  \"C\": 3\n", true},
	{"lead-space-header", "  treemap-beta\n\"A\"\n  \"B\": 1\n", true},
	{"lead-newlines", "\n\ntreemap-beta\n\"A\"\n  \"B\": 1\n", true},
	{"trailing-space-eof", "treemap-beta\n\"A\"\n  \"B\": 1  ", false},
	{"trailing-space-header", "treemap-beta  \n\"A\"\n  \"B\": 1\n", true},
	{"trailing-space-then-unindented", "treemap-beta\n\"A\"  \n\"B\"\n", true},
	{"title-after-leaf", "treemap-beta\n\"A\"\n  \"B\": 1 title X\n", true},
	{"title-trailing", "treemap-beta\n\"A\"\n  \"B\": 1\ntitle X  \n  \"C\": 2\n", true},
	{"title-nospace", "treemap-beta\ntitleX\n", false},
	{"title-only", "treemap-beta\ntitle\n\"A\"\n", true},
	{"acc-multi", "treemap-beta\naccDescr {\n a\n b\n}\n\"A\"\n", true},
	{"acc-multi-brace-first", "treemap-beta\naccDescr{ a }\n\"A\"\n", true},
	{"treemap-twice", "treemap-beta\n\"A\"\ntreemap-beta\n", false},
	{"true", "treemap-beta\ntrue\n", false},
	{"number-lead-dot", "treemap-beta\n\"A\"\n  \"B\": .5\n", true},
	{"number-comma-only", "treemap-beta\n\"A\"\n  \"B\": ,,\n", false},
	{"neg", "treemap-beta\n\"A\"\n  \"B\": -5\n", false},
	{"plus", "treemap-beta\n\"A\"\n  \"B\": +5\n", false},
	{"name-empty", "treemap-beta\n\"\"\n  \"B\": 5\n", true},
	{"id-selector-digit", "treemap-beta\n\"A\":::1a\n", false},
	{"backslash-quote", "treemap-beta\n\"A\\\"\n  \"B\": 5\n", true},
	{"mixed-quotes", "treemap-beta\n\"A'\n  \"B\": 5\n", false},
	{"crlf", "treemap-beta\r\n\"A\"\r\n  \"B\": 5\r\n", true},
	{"lone-cr", "treemap-beta\r\"A\"\r  \"B\": 5\r", true},
	{"classdef-semicolon", "treemap-beta\n\"A\"\nclassDef cc fill:red;color:blue;\n  \"B\": 5\n", false},
	{"classdef-indented", "treemap-beta\n\"A\"\n  classDef cc fill:red\n", true},
	{"classdef-nostyle", "treemap-beta\n\"A\"\nclassDef cc\n", true},
	{"classdef-nostyle-space", "treemap-beta\n\"A\"\nclassDef cc \n", true},
	{"classdef-then-row", "treemap-beta\nclassDef cc fill:red\n\"A\"\n  \"B\": 1\n", true},
}

func TestUpstreamVerdicts(t *testing.T) {
	for _, c := range oracleVerdicts {
		_, ds := parse(c.source)
		if c.accept {
			require.Empty(t, ds, c.name)
		} else {
			require.NotEmpty(t, ds, c.name)
		}
	}
}

func TestRowShapes(t *testing.T) {
	doc, ds := parse("treemap-beta\ntitle Sales\n\"Root\":::big\n    \"Leaf\": 1,234.5:::small\n  classDef big fill:red\n")
	require.Empty(t, ds)
	require.Equal(t, "treemap-beta", doc.Header.Text)
	require.Len(t, doc.Rows, 4)
	title, ok := doc.Rows[0].(*TitleAndAccessibilities)
	require.True(t, ok)
	require.Equal(t, "TITLE", title.Tokens[0].Kind)
	root := doc.Rows[1].(*TreemapRow)
	require.Nil(t, root.Indent)
	section := root.Item.(*Section)
	require.Equal(t, "Root", section.Name.Value)
	require.Equal(t, "big", section.ClassSelector.Name)
	leafRow := doc.Rows[2].(*TreemapRow)
	require.Equal(t, 4, leafRow.Indent.Width)
	leaf := leafRow.Item.(*Leaf)
	require.Equal(t, "Leaf", leaf.Name.Value)
	require.True(t, leaf.Value.Valid)
	require.Equal(t, "1234.5", leaf.Value.Literal)
	require.Equal(t, "small", leaf.ClassSelector.Name)
	class := doc.Rows[3].(*TreemapRow)
	require.Equal(t, 2, class.Indent.Width)
	require.Equal(t, "big", class.ClassDef.Name)
	require.Equal(t, "fill:red", class.ClassDef.Style)
}

func TestConvertNumber(t *testing.T) {
	for raw, want := range map[string]string{
		"12": "12", "1,234.5": "1234.5", ".5": ".5", "1_2": "1", "1.2.3": "1.2", "5.": "5.", "007": "007",
	} {
		got, valid := convertNumber(raw)
		require.True(t, valid, raw)
		require.Equal(t, want, got, raw)
	}
	for _, raw := range []string{"...", "_", ",,", ".", ""} {
		_, valid := convertNumber(raw)
		require.False(t, valid, raw)
	}
}

func TestDiagnosticCodes(t *testing.T) {
	for source, want := range map[string]string{
		"flowchart TD\n":                                  "treemap/unexpected-token",
		"treemap-beta\n\"A\"\n  \"B\":\n":                 "treemap/unexpected-token",
		"treemap-beta\ntrue\n":                            "treemap/unknown-statement",
		"treemap-beta\n\"A\nB":                            "treemap/unterminated",
		"treemap-beta\naccDescr {\nnever closed":          "treemap/unterminated",
		"treemap-beta\n\"A\":::1a\n":                      "treemap/unexpected-token",
		"treemap-beta\n\"A\"\n  \"B\": 5\n  \"C\": 6  \n": "treemap/unexpected-token",
	} {
		_, ds := parse(source)
		require.NotEmpty(t, ds, source)
		require.Equal(t, want, ds[0].Code, source)
	}
}

func TestRecoveryKeepsLaterRows(t *testing.T) {
	doc, ds := parse("treemap-beta\n\"A\"\n  \"B\": ,\n  \"C\": 6\n")
	require.Equal(t, []string{"treemap/unexpected-token"}, codes(ds))
	var names []string
	for _, row := range doc.Rows {
		if r, ok := row.(*TreemapRow); ok {
			switch item := r.Item.(type) {
			case *Leaf:
				names = append(names, item.Name.Value)
			case *Section:
				names = append(names, item.Name.Value)
			}
		}
	}
	require.Contains(t, names, "C")
}
