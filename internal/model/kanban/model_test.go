package kanban

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/kanban"
)

func resolve(src string) (*Model, []diag.Diagnostic) {
	text := []byte(src)
	start, parsed := syn.Parse(text, syntax.Preprocess(text).Removed)
	model, resolved := Resolve(text, start)
	return model, append(parsed, resolved...)
}

func codes(ds []diag.Diagnostic) []string {
	out := make([]string, len(ds))
	for i, d := range ds {
		out[i] = d.Code
	}
	return out
}

func ids(model *Model, indexes []int) []string {
	out := make([]string, len(indexes))
	for i, index := range indexes {
		out[i] = model.Nodes[index].ID
	}
	return out
}

func TestSectionsAndCards(t *testing.T) {
	model, ds := resolve("kanban\n  todo[To Do]\n    a[Task A]\n    b[Task B]\n  done[Done]\n    c[Task C]\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"todo", "done"}, ids(model, model.Sections))
	columns := model.Columns()
	require.Len(t, columns, 2)
	require.Equal(t, []string{"a", "b"}, ids(model, columns[0].Cards))
	require.Equal(t, []string{"c"}, ids(model, columns[1].Cards))
	require.Equal(t, "Task A", model.Nodes[columns[0].Cards[0]].Label)
	require.Equal(t, TypeRect, model.Nodes[0].Type)
	require.Equal(t, 4, model.Nodes[columns[0].Cards[0]].Level)
}

func TestSameIndentationMakesEveryNodeASection(t *testing.T) {
	model, ds := resolve("kanban\n  a[A]\n  b[B]\n  c[C]\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"a", "b", "c"}, ids(model, model.Sections))
	for _, column := range model.Columns() {
		require.Empty(t, column.Cards)
	}
}

func TestDeeperIndentationAttachesToLatestSection(t *testing.T) {
	model, ds := resolve("kanban\n  s[S]\n      a[A]\n    b[B]\n          c[C]\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"a", "b", "c"}, ids(model, model.Columns()[0].Cards))
}

func TestRepeatedSectionIDsShareCards(t *testing.T) {
	model, ds := resolve("kanban\n  s[One]\n    a[A]\n  s[Two]\n    b[B]\n")
	require.Empty(t, ds)
	columns := model.Columns()
	require.Equal(t, []string{"a", "b"}, ids(model, columns[0].Cards))
	require.Equal(t, []string{"a", "b"}, ids(model, columns[1].Cards))
}

func TestFirstLevelIsTheSectionLevel(t *testing.T) {
	model, ds := resolve("kanban\n      s[S]\n      t[T]\n        a[A]\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"s", "t"}, ids(model, model.Sections))
	require.Equal(t, 6, model.Nodes[0].Level)
}

func TestItemsWithoutSectionRejectsOnNextInsertion(t *testing.T) {
	src := "kanban\n    s[S]\n  a[A]\n    t[T]\n"
	model, ds := resolve(src)
	require.Equal(t, []string{"kanban/items-without-section"}, codes(ds))
	require.Equal(t, "items without section detected at A", ds[0].Message)
	require.Equal(t, "  ", src[ds[0].Span.Start:ds[0].Span.End])
	require.Len(t, model.Nodes, 2)
}

func TestItemsWithoutSectionUsesFirstTokenAtLevelZero(t *testing.T) {
	src := "kanban\n  s[S]\nzero[Z]\n  t[T]\n"
	_, ds := resolve(src)
	require.Equal(t, []string{"kanban/items-without-section"}, codes(ds))
	require.Equal(t, "zero", src[ds[0].Span.Start:ds[0].Span.End])
}

func TestBelowSectionLevelCardIsRetainedAtEndOfInput(t *testing.T) {
	model, ds := resolve("kanban\n    s[S]\n  a[A]\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"a"}, ids(model, model.Columns()[0].Cards))
}

func TestLowerLevelErrorIsReportedOncePerOffender(t *testing.T) {
	_, ds := resolve("kanban\n    s[S]\n  a[A]\n    t[T]\n    u[U]\n")
	require.Equal(t, []string{"kanban/items-without-section"}, codes(ds))
}

func TestTabsCountAsOneCharacter(t *testing.T) {
	model, ds := resolve("kanban\n\ts[S]\n\t\ta[A]\n")
	require.Empty(t, ds)
	require.Equal(t, 1, model.Nodes[0].Level)
	require.Equal(t, 2, model.Nodes[1].Level)
}

func TestNodeTypesAndStoredFields(t *testing.T) {
	model, ds := resolve("kanban\n  a\n  b[x]\n  c(x)\n  d((x))\n  e))x((\n  f{{x}}\n  g)x(\n")
	require.Empty(t, ds)
	want := []NodeType{TypeDefault, TypeRect, TypeRoundedRect, TypeCircle, TypeBang, TypeHexagon, TypeCloud}
	for i, node := range model.Nodes {
		require.Equal(t, want[i], node.Type, node.ID)
	}
	require.Equal(t, int64(10), model.Nodes[0].Padding)
	require.Equal(t, int64(20), model.Nodes[1].Padding)
	require.Equal(t, int64(20), model.Nodes[2].Padding)
	require.Equal(t, int64(10), model.Nodes[3].Padding)
	require.Equal(t, int64(20), model.Nodes[5].Padding)
	require.Equal(t, int64(200), model.Nodes[0].Width)
}

func TestIdFallsBackToDescriptionAndKeepsTrailingSpace(t *testing.T) {
	model, ds := resolve("kanban\n  [Only]\n  id  [x]\n")
	require.Empty(t, ds)
	require.Equal(t, "Only", model.Nodes[0].ID)
	require.Equal(t, "Only", model.Nodes[0].Label)
	require.Equal(t, "id  ", model.Nodes[1].ID)
}

func TestEntitiesDecodeInIDAndLabel(t *testing.T) {
	model, ds := resolve("kanban\n  a#35;b[x #quot; y #9731;]\n")
	require.Empty(t, ds)
	require.Equal(t, "a#b", model.Nodes[0].ID)
	require.Equal(t, "x \" y \u2603", model.Nodes[0].Label)
}

func TestLineEndsInTextNormaliseBeforeDecoding(t *testing.T) {
	model, ds := resolve("kanban\r\n  a[x\r\ny]\r\n    c[p\rq]\r\n    ::icon(i\rj)\r\n    :::k\r\n")
	require.Empty(t, ds)
	require.Equal(t, "x\ny", model.Nodes[0].Label)
	require.Equal(t, "p\nq", model.Nodes[1].Label)
	require.Equal(t, "i\nj", model.Nodes[1].Icon)
}

func TestMetadataFields(t *testing.T) {
	src := "kanban\n  s[S]\n    a[A]@{ ticket: MC-2036, assigned: 'knsv', priority: 'Very High', icon: 7, label: \"New\", extra: 1 }\n"
	model, ds := resolve(src)
	require.Empty(t, ds)
	card := model.Nodes[1]
	require.Equal(t, "MC-2036", card.Ticket)
	require.Equal(t, "knsv", card.Assigned)
	require.Equal(t, "Very High", card.Priority)
	require.True(t, card.HasPriority)
	require.Equal(t, "7", card.Icon)
	require.Equal(t, "New", card.Label)
}

func TestMetadataFalsyValuesLeaveFieldsUnset(t *testing.T) {
	model, ds := resolve("kanban\n  a[A]@{ ticket: 0, assigned: false, priority: null, icon: '', label: 0.0 }\n")
	require.Empty(t, ds)
	node := model.Nodes[0]
	require.Empty(t, node.Ticket+node.Assigned+node.Icon)
	require.False(t, node.HasPriority)
	require.Equal(t, "A", node.Label)
}

func TestMetadataJavaScriptConversions(t *testing.T) {
	model, ds := resolve("kanban\n  a[A]@{ ticket: 007, assigned: 1.50, icon: [x, y], label: true }\n  b[B]@{\n    priority:\n      k: v\n}\n")
	require.Empty(t, ds)
	node := model.Nodes[0]
	require.Equal(t, "7", node.Ticket)
	require.Equal(t, "1.5", node.Assigned)
	require.Equal(t, "x,y", node.Icon)
	require.Equal(t, "true", node.Label)
	require.Equal(t, "[object Object]", model.Nodes[1].Priority)
	require.True(t, model.Nodes[1].HasPriority)
}

func TestMetadataConversionFailureRejects(t *testing.T) {
	src := "kanban\n  a[A]@{\n    ticket:\n      toString: 1\n}\n"
	model, ds := resolve(src)
	require.Equal(t, []string{"kanban/malformed-metadata"}, codes(ds))
	require.Equal(t, "invalid node metadata", ds[0].Message)
	require.Equal(t, "@{\n    ticket:\n      toString: 1\n}", src[ds[0].Span.Start:ds[0].Span.End])
	require.Empty(t, model.Nodes)
}

func TestMetadataBlockForm(t *testing.T) {
	model, ds := resolve("kanban\n  a[A]@{\n    ticket: T1\n    assigned: me\n  }\n")
	require.Empty(t, ds)
	require.Equal(t, "T1", model.Nodes[0].Ticket)
	require.Equal(t, "me", model.Nodes[0].Assigned)
}

func TestMetadataQuotedLineBreakBecomesBr(t *testing.T) {
	model, ds := resolve("kanban\n  a[A]@{ label: \"x\n   y\" }\n")
	require.Empty(t, ds)
	require.Equal(t, "x<br/>y", model.Nodes[0].Label)
}

func TestMalformedMetadataRejectsWithoutInsertion(t *testing.T) {
	for _, src := range []string{
		"kanban\n  a[A]@{ ticket: [ }\n",
		"kanban\n  a[A]@{ ticket: 1, ticket: 2 }\n",
		"kanban\n  a[A]@{\n}\n",
		"kanban\n  a[A]@{\n  # only a comment\n}\n",
		"kanban\n  a[A]@{ null }\n  b@{ ~ }\n",
	} {
		model, ds := resolve(src)
		require.Contains(t, codes(ds), "kanban/malformed-metadata", src)
		require.Empty(t, model.Nodes, src)
	}
}

func TestScalarMetadataDocumentIsIgnored(t *testing.T) {
	model, ds := resolve("kanban\n  a[A]@{\n  just text\n}\n")
	require.Empty(t, ds)
	require.Len(t, model.Nodes, 1)
}

func TestInvalidShapeRejectsWithValueSpan(t *testing.T) {
	for src, want := range map[string]string{
		"kanban\n  a[A]@{ shape: kanbanItem }\n":         "kanbanItem",
		"kanban\n  a[A]@{ shape: 'two_words', x: 1 }\n":  "'two_words'",
		"kanban\n  a[A]@{ x: 1, shape: 5 }\n":            "5",
		"kanban\n  a[A]@{\n    shape: Upper # note\n}\n": "Upper",
	} {
		model, ds := resolve(src)
		require.Equal(t, []string{"kanban/invalid-shape"}, codes(ds), src)
		require.Equal(t, want, src[ds[0].Span.Start:ds[0].Span.End], src)
		require.Empty(t, model.Nodes, src)
	}
	_, ds := resolve("kanban\n  a[A]@{ shape: 5 }\n")
	require.Equal(t, "invalid shape 5; shape names must be lowercase without underscores", ds[0].Message)
}

func TestLowercaseAndFalsyShapesAreIgnored(t *testing.T) {
	model, ds := resolve("kanban\n  a[A]@{ shape: rect }\n  b[B]@{ shape: '' }\n  c[C]@{ shape: false }\n")
	require.Empty(t, ds)
	require.Len(t, model.Nodes, 3)
}

func TestDecorationsModifyLastNode(t *testing.T) {
	model, ds := resolve("kanban\n  s[S]\n    ::icon(fa fa-x)\n  :::big #35;\n        ::icon(fa fa-y)\n")
	require.Empty(t, ds)
	require.Equal(t, "fa fa-y", model.Nodes[0].Icon)
	require.Equal(t, "big #", model.Nodes[0].Class)
}

func TestDecorationWithoutNodeRejects(t *testing.T) {
	src := "kanban\n  ::icon(x)\n  s[S]\n"
	model, ds := resolve(src)
	require.Equal(t, []string{"kanban/decoration-without-node"}, codes(ds))
	require.Equal(t, "decoration requires a preceding node", ds[0].Message)
	require.Equal(t, "::icon(x)", src[ds[0].Span.Start:ds[0].Span.End])
	require.Len(t, model.Nodes, 1)
}

func TestConfigKeys(t *testing.T) {
	model, ds := resolve("---\nconfig:\n  kanban:\n    sectionWidth: 250\n    padding: 4\n  mindmap:\n    padding: 6\n    maxNodeWidth: 300\n---\nkanban\n  a[A]\n")
	require.Empty(t, ds)
	config := model.Config
	require.True(t, config.SectionWidthSet)
	require.Equal(t, int64(250), config.SectionWidth)
	require.True(t, config.PaddingSet)
	require.Equal(t, int64(4), config.Padding)
	require.Equal(t, int64(12), model.Nodes[0].Padding)
	require.Equal(t, int64(300), model.Nodes[0].Width)
}

func TestConfigIgnoresZeroWidthDecimalsAndNegatives(t *testing.T) {
	model, _ := resolve("%%{init: {\"kanban\": {\"sectionWidth\": 0, \"padding\": 1.5}}}%%\nkanban\n  a\n")
	require.False(t, model.Config.SectionWidthSet)
	require.False(t, model.Config.PaddingSet)
	model, _ = resolve("%%{init: {\"kanban\": {\"padding\": -2}}}%%\nkanban\n  a\n")
	require.False(t, model.Config.PaddingSet)
}

func TestEmptyDocumentHasNoSections(t *testing.T) {
	model, ds := resolve("kanban\n\n")
	require.Empty(t, ds)
	require.Empty(t, model.Sections)
	require.Empty(t, model.Columns())
}

func TestJavaScriptNumberText(t *testing.T) {
	for text, want := range map[string]string{
		"0":                      "0",
		"-0":                     "0",
		"007":                    "7",
		"+5":                     "5",
		"1.50":                   "1.5",
		"0.000001":               "0.000001",
		"0.0000001":              "1e-7",
		"123456789012345678901":  "123456789012345680000",
		"1234567890123456789012": "1.2345678901234568e+21",
		"-12.25":                 "-12.25",
	} {
		require.Equal(t, want, jsNumber(number(text)), text)
	}
	huge := make([]byte, 400)
	for i := range huge {
		huge[i] = '9'
	}
	require.Equal(t, "Infinity", jsNumber(number(string(huge))))
}
