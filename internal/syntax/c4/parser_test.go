package c4_test

import (
	"reflect"
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/c4"
)

func parse(t *testing.T, src string) *parser.Start {
	t.Helper()
	start, ds := parser.Parse([]byte(src), nil)
	if len(ds) != 0 {
		t.Fatalf("unexpected diagnostics %v", ds)
	}
	if start == nil {
		t.Fatal("nil start")
	}
	return start
}

func TestHeadersRetainSelectedType(t *testing.T) {
	for _, header := range []string{"C4Context", "C4Container", "C4Component", "C4Dynamic", "C4Deployment"} {
		start := parse(t, header+"\nPerson(a,\"A\")\n")
		if start.MermaidDoc == nil {
			t.Fatalf("%s: not a document", header)
		}
		if got := string(start.MermaidDoc.GraphConfig.Header.Raw); got != header {
			t.Fatalf("%s: header %q", header, got)
		}
		items := start.MermaidDoc.GraphConfig.Statements.Items
		if len(items) != 1 || items[0].Diagram == nil || items[0].Diagram.Call == nil {
			t.Fatalf("%s: statements %v", header, items)
		}
		want := header + "\nPerson(a,\"A\")"
		if items[0].Span.Start != len(header)+1 || items[0].Span.End != len(want) {
			t.Fatalf("%s: call span %v", header, items[0].Span)
		}
	}
}

func TestHeaderRequiresLineSeparator(t *testing.T) {
	_, ds := parser.Parse([]byte("C4Context Person(a,\"A\")"), nil)
	if len(ds) != 1 || ds[0].Message != "unexpected Person, expected one of: NEWLINE" {
		t.Fatalf("diagnostics %v", ds)
	}
	if ds[0].Span.Start != 10 || ds[0].Span.End != 16 {
		t.Fatalf("span %v", ds[0].Span)
	}
}

func TestMacroNamesKeepLongestVariant(t *testing.T) {
	for _, name := range []string{
		"Person_Ext", "Person", "SystemQueue_Ext", "SystemDb_Ext", "System_Ext", "SystemQueue", "SystemDb", "System",
		"ContainerQueue_Ext", "ContainerDb_Ext", "Container_Ext", "ContainerQueue", "ContainerDb", "Container",
		"ComponentQueue_Ext", "ComponentDb_Ext", "Component_Ext", "ComponentQueue", "ComponentDb", "Component",
		"Deployment_Node", "Node", "Node_L", "Node_R",
		"Rel", "BiRel", "Rel_Up", "Rel_U", "Rel_Down", "Rel_D", "Rel_Left", "Rel_L", "Rel_Right", "Rel_R", "Rel_Back",
		"RelIndex", "UpdateElementStyle", "UpdateRelStyle", "UpdateLayoutConfig",
	} {
		tokens := parser.Lex([]byte(name+"(a,\"A\")"), nil)
		if len(tokens) < 2 || string(tokens[0].Raw) != name {
			t.Fatalf("%s: tokens %v", name, tokens)
		}
		if tokens[1].Kind != "LPAREN" {
			t.Fatalf("%s: second token %v", name, tokens[1])
		}
		if last := tokens[len(tokens)-2]; last.Kind != "RPAREN" {
			t.Fatalf("%s: penultimate token %v", name, last)
		}
	}
}

func TestPersonDoesNotShadowPersonExt(t *testing.T) {
	tokens := parser.Lex([]byte("Person_Ext(a)"), nil)
	if tokens[0].Kind != "PERSON_EXT" {
		t.Fatalf("kind %q", tokens[0].Kind)
	}
}

func TestMacroAliasesShareTokenKinds(t *testing.T) {
	for _, group := range []struct{ name, kind string }{
		{"Boundary", "BOUNDARY"},
		{"Enterprise_Boundary", "ENTERPRISE_BOUNDARY"},
		{"System_Boundary", "SYSTEM_BOUNDARY"},
		{"Container_Boundary", "CONTAINER_BOUNDARY"},
		{"Rel_Up", "REL_U"},
		{"Rel_U", "REL_U"},
		{"Rel_Down", "REL_D"},
		{"Rel_D", "REL_D"},
		{"Rel_Left", "REL_L"},
		{"Rel_L", "REL_L"},
		{"Rel_Right", "REL_R"},
		{"Rel_R", "REL_R"},
		{"Rel_Back", "REL_B"},
		{"RelIndex", "REL_INDEX"},
		{"Deployment_Node", "NODE"},
		{"Node", "NODE"},
		{"UpdateElementStyle", "UPDATE_EL_STYLE"},
		{"UpdateRelStyle", "UPDATE_REL_STYLE"},
		{"UpdateLayoutConfig", "UPDATE_LAYOUT_CONFIG"},
	} {
		tokens := parser.Lex([]byte(group.name+"(a,\"A\")"), nil)
		if len(tokens) < 2 || tokens[0].Kind != group.kind || string(tokens[0].Raw) != group.name {
			t.Fatalf("%s: tokens %v", group.name, tokens)
		}
		if tokens[1].Kind != "LPAREN" {
			t.Fatalf("%s: second token %v", group.name, tokens[1])
		}
	}
}

func TestNonMacroNameCandidatesStayRejected(t *testing.T) {
	for _, name := range []string{
		"Personx", "Person_Ext2", "System_Ext_Boundary", "SystemBoundary", "Container_Boundaries",
		"Node_X", "NodeQueue", "Rel_Z", "Rel_Up2", "_Boundary", "BoundaryX", "UpdateElement",
	} {
		text := name + "(a,\"A\")"
		tokens := parser.Lex([]byte(text), nil)
		if len(tokens) != 2 || tokens[0].Kind != "INVALID" || string(tokens[0].Raw) != text {
			t.Fatalf("%s: tokens %v", name, tokens)
		}
		if tokens[1].Kind != "EOF" {
			t.Fatalf("%s: trailing %v", name, tokens[1])
		}
	}
	tokens := parser.Lex([]byte("RelFoo bar"), nil)
	want := []struct{ kind, raw string }{{"INVALID", "RelFoo"}, {"INVALID", "bar"}, {"EOF", ""}}
	if len(tokens) != len(want) {
		t.Fatalf("no-paren rejection tokens %v", tokens)
	}
	for i := range want {
		if tokens[i].Kind != want[i].kind || string(tokens[i].Raw) != want[i].raw {
			t.Fatalf("no-paren rejection %d: %v", i, tokens[i])
		}
	}
}

func TestBareArgumentKeepsClosingParenthesis(t *testing.T) {
	tokens := parser.Lex([]byte("Person(a,raw)more,\"x\\\")"), nil)
	var bare, quoted *parser.Token
	for i := range tokens {
		switch string(tokens[i].Raw) {
		case "raw)more":
			bare = &tokens[i]
		case `x\`:
			quoted = &tokens[i]
		}
	}
	if bare == nil || bare.Kind != "STR" || bare.Span.Start != 9 || bare.Span.End != 17 {
		t.Fatalf("bare argument %v", tokens)
	}
	if quoted == nil || quoted.Kind != "STR" {
		t.Fatalf("backslash not ordinary: %v", tokens)
	}
}

func TestAttributesKeepSpansAndEmptySlots(t *testing.T) {
	src := []byte("C4Context\nPerson(,\"\")\n")
	start := parse(t, string(src))
	attributes := start.MermaidDoc.GraphConfig.Statements.Items[0].Diagram.Call.Attributes
	if attributes.Span.Start != 16 || attributes.Span.End != 21 || len(attributes.Items) != 2 {
		t.Fatalf("attributes %+v", attributes)
	}
	if first := attributes.Items[0]; first.Empty == nil || first.Span.Start != 17 || first.Span.End != 18 {
		t.Fatalf("empty slot %+v", first)
	}
	if second := attributes.Items[1]; second.Empty == nil || second.Span.Start != 18 || second.Span.End != 20 {
		t.Fatalf("empty quotes %+v", second)
	}
}

func TestNamedAttributeSpanCoversDelimiters(t *testing.T) {
	src := "C4Context\nPerson(a,\"é\",,\"\",$tags=\" x \")\n"
	start := parse(t, src)
	items := start.MermaidDoc.GraphConfig.Statements.Items[0].Diagram.Call.Attributes.Items
	if len(items) != 5 {
		t.Fatalf("attributes %v", items)
	}
	label := items[1]
	if label.Positional == nil || string(label.Positional.Raw) != "é" || label.Span.Start != 19 || label.Span.End != 23 {
		t.Fatalf("label %+v", label)
	}
	named := items[4]
	if named.Key == nil || string(named.Key.Raw) != "tags" {
		t.Fatalf("key %+v", named.Key)
	}
	if src[named.Span.Start:named.Span.End] != `$tags=" x "` {
		t.Fatalf("named span %q", src[named.Span.Start:named.Span.End])
	}
}

func TestBoundaryBraceArrangements(t *testing.T) {
	for _, form := range []struct{ prefix, suffix string }{{" {\n", "\n}"}, {"\n{", "}"}, {"\n{\n", "\n}"}} {
		src := "C4Deployment\nNode_L(n,\"N\")" + form.prefix + "Person(a,\"A\")" + form.suffix + "\n"
		start := parse(t, src)
		boundary := start.MermaidDoc.GraphConfig.Statements.Items[0].Diagram.Boundary
		if boundary == nil || string(boundary.Start.Start.Macro.Raw) != "Node_L" || len(boundary.Body.Items) != 1 {
			t.Fatalf("%q: %+v", form.prefix, boundary)
		}
		if got := src[boundary.Span.Start:boundary.Span.End]; got != strings.TrimSuffix(strings.TrimPrefix(src, "C4Deployment\n"), "\n") {
			t.Fatalf("%q: span %q", form.prefix, got)
		}
	}
}

func TestBoundaryNeedsNewlineAfterBrace(t *testing.T) {
	_, ds := parser.Parse([]byte("C4Context\nBoundary(b,\"B\") { Person(a,\"A\") }\n"), nil)
	if len(ds) != 2 {
		t.Fatalf("diagnostics %v", ds)
	}
	if ds[0].Message != "unexpected Person, expected one of: NEWLINE" {
		t.Fatalf("first %v", ds[0])
	}
	if ds[1].Message != "unexpected }, expected one of: EOF" {
		t.Fatalf("second %v", ds[1])
	}
}

func TestEmptyCallAndEmptyBodyRejected(t *testing.T) {
	_, ds := parser.Parse([]byte("C4Context\nPerson()\nPerson(a,\"A\")\n"), nil)
	if len(ds) != 1 || ds[0].Message != "unexpected ), expected one of: ATTRIBUTE_EMPTY, STR, STR_KEY" {
		t.Fatalf("diagnostics %v", ds)
	}
	start, more := parser.Parse([]byte("C4Context\n"), nil)
	if len(more) != 1 || more[0].Message != "unexpected , expected one of: diagramStatement, otherStatement" {
		t.Fatalf("diagnostics %v", more)
	}
	if more[0].Span.Start != 10 || more[0].Span.End != 10 {
		t.Fatalf("span %v", more[0].Span)
	}
	if len(start.MermaidDoc.GraphConfig.Statements.Items) != 0 {
		t.Fatalf("statements %v", start.MermaidDoc.GraphConfig.Statements.Items)
	}
}

func TestEmptyNamedValueIsNotAnAttribute(t *testing.T) {
	_, ds := parser.Parse([]byte("C4Context\nPerson(a,$tags=\"\")\nPerson(b,\"B\")\n"), nil)
	if len(ds) != 1 || ds[0].Message != "unexpected ), expected one of: STR_VALUE" {
		t.Fatalf("diagnostics %v", ds)
	}
	if ds[0].Span.Start != 27 || ds[0].Span.End != 28 {
		t.Fatalf("span %v", ds[0].Span)
	}
}

func TestUnknownStatementStopsBeforeEnclosingBrace(t *testing.T) {
	src := []byte("C4Context\nBoundary(b,\"B\") {\nPerson(a,\"A\")\nwrong stuff}\nPerson(z,\"Z\")\n")
	start, ds := parser.Parse(src, nil)
	if len(ds) != 1 || ds[0].Code != "c4/unknown-statement" || ds[0].Message != "unknown statement wrong" {
		t.Fatalf("diagnostics %v", ds)
	}
	if ds[0].Span.Start != 42 || ds[0].Span.End != 53 {
		t.Fatalf("span %v", ds[0].Span)
	}
	items := start.MermaidDoc.GraphConfig.Statements.Items
	if len(items) != 2 || items[0].Diagram.Boundary == nil || len(items[0].Diagram.Boundary.Body.Items) != 1 {
		t.Fatalf("statements %v", items)
	}
}

func TestSemicolonAndUnmatchedCloseDoNotCreateStatements(t *testing.T) {
	start, ds := parser.Parse([]byte("C4Context\nPerson(a,\"A\");\n}\nPerson(b,\"B\")\n"), nil)
	if len(ds) != 2 {
		t.Fatalf("diagnostics %v", ds)
	}
	if ds[0].Message != "unexpected ;, expected one of: EOF, NEWLINE, RBRACE" || ds[0].Span.Start != 23 || ds[0].Span.End != 24 {
		t.Fatalf("first %v", ds[0])
	}
	if ds[1].Message != "unexpected }, expected one of: EOF" || ds[1].Span.Start != 25 || ds[1].Span.End != 26 {
		t.Fatalf("second %v", ds[1])
	}
	if len(start.MermaidDoc.GraphConfig.Statements.Items) != 1 {
		t.Fatalf("statements %v", start.MermaidDoc.GraphConfig.Statements.Items)
	}
}

func TestEmptyBoundaryIsNotRetained(t *testing.T) {
	start, ds := parser.Parse([]byte("C4Context\nBoundary(b,\"B\") {\n}\nPerson(a,\"A\")\n"), nil)
	if len(ds) != 1 || ds[0].Message != "unexpected }, expected one of: diagramStatement" {
		t.Fatalf("diagnostics %v", ds)
	}
	if ds[0].Span.Start != 28 || ds[0].Span.End != 29 {
		t.Fatalf("span %v", ds[0].Span)
	}
	if len(start.MermaidDoc.GraphConfig.Statements.Items) != 1 {
		t.Fatalf("statements %v", start.MermaidDoc.GraphConfig.Statements.Items)
	}
}

func TestUnterminatedDelimitersSpanOpeningThroughEOF(t *testing.T) {
	cases := []struct {
		src   string
		start int
		text  string
	}{
		{"C4Context\nPerson(", 16, "("},
		{"C4Context\nPerson(a,\"é", 19, "\"é"},
		{"C4Context\nPerson(a,$tags=\"x", 19, "$tags=\"x"},
		{"C4Context\naccDescr {x", 19, "{x"},
		{"C4Context\nBoundary(b,\"B\") {\nPerson(a,\"A\")", 26, "{"},
	}
	for _, c := range cases {
		_, ds := parser.Parse([]byte(c.src), nil)
		if len(ds) == 0 {
			t.Fatalf("%q: no diagnostics", c.src)
		}
		last := ds[len(ds)-1]
		if last.Code != "c4/unterminated" || last.Message != "unterminated "+c.text {
			t.Fatalf("%q: %v", c.src, last)
		}
		if last.Span.Start != c.start || last.Span.End != len(c.src) {
			t.Fatalf("%q: span %v", c.src, last.Span)
		}
	}
}

func assertUnterminatedBrace(t *testing.T, src string, start, end int) {
	t.Helper()
	_, ds := parser.Parse([]byte(src), nil)
	if len(ds) != 1 || ds[0].Code != "c4/unterminated" || ds[0].Message != "unterminated {" {
		t.Fatalf("diagnostics %v", ds)
	}
	if ds[0].Span.Start != start || ds[0].Span.End != end {
		t.Fatalf("span %v", ds[0].Span)
	}
}

func TestUnterminatedReplacesUnexpectedAtEOF(t *testing.T) {
	assertUnterminatedBrace(t, "C4Context\naccDescr {", 19, 20)
	assertUnterminatedBrace(t, "C4Context\nBoundary(b,\"B\") {", 26, 27)
}

func TestNestingDepthLimitAtOpeningBrace(t *testing.T) {
	var body strings.Builder
	body.WriteString("C4Context\n")
	for range 65 {
		body.WriteString("Boundary(b,\"B\") {\n")
	}
	_, ds := parser.Parse([]byte(body.String()), nil)
	if len(ds) != 1 || ds[0].Code != "limit/nesting-depth" || ds[0].Message != "nesting depth exceeds 64" {
		t.Fatalf("diagnostics %v", ds)
	}
	if ds[0].Span.Start != 1178 || ds[0].Span.End != 1179 {
		t.Fatalf("span %v", ds[0].Span)
	}
}

func assertMetadataForms(t *testing.T, items []parser.Statement) {
	t.Helper()
	if len(items) != 6 {
		t.Fatalf("items %d", len(items))
	}
	forms := []string{"title", "acc_title", "accDescription", "acc_descr", "acc_descr_multiline_value"}
	var seen []string
	for i := range items {
		if items[i].Other != nil {
			seen = append(seen, items[i].Other.Form)
		}
	}
	if !reflect.DeepEqual(seen, forms) {
		t.Fatalf("forms %v", seen)
	}
}

func assertMetadataValues(t *testing.T, src string, items []parser.Statement) {
	t.Helper()
	if got := string(items[0].Other.Value.Raw); got != "Demo" {
		t.Fatalf("title %q", got)
	}
	if got := src[items[0].Other.Value.Span.Start:items[0].Other.Value.Span.End]; got != "Demo" {
		t.Fatalf("title span %q", got)
	}
	if got := string(items[2].Other.Value.Raw); got != "Long" {
		t.Fatalf("description %q", got)
	}
	if got := string(items[4].Other.Value.Raw); got != " one\ntwo " {
		t.Fatalf("multiline %q", got)
	}
	if got := src[items[4].Span.Start:items[4].Span.End]; got != "accDescr { one\ntwo }" {
		t.Fatalf("multiline span %q", got)
	}
}

func TestMetadataAndDirectionTokens(t *testing.T) {
	src := "C4Context\ntitle Demo\naccTitle: é\naccDescription Long\naccDescr: text\naccDescr { one\ntwo }\nPerson(a,\"A\")\n"
	start := parse(t, src)
	assertMetadataForms(t, start.MermaidDoc.GraphConfig.Statements.Items)
	assertMetadataValues(t, src, start.MermaidDoc.GraphConfig.Statements.Items)
	for _, direction := range []struct{ name, kind string }{
		{"TB", "direction_tb"}, {"BT", "direction_bt"}, {"RL", "direction_rl"}, {"LR", "direction_lr"},
	} {
		parsed := parse(t, "direction "+direction.name)
		if parsed.Direction == nil || parsed.Direction.Direction.Kind != direction.kind {
			t.Fatalf("%s: %+v", direction.name, parsed)
		}
	}
}

func TestDirectionMatchConsumesWholeLine(t *testing.T) {
	start := parse(t, "noise direction LR suffix direction TB end")
	if start.Direction == nil || start.Direction.Direction.Kind != "direction_tb" {
		t.Fatalf("start %+v", start)
	}
	if start.Direction.Span.Start != 0 || start.Direction.Span.End != 42 {
		t.Fatalf("span %v", start.Direction.Span)
	}
}

func TestDirectionPriorityIgnoresOccurrenceOrder(t *testing.T) {
	for _, c := range []struct{ src, kind string }{
		{"noise direction BT suffix direction TB end", "direction_tb"},
		{"noise direction RL suffix direction BT end", "direction_bt"},
		{"noise direction LR suffix direction RL end", "direction_rl"},
	} {
		start := parse(t, c.src)
		if start.Direction == nil || start.Direction.Direction.Kind != c.kind {
			t.Fatalf("%s: %+v", c.src, start.Direction)
		}
	}
}

func TestDiagnosticsAreSortedAndSpanSource(t *testing.T) {
	src := []byte("C4Context\nBoundary(b,\"B\") {\nwrong stuff\nPerson(\n")
	_, ds := parser.Parse(src, nil)
	if len(ds) == 0 {
		t.Fatal("no diagnostics")
	}
	previous := diag.Diagnostic{}
	for i, d := range ds {
		if d.Span.Start < 0 || d.Span.End < d.Span.Start || d.Span.End > len(src) {
			t.Fatalf("span outside source: %v", d)
		}
		if i > 0 && (d.Span.Start < previous.Span.Start || d.Span.Start == previous.Span.Start && d.Code < previous.Code) {
			t.Fatalf("unsorted diagnostics %v", ds)
		}
		previous = d
	}
}

func TestTokenSourceBorrowing(t *testing.T) {
	src := []byte("C4Context\nPerson(a,\"A\")")
	tokens := parser.Lex(src, nil)
	for i := range src {
		src[i] = 0x01
	}
	for _, token := range tokens {
		for _, b := range token.Raw {
			if b != 0x01 {
				t.Fatalf("token text does not borrow source: %+v", token)
			}
		}
	}
}

func TestRemovedSpansAreSkipped(t *testing.T) {
	src := []byte("C4Context\n%% hidden\nPerson(a,\"A\")")
	removed := []source.Span{{Start: 10, End: 20}}
	start, ds := parser.Parse(src, removed)
	if len(ds) != 0 {
		t.Fatalf("diagnostics %v", ds)
	}
	items := start.MermaidDoc.GraphConfig.Statements.Items
	if len(items) != 1 || items[0].Diagram.Call == nil {
		t.Fatalf("statements %v", items)
	}
	if got := string(items[0].Diagram.Call.Macro.Raw); got != "Person" {
		t.Fatalf("macro %q", got)
	}
}
