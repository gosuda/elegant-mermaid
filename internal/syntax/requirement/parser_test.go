package requirement

import (
	"slices"
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

func parse(t *testing.T, src string) (*Start, []string) {
	t.Helper()
	document, ds := Parse([]byte(src), nil)
	codes := make([]string, len(ds))
	for i, d := range ds {
		codes[i] = d.Code
	}
	return document, codes
}

func firstStatement(t *testing.T, d *Start) Statement {
	t.Helper()
	if len(d.Diagram.Statements) == 0 {
		t.Fatal("missing statement")
	}
	return d.Diagram.Statements[0]
}

func TestHeaderAliasRequiresNewline(t *testing.T) {
	for _, ending := range []string{"\n", "\r\n", "\r"} {
		src := "requirement" + ending
		d, diagnostics := Parse([]byte(src), nil)
		if len(diagnostics) != 0 || d.Header.Span != (source.Span{Start: 0, End: 11}) {
			t.Fatal(ending, diagnostics, d.Header)
		}
		if src[d.Header.Span.Start:d.Header.Span.End] != "requirement" {
			t.Fatal(ending, d.Header)
		}
		if d.Diagram.Span != (source.Span{Start: len(src), End: len(src)}) {
			t.Fatal(ending, d.Diagram.Span)
		}
	}
	for _, src := range []string{"requirementDiagram", "requirement"} {
		_, diagnostics := Parse([]byte(src), nil)
		if len(diagnostics) != 1 || diagnostics[0].Code != "requirement/unexpected-token" {
			t.Fatal(src, diagnostics)
		}
		if diagnostics[0].Span != (source.Span{Start: len(src), End: len(src)}) {
			t.Fatalf("%q: missing-header-newline diagnostic must cover EOF: %v", src, diagnostics[0])
		}
	}
}

func TestDefinitionKeepsFieldsAndDelimiters(t *testing.T) {
	src := "requirementDiagram\nrequirement req {\nid: 1\ntext: \"é\"\nrisk: high\nverifyMethod: test\n}\n"
	d, ds := parse(t, src)
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	def := firstStatement(t, d).Kind.Requirement
	type parts struct {
		name    string
		nameSp  source.Span
		open    source.Span
		fields  int
		typ     string
		text    Text
		textCol source.Span
	}
	got := parts{
		name:    def.Name.Value,
		nameSp:  def.Name.Span,
		open:    def.Delimiters[0],
		fields:  len(def.Body.Fields),
		typ:     def.RequirementType.Value,
		text:    def.Body.Fields[1].Value.Text,
		textCol: def.Body.Fields[1].Colon,
	}
	want := parts{
		name:    "req",
		nameSp:  source.Span{Start: 31, End: 35},
		open:    source.Span{Start: 35, End: 36},
		fields:  4,
		typ:     "Requirement",
		text:    Text{Span: source.Span{Start: 49, End: 53}, Quoted: true, Value: "é"},
		textCol: source.Span{Start: 47, End: 48},
	}
	if got != want {
		t.Fatal(got)
	}
}

func TestTypeAlternativesAndEmptyBodies(t *testing.T) {
	for _, form := range [][2]string{
		{"requirement", "Requirement"},
		{"functionalRequirement", "Functional Requirement"},
		{"interfaceRequirement", "Interface Requirement"},
		{"performanceRequirement", "Performance Requirement"},
		{"physicalRequirement", "Physical Requirement"},
		{"designConstraint", "Design Constraint"},
	} {
		src := "requirementDiagram\n" + form[0] + " req {\n}\n"
		d, ds := parse(t, src)
		if len(ds) != 0 {
			t.Fatal(form, ds)
		}
		def := firstStatement(t, d).Kind.Requirement
		if def.RequirementType.Value != form[1] || len(def.Body.Fields) != 0 || def.Body.Span != def.Delimiters[1] {
			t.Fatal(form, def)
		}
	}
}

func TestRelationshipsKeepDirectionAndKinds(t *testing.T) {
	for _, relation := range []string{"contains", "copies", "derives", "satisfies", "verifies", "refines", "traces"} {
		src := "requirementDiagram\nA - " + relation + " -> B\nA <- " + relation + " - A\n"
		d, ds := parse(t, src)
		if len(ds) != 0 {
			t.Fatal(ds)
		}
		forward := d.Diagram.Statements[0].Kind.Relationship
		type ends struct {
			left, right, relation string
			reversed              bool
			leftSp                source.Span
		}
		got := ends{forward.Left.Value, forward.Right.Value, forward.Relationship.Value, forward.Reversed, forward.Left.Span}
		want := ends{"A", "B", relation, false, source.Span{Start: 19, End: 21}}
		if got != want {
			t.Fatal(got)
		}
		reverse := d.Diagram.Statements[1].Kind.Relationship
		back := ends{reverse.Left.Value, reverse.Right.Value, reverse.Relationship.Value, reverse.Reversed, reverse.Left.Span}
		reverseStart := 19 + 10 + len(relation)
		wantBack := ends{"A", "A", relation, true, source.Span{Start: reverseStart, End: reverseStart + 2}}
		if back != wantBack {
			t.Fatal(back)
		}
	}
}

func componentTexts(style Style) []string {
	out := make([]string, len(style.Components))
	for i, c := range style.Components {
		out[i] = c.Text
	}
	return out
}

func TestStylesKeepComponentsAndClassLists(t *testing.T) {
	src := "requirementDiagram\nclassDef blue,red fill:#abc,color:red;\nstyle A,B stroke-width:2\nclass A,B blue,red\nA:::blue,red\n"
	d, ds := parse(t, src)
	if len(ds) != 0 || len(d.Diagram.Statements) != 4 {
		t.Fatal(ds, len(d.Diagram.Statements))
	}
	def := d.Diagram.Statements[0].Kind.ClassDef
	type idAndSpan struct {
		first, second string
		sp            source.Span
	}
	if got := (idAndSpan{def.Ids.Names[0].Value, def.Ids.Names[1].Value, def.Ids.Span}); got != (idAndSpan{"blue", "red", source.Span{Start: 28, End: 36}}) {
		t.Fatal(got)
	}
	type styleParts struct {
		components string
		sp         source.Span
	}
	first := def.Styles.Styles[0]
	if got := (styleParts{strings.Join(componentTexts(first), ","), first.Span}); got != (styleParts{"fill,:,#,abc", source.Span{Start: 37, End: 46}}) {
		t.Fatal(got)
	}
	style := d.Diagram.Statements[1].Kind.Style
	if !slices.Equal(namesOf(style.Ids), []string{"A", "B"}) {
		t.Fatal(namesOf(style.Ids))
	}
	class := d.Diagram.Statements[3].Kind.Class
	separator := source.Span{}
	if class.Separator != nil {
		separator = *class.Separator
	}
	type classParts struct {
		classes   int
		separator source.Span
	}
	if got := (classParts{len(class.Classes.Names), separator}); got != (classParts{2, source.Span{Start: 103, End: 106}}) {
		t.Fatal(got)
	}
}

func namesOf(list IdList) []string {
	out := make([]string, len(list.Names))
	for i, n := range list.Names {
		out[i] = n.Value
	}
	return out
}

func TestAccessibilityModes(t *testing.T) {
	src := "accTitle: Before\nrequirementDiagram\naccDescr: café\naccDescr {one\r\ntwo}\naccTitle:\n"
	d, ds := parse(t, src)
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	if d.Directives[0].Value.Text != "Before" || d.Directives[0].Span != (source.Span{Start: 0, End: 16}) {
		t.Fatal(d.Directives[0])
	}
	block := d.Diagram.Statements[1].Kind.Directive
	if block.Value.Text != "one\r\ntwo" || !block.Multiline || block.Span != (source.Span{Start: 52, End: 71}) {
		t.Fatal(block)
	}
	empty := d.Diagram.Statements[2].Kind.Directive
	if empty.Value.Text != "" {
		t.Fatal(empty)
	}
}

func TestWholeLineDirections(t *testing.T) {
	src := "requirementDiagram\nnoise direction LR suffix direction TB\n# direction BT\n%% direction RL\n"
	d, ds := parse(t, src)
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	var values []string
	for _, s := range d.Diagram.Statements {
		if s.Kind.Kind == "Direction" {
			values = append(values, s.Kind.Direction.Value)
		}
	}
	if len(values) != 3 || values[0] != "TB" || values[1] != "BT" || values[2] != "RL" {
		t.Fatal(values)
	}
	if d.Diagram.Statements[0].Span != (source.Span{Start: 19, End: 57}) {
		t.Fatal(d.Diagram.Statements[0].Span)
	}
}

func TestMixedLineEndingsAndBodyCaseFold(t *testing.T) {
	src := "requirementDiagram\rReQuIrEmEnT r {\r\nRiSk: LOW\nVERIFYMETHOD: ANALYSIS\r}\r"
	d, ds := parse(t, src)
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	fields := firstStatement(t, d).Kind.Requirement.Body.Fields
	if len(fields) != 2 || fields[0].Value.Risk.Value != "Low" || fields[0].Value.Risk.Span != (source.Span{Start: 42, End: 45}) {
		t.Fatal(fields)
	}
}

func TestInvalidRiskRecoversAtNextField(t *testing.T) {
	src := "requirementDiagram\nrequirement r {\nrisk: extreme\ntext: okay\n}\nelement e {\n}\n"
	document, ds := Parse([]byte(src), nil)
	if len(ds) != 1 || ds[0].Code != "requirement/unexpected-token" {
		t.Fatal(ds)
	}
	if ds[0].Message != "unexpected extreme, expected one of: HIGH_RISK, LOW_RISK, MED_RISK" {
		t.Fatal(ds[0].Message)
	}
	if ds[0].Span != (source.Span{Start: 41, End: 48}) || len(document.Diagram.Statements) != 2 {
		t.Fatal(ds[0].Span, len(document.Diagram.Statements))
	}
	fields := document.Diagram.Statements[0].Kind.Requirement.Body.Fields
	if len(fields) != 1 {
		t.Fatal(fields)
	}
}

func TestInvalidVerificationKeepsClosingBrace(t *testing.T) {
	document, ds := Parse([]byte("requirementDiagram\nrequirement r {\nverifyMethod: nope\n}\n"), nil)
	if len(ds) != 1 || ds[0].Message != "unexpected nope, expected one of: VERIFY_ANALYSIS, VERIFY_DEMONSTRATION, VERIFY_INSPECTION, VERIFY_TEST" {
		t.Fatal(ds)
	}
	if ds[0].Span != (source.Span{Start: 49, End: 53}) || len(document.Diagram.Statements) != 1 {
		t.Fatal(ds[0].Span, len(document.Diagram.Statements))
	}
}

func TestUnknownStatementRecovers(t *testing.T) {
	for _, src := range []string{"requirementDiagram\n@ bad\nelement e {\n}\n", "requirementDiagram\nnonsense\nelement e {\n}\n"} {
		document, ds := Parse([]byte(src), nil)
		if len(ds) != 1 || ds[0].Code != "requirement/unknown-statement" {
			t.Fatal(src, ds)
		}
		if !strings.HasPrefix(ds[0].Message, "unknown statement ") || len(document.Diagram.Statements) != 1 {
			t.Fatal(ds[0].Message, len(document.Diagram.Statements))
		}
	}
	d, ds := parse(t, "requirementDiagram\n@ bad\nelement e {\n}\n")
	if ds[0] != "requirement/unknown-statement" {
		t.Fatal(ds)
	}
	if d.Diagram.Statements[0].Span != (source.Span{Start: 25, End: 38}) {
		t.Fatal(d.Diagram.Statements[0].Span)
	}
}

func TestUnknownUnquotedWordMessageDropsTrailingWhitespace(t *testing.T) {
	_, ds := Parse([]byte("requirementDiagram\n  req1 \n  req2   \n"), nil)
	want := []struct {
		message string
		span    source.Span
	}{
		{"unknown statement req1", source.Span{Start: 21, End: 26}},
		{"unknown statement req2", source.Span{Start: 29, End: 36}},
	}
	if len(ds) != len(want) {
		t.Fatal(ds)
	}
	for i, w := range want {
		if ds[i].Code != "requirement/unknown-statement" || ds[i].Message != w.message || ds[i].Span != w.span {
			t.Fatalf("diagnostic %d: %+v, want %+v", i, ds[i], w)
		}
	}
}

func TestPercentStaysUnexpectedInStyle(t *testing.T) {
	_, ds := Parse([]byte("requirementDiagram\nstyle A width:50%\nelement e {\n}\n"), nil)
	if len(ds) != 1 || ds[0].Message != "unexpected %, expected one of: ALPHA, BRKT, COLON, LABEL, MINUS, NUM, PCT, SEMICOLON, SPACE, UNIT" {
		t.Fatal(ds)
	}
	if ds[0].Span != (source.Span{Start: 35, End: 36}) {
		t.Fatal(ds[0].Span)
	}
}

func TestTitleIsLexedWithoutProduction(t *testing.T) {
	document, ds := Parse([]byte("requirementDiagram\ntitle unused\nelement e {\n}\n"), nil)
	if len(ds) != 1 || ds[0].Code != "requirement/unexpected-token" || ds[0].Span != (source.Span{Start: 19, End: 31}) {
		t.Fatal(ds)
	}
	if !strings.HasPrefix(ds[0].Message, "unexpected title unused, expected one of: CLASS, CLASSDEF,") {
		t.Fatal(ds[0].Message)
	}
	if len(document.Diagram.Statements) != 1 {
		t.Fatal(len(document.Diagram.Statements))
	}
}

func TestEOFReportsEachOpenDelimiterOnce(t *testing.T) {
	for _, form := range [][3]any{
		{"requirementDiagram\nrequirement r {\n", 33, "{"},
		{"requirementDiagram\nelement e {\n", 29, "{"},
		{"requirementDiagram\nelement \"é", 27, "\"é"},
		{"requirementDiagram\naccDescr {unfinished", 28, "{unfinished"},
		{"requirementDiagram\nrequirement r {\ntext: \"é", 41, "\"é"},
	} {
		src := form[0].(string)
		document, ds := Parse([]byte(src), nil)
		if len(ds) != 1 || ds[0].Code != "requirement/unterminated" {
			t.Fatal(src, ds)
		}
		if ds[0].Span != (source.Span{Start: form[1].(int), End: len(src)}) {
			t.Fatal(ds[0].Span)
		}
		if ds[0].Message != "unterminated "+form[2].(string) {
			t.Fatal(ds[0].Message)
		}
		if len(document.Diagram.Statements) != 0 {
			t.Fatal(document.Diagram.Statements)
		}
	}
}

func TestQuotedTokensKeepQuotesWithoutEscaping(t *testing.T) {
	tokens := Lex([]byte("requirementDiagram\nelement \"\" {\n}\n\"a\\\"b\n"), nil)
	var quoted []Token
	for _, tok := range tokens {
		if tok.Kind == "qString" {
			quoted = append(quoted, tok)
		}
	}
	if len(quoted) != 2 || quoted[0].Text != "" || quoted[0].Span != (source.Span{Start: 27, End: 29}) {
		t.Fatal(quoted)
	}
	if quoted[1].Text != "a\\" || quoted[1].Span != (source.Span{Start: 34, End: 38}) {
		t.Fatal(quoted[1])
	}
}

func TestLexerModesAndRulePrecedence(t *testing.T) {
	want := []string{"INITIAL", "string", "token", "unqString", "style", "acc_title", "acc_descr", "acc_descr_multiline"}
	if strings.Join(Modes, ",") != strings.Join(want, ",") {
		t.Fatal(Modes)
	}
	tokens := Lex([]byte("requirementDiagram\nstyle A x:12%;#fff\n"), nil)
	kinds := make([]string, len(tokens))
	for i, tok := range tokens {
		kinds[i] = tok.Kind
	}
	wantKinds := "RD,NEWLINE,STYLE,ALPHA,ALPHA,COLON,ALPHA,PERCENT,SEMICOLON,BRKT,ALPHA,EOF"
	if strings.Join(kinds, ",") != wantKinds {
		t.Fatal(kinds)
	}
	if tokens[6].Text != "12" || tokens[6].Span != (source.Span{Start: 29, End: 31}) {
		t.Fatal(tokens[6])
	}
}

func TestRemovedRegionsPreserveOffsets(t *testing.T) {
	src := "ignored\nrequirementDiagram\nelement e {\n}\n"
	document, ds := Parse([]byte(src), []source.Span{{Start: 0, End: 8}})
	if len(ds) != 0 || document.Header.Span != (source.Span{Start: 8, End: 26}) {
		t.Fatal(ds, document.Header.Span)
	}
	if document.Diagram.Statements[0].Span != (source.Span{Start: 27, End: 40}) {
		t.Fatal(document.Diagram.Statements[0].Span)
	}
}

func TestInvalidElementFieldRecovers(t *testing.T) {
	document, ds := Parse([]byte("requirementDiagram\nelement e {\nrisk: low\ndocref: doc\n}\n"), nil)
	if len(ds) != 1 || ds[0].Message != "unexpected risk, expected one of: DOCREF, NEWLINE, STRUCT_STOP, TYPE" {
		t.Fatal(ds)
	}
	if ds[0].Span != (source.Span{Start: 31, End: 35}) || len(document.Diagram.Statements) != 1 {
		t.Fatal(ds[0].Span, len(document.Diagram.Statements))
	}
	fields := document.Diagram.Statements[0].Kind.Element.Body.Fields
	if len(fields) != 1 || fields[0].Value.Ref.Value != "doc" || fields[0].Value.Ref.Span != (source.Span{Start: 49, End: 52}) {
		t.Fatal(fields)
	}
}

func TestStyleQuoteTargetTokens(t *testing.T) {
	tokens := Lex([]byte("requirementDiagram\nclass \"A\",B blue\n"), nil)
	var quoted Token
	for _, tok := range tokens {
		if tok.Kind == "qString" {
			quoted = tok
			break
		}
	}
	if quoted.Text != "A" || quoted.Span != (source.Span{Start: 25, End: 28}) {
		t.Fatal(quoted)
	}
	var tail []string
	for _, tok := range tokens {
		if tok.Span.Start >= 28 {
			tail = append(tail, tok.Kind)
		}
	}
	if strings.Join(tail, ",") != "COMMA,ALPHA,ALPHA,EOF" {
		t.Fatal(tail)
	}
}

func TestStyleUnterminatedQuoteReportsEOF(t *testing.T) {
	_, ds := Parse([]byte("requirementDiagram\nstyle A \"unfinished"), nil)
	if len(ds) != 1 || ds[0].Code != "requirement/unterminated" {
		t.Fatal(ds)
	}
	if ds[0].Message != "unterminated \"unfinished" || ds[0].Span != (source.Span{Start: 27, End: 38}) {
		t.Fatal(ds[0])
	}
}

func TestLexerGroupsLineEvents(t *testing.T) {
	tokens := Lex([]byte("requirementDiagram\n\nA café  - copies -> B\n"), nil)
	if tokens[1].Kind != "NEWLINE" || tokens[1].Span != (source.Span{Start: 18, End: 20}) {
		t.Fatal(tokens[1])
	}
	if tokens[2].Text != "A café" || tokens[2].Span != (source.Span{Start: 20, End: 29}) {
		t.Fatal(tokens[2])
	}
}
