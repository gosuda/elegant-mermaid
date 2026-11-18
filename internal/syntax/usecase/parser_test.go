package usecase_test

import (
	"fmt"
	"slices"
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/usecase"
)

func statements(start *parser.Start) []*parser.Statement {
	var out []*parser.Statement
	for _, line := range start.Lines {
		if line.Statement != nil {
			out = append(out, line.Statement)
		}
	}
	return out
}

func firstDiagnostic(t *testing.T, ds []diag.Diagnostic) diag.Diagnostic {
	t.Helper()
	if len(ds) == 0 {
		t.Fatal("no diagnostics")
	}
	return ds[0]
}

func TestHeaderOnlyHasNoBody(t *testing.T) {
	start, ds := parser.Parse([]byte("usecase-beta"), nil)
	if len(ds) != 0 || len(start.Lines) != 0 {
		t.Fatalf("%v %v", ds, start.Lines)
	}
	if start.Header.Span != (source.Span{Start: 0, End: 12}) || start.LineEnd.Span != (source.Span{Start: 12, End: 12}) {
		t.Fatalf("%+v %+v", start.Header, start.LineEnd)
	}
}

func TestTokenOrderKeepsKeywordsAndOperators(t *testing.T) {
	src := "actor actorX classDef Include includeX 1mg 1.5px --var --o <-- --|> ..> \\,"
	var kinds []string
	for _, token := range parser.Lex(src, nil) {
		kinds = append(kinds, token.Kind)
	}
	want := []string{"ACTOR", "IDENTIFIER", "CLASS_DEF", "INCLUDE", "IDENTIFIER", "IDENTIFIER", "NUMBER", "MARKERLESS_SOLID", "IDENTIFIER", "FORWARD_CIRCLE", "BACKWARD_SOLID", "GENERALIZATION", "DEPENDENCY_ARROW", "CSS_ESCAPED_COMMA"}
	if !slices.Equal(kinds, want) {
		t.Fatalf("%v", kinds)
	}
	number := parser.Lex(src, nil)[6]
	if number.Text != "1.5px" || number.Span != (source.Span{Start: 43, End: 48}) {
		t.Fatalf("%+v", number)
	}
}

func TestRemovedSpansAndMixedLineEndsKeepByteOffsets(t *testing.T) {
	src := "xxxx\r\nusecase-beta\ractor A(é)\r\nB[界]\n"
	removed := []source.Span{{Start: 0, End: 6}}
	tokens := parser.Lex(src, removed)
	if tokens[0].Span != (source.Span{Start: 6, End: 18}) {
		t.Fatalf("%+v", tokens[0])
	}
	var symbols []string
	for _, token := range tokens {
		if token.Kind == "LABEL_SYMBOL" {
			symbols = append(symbols, fmt.Sprintf("%s@%d-%d", token.Text, token.Span.Start, token.Span.End))
		}
	}
	if !slices.Equal(symbols, []string{"é@27-29", "界@34-37"}) {
		t.Fatalf("%v", symbols)
	}
	start, ds := parser.Parse([]byte(src), removed)
	if len(ds) != 0 || len(start.Lines) != 2 {
		t.Fatalf("%v %d", ds, len(start.Lines))
	}
}

func TestDeclarationsKeepLabelsSuffixesAndBytes(t *testing.T) {
	src := "usecase-beta\nactor A(Hello  世界)@{business:true} << Staff >>:::staff,admin\nU[\"Quoted\"]\n\"`**Named**`\"\n"
	start, ds := parser.Parse([]byte(src), nil)
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	item := start.Lines[0].Statement.Actor.Items[0]
	if item.Name.Label.Text != "Hello  世界" || item.Name.Label.ContentSpan != (source.Span{Start: 21, End: 34}) {
		t.Fatalf("%+v", item.Name.Label)
	}
	var classes []string
	for _, class := range item.Classes.Classes {
		classes = append(classes, class.Text)
	}
	if !slices.Equal(classes, []string{"staff", "admin"}) || item.Stereotype.Content.Text != " Staff " || item.Stereotype.ContentSpan != (source.Span{Start: 55, End: 60}) {
		t.Fatalf("%v %+v", classes, item.Stereotype)
	}
}

func TestEveryStatementFormRetainsItsNode(t *testing.T) {
	src := "usecase-beta\naccTitle: Caption\naccDescr {first\nsecond}\ndirection TD\nactor A, B\nU(Use case)\nU --> V\nU@{business:true}\nnote for U \"memo\"\njson J@{\"b\":[1,{\"a\":true}],\"a\":null}:::data\nclassDef hot,cold fill:#abc,stroke-width:2px\nclass U,V hot,cold\nstyle U stroke:rgb(1\\,2\\,3),opacity:.5\nsystemBoundary S[System]@{type:package}:::box\nactor C\nX(Inside)\n\n%% comment\nend\n"
	start, ds := parser.Parse([]byte(src), nil)
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	all := statements(start)
	if len(all) != 13 {
		t.Fatalf("%d statements", len(all))
	}
	json := all[8].JSON
	if json == nil || json.ID.Text != "J" || len(json.Object.Properties) != 2 || json.Object.Properties[0].Key.Text != "\"b\"" {
		t.Fatalf("%+v", all[8])
	}
	boundary := all[12].SystemBoundary
	if boundary == nil || len(boundary.Content.Elements) != 4 || boundary.Close.Text != "end" {
		t.Fatalf("%+v", all[12])
	}
}

func TestAssociationLabelsAndSemanticArrows(t *testing.T) {
	src := "usecase-beta\nA --> B\nA <-- B\nA -- B\nA --o B\nA o-- B\nA --x B\nA x-- B\nA -- yes --> B\nA -- yes -- B\nA -- yes --o B\nA -- yes --x B\nA <-- yes -- B\nA o-- yes -- B\nA x-- yes -- B\nA e@..>:Include B\nA --|> B\nactor User --> B\n"
	start, ds := parser.Parse([]byte(src), nil)
	if len(ds) != 0 || len(start.Lines) != 17 {
		t.Fatalf("%v %d", ds, len(start.Lines))
	}
	arrow := start.Lines[7].Statement.Entity.Relation.Arrow.MarkerlessSolid
	if arrow == nil || arrow.Label.Label.Text != "yes" || arrow.Right.Kind != "FORWARD_SOLID" {
		t.Fatalf("%+v", arrow)
	}
	semantic := start.Lines[14].Statement.Entity.Relation
	if semantic.ID.Text != "e" || semantic.Arrow.Semantic.Relation.Text != "Include" {
		t.Fatalf("%+v", semantic)
	}
}

func TestMarkdownJSONAndStereotypeModesKeepDelimiters(t *testing.T) {
	src := "usecase-beta\nA(\"`a\r\nb`\") <<Core>>\njson J@{\"brace\":\"}\\\"{\",\"nested\":{}}\n"
	tokens := parser.Lex(src, nil)
	find := func(kind string) parser.Token {
		for _, token := range tokens {
			if token.Kind == kind {
				return token
			}
		}
		t.Fatalf("no %s", kind)
		return parser.Token{}
	}
	if markdown := find("MARKDOWN_STRING"); markdown.Text != "\"`a\r\nb`\"" || markdown.Span != (source.Span{Start: 15, End: 23}) {
		t.Fatalf("%+v", markdown)
	}
	if object := find("JSON_OBJECT_LITERAL"); object.Text != "{\"brace\":\"}\\\"{\",\"nested\":{}}" {
		t.Fatalf("%q", object.Text)
	}
	if _, ds := parser.Parse([]byte(src), nil); len(ds) != 0 {
		t.Fatal(ds)
	}
}

func TestRejectedStatementsRecoverWithoutPhantomNodes(t *testing.T) {
	start, ds := parser.Parse([]byte("usecase-beta\nPACKAGE box\nA;\nB\n"), nil)
	if len(ds) != 2 {
		t.Fatal(ds)
	}
	if ds[0].Code != "usecase/unknown-statement" || ds[0].Message != "unknown statement PACKAGE" || ds[0].Span != (source.Span{Start: 13, End: 24}) {
		t.Fatalf("%+v", ds[0])
	}
	if ds[1].Code != "usecase/unexpected-token" || ds[1].Span != (source.Span{Start: 26, End: 27}) || len(statements(start)) != 1 {
		t.Fatalf("%+v", ds[1])
	}
}

func TestDiagnosticMessagesAndSpans(t *testing.T) {
	cases := []struct {
		name, src, code, message string
		span                     source.Span
	}{
		{"direction", "usecase-beta\ndirection UP\nB\n", "usecase/unexpected-token", "unexpected UP, expected one of: BT, LR, RL, TB, TD", source.Span{Start: 23, End: 25}},
		{"boundary", "usecase-beta\nsystemBoundary S\nA --> B\nC\nend\nD\n", "usecase/unexpected-token", "unexpected -->, expected one of: NEWLINE", source.Span{Start: 32, End: 35}},
		{"json comma", "usecase-beta\njson J@{\"x\":1,}\nB\n", "usecase/invalid-json", "invalid JSON object: unexpected token", source.Span{Start: 27, End: 28}},
		{"stereotype", "usecase-beta\nA <<unfinished\nB\n", "usecase/unexpected-token", "unexpected unfinished, expected one of: STEREOTYPE_TEXT", source.Span{Start: 17, End: 27}},
		{"mixed label", "usecase-beta\nA -- \"yes\" extra --> B\nC\n", "usecase/unexpected-token", "unexpected extra, expected one of: FORWARD_CIRCLE, FORWARD_CROSS, FORWARD_SOLID, MARKERLESS_SOLID", source.Span{Start: 24, End: 29}},
	}
	for _, c := range cases {
		_, ds := parser.Parse([]byte(c.src), nil)
		d := firstDiagnostic(t, ds)
		if d.Code != c.code || d.Message != c.message || d.Span != c.span || len(ds) != 1 {
			t.Fatalf("%s: %+v (%d)", c.name, ds, len(ds))
		}
	}
}

func TestUnfinishedDelimitersEmitOneErrorThroughEOF(t *testing.T) {
	for _, c := range []struct {
		body  string
		start int
		token string
	}{
		{"A(", 14, "("}, {"A[", 14, "["}, {"A@{", 14, "@{"}, {"A <<", 15, "<<"},
		{"A(\"unfinished", 15, "\"unfinished"}, {"A(\"`unfinished", 15, "\"`unfinished"},
		{"json J@{", 20, "{"}, {"accDescr {", 13, "accDescr {"}, {"systemBoundary S\nA\n", 13, "systemBoundary"},
	} {
		src := "usecase-beta\n" + c.body
		_, ds := parser.Parse([]byte(src), nil)
		if len(ds) != 1 || ds[0].Code != "usecase/unterminated" || ds[0].Message != "unterminated "+c.token || ds[0].Span != (source.Span{Start: c.start, End: len(src)}) {
			t.Fatalf("%q: %+v", c.body, ds)
		}
	}
}

func TestJSONNestingRejectsLevelSixtyFive(t *testing.T) {
	src := "usecase-beta\njson J@{\"x\":" + strings.Repeat("[", 64) + "0" + strings.Repeat("]", 64) + "}"
	_, ds := parser.Parse([]byte(src), nil)
	if len(ds) != 1 || ds[0].Code != "limit/nesting-depth" || ds[0].Message != "nesting depth exceeds 64" || ds[0].Span != (source.Span{Start: 88, End: 89}) {
		t.Fatalf("%+v", ds)
	}
}

func TestClosedInvalidConstructsAtEOFAreNotUnterminated(t *testing.T) {
	for _, src := range []string{"usecase-beta\nA()", "usecase-beta\nA << >>", "usecase-beta\nA@{x:[]}"} {
		_, ds := parser.Parse([]byte(src), nil)
		if len(ds) != 1 || ds[0].Code != "usecase/unexpected-token" {
			t.Fatalf("%q: %+v", src, ds)
		}
	}
}

func TestJSONIdentifierDoesNotAliasKeyword(t *testing.T) {
	start, ds := parser.Parse([]byte("usecase-beta\njson json@{}\n"), nil)
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	json := start.Lines[0].Statement.JSON
	if json.ID.Text != "json" || json.ID.Span != (source.Span{Start: 18, End: 22}) || json.Object.Span != (source.Span{Start: 23, End: 25}) {
		t.Fatalf("%+v", json)
	}
}

func TestStrictJSONKeepsScalarLexemesAndOrder(t *testing.T) {
	start, ds := parser.Parse([]byte("usecase-beta\njson J@{\"z\":-1.25e+2,\"a\":\"\\u0041\",\"z\":false}\n"), nil)
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	properties := start.Lines[0].Statement.JSON.Object.Properties
	if len(properties) != 3 || properties[2].Key.Text != "\"z\"" {
		t.Fatalf("%+v", properties)
	}
	if number := properties[0].Value.Scalar; number.Kind != "JSON_NUMBER" || number.Text != "-1.25e+2" {
		t.Fatalf("%+v", number)
	}
}

func TestQuotedAndMarkdownContentSpansExcludeOnlyDelimiters(t *testing.T) {
	start, ds := parser.Parse([]byte("usecase-beta\n\"é 名\"\nA(\"`**bold**`\")\n"), nil)
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	name := start.Lines[0].Statement.Entity.Name
	if name.ID.Span != (source.Span{Start: 13, End: 21}) || name.IDContentSpan != (source.Span{Start: 14, End: 20}) {
		t.Fatalf("%+v", name)
	}
	label := start.Lines[1].Statement.Entity.Name.Label
	if label.Kind != parser.LabelMarkdown || label.Text != "**bold**" || label.ContentSpan != (source.Span{Start: 26, End: 34}) {
		t.Fatalf("%+v", label)
	}
}

func TestMetadataAssignmentIsNotAnEntityDeclaration(t *testing.T) {
	start, ds := parser.Parse([]byte("usecase-beta\nA@{\n business:true,\n}\n"), nil)
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	assignment := start.Lines[0].Statement.MetadataAssignment
	if assignment == nil || assignment.Target.Token.Text != "A" {
		t.Fatalf("%+v", start.Lines[0])
	}
	property := assignment.Metadata.Properties[0]
	if property.KeyContentSpan != (source.Span{Start: 18, End: 26}) || property.ValueContentSpan != (source.Span{Start: 27, End: 31}) {
		t.Fatalf("%+v", property)
	}
}
