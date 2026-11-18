package er_test

import (
	"fmt"
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/er"
)

func statements(start *parser.Start) []*parser.Statement {
	var out []*parser.Statement
	for i := range start.Document.Lines {
		if line := start.Document.Lines[i].Statement; line != nil {
			out = append(out, line)
		}
	}
	return out
}

func wantDiag(t *testing.T, ds []diag.Diagnostic, code, message string, span source.Span) {
	t.Helper()
	if len(ds) != 1 {
		t.Fatal(ds)
	}
	if ds[0].Code != code || ds[0].Message != message || ds[0].Span != span {
		t.Fatal(ds[0])
	}
}

func TestEmptyHeaderParses(t *testing.T) {
	start, ds := parser.Parse([]byte("erDiagram"), nil)
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	if start.Span != (source.Span{Start: 0, End: 9}) {
		t.Fatal(start.Span)
	}
	if start.Document.Span != (source.Span{Start: 9, End: 9}) || len(start.Document.Lines) != 0 {
		t.Fatal(start.Document)
	}
}

func TestAdjacentDeclarationsKeepEmptyBlock(t *testing.T) {
	start, ds := parser.Parse([]byte("erDiagram\nA B C{}"), nil)
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	nodes := statements(start)
	if len(nodes) != 3 || nodes[0].Span != (source.Span{Start: 10, End: 11}) {
		t.Fatal(nodes)
	}
	entity := nodes[2].Entity
	if entity == nil || entity.Attributes == nil || len(entity.Attributes.Attributes) != 0 {
		t.Fatal(entity)
	}
	if entity.Delimiters == nil || entity.Delimiters[0] != (source.Span{Start: 15, End: 16}) || entity.Delimiters[1] != (source.Span{Start: 16, End: 17}) {
		t.Fatal(entity.Delimiters)
	}
}

func entityOf(start *parser.Start) *parser.EntityStatement {
	return statements(start)[0].Entity
}

func TestAliasAndInlineClassesPreserveBorrowedIdentity(t *testing.T) {
	start, ds := parser.Parse([]byte("erDiagram\nA[\"é\"]:::red,blue {}"), nil)
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	entity := entityOf(start)
	if entity == nil || entity.Name.Name != "A" || entity.Attributes == nil {
		t.Fatal(entity)
	}
	if entity.Alias == nil || entity.Alias.Name != "é" || entity.Alias.Span != (source.Span{Start: 12, End: 16}) {
		t.Fatal(entity.Alias)
	}
	wantClasses(t, entity.Classes, "red", "blue")
}

func wantClasses(t *testing.T, list *parser.IdList, want ...string) {
	t.Helper()
	if list == nil || len(list.Names) != len(want) {
		t.Fatal(list)
	}
	for i := range want {
		if list.Names[i].Text != want[i] {
			t.Fatal(list)
		}
	}
}

func TestAttributeModesNullableKeysAndComments(t *testing.T) {
	start, ds := parser.Parse([]byte("erDiagram\nA {\n`custom type`? `first name` pk, FK,uk \"é\"\nint second\n}"), nil)
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	attributes := entityOf(start).Attributes
	if attributes == nil || len(attributes.Attributes) != 2 {
		t.Fatal(attributes)
	}
	attribute := attributes.Attributes[0]
	if attribute.AttributeType.Word.Text != "custom type" || attribute.AttributeType.Span != (source.Span{Start: 14, End: 28}) {
		t.Fatal(attribute.AttributeType)
	}
	if attribute.Name.Word.Text != "first name" {
		t.Fatal(attribute.Name)
	}
	wantKeys(t, attribute.Keys, "PK", "FK", "UK")
	if attribute.Comment == nil || attribute.Comment.Text != "é" {
		t.Fatal(attribute.Comment)
	}
}

func wantKeys(t *testing.T, list *parser.AttributeKeyTypeList, want ...string) {
	t.Helper()
	if list == nil || len(list.Keys) != len(want) {
		t.Fatal(list)
	}
	for i := range want {
		if list.Keys[i].Value != want[i] {
			t.Fatal(list)
		}
	}
}

func TestRelationshipRetainsEachMarkerClassAndLineKind(t *testing.T) {
	start, ds := parser.Parse([]byte("erDiagram\nA:::red ||..o{ B:::blue: \"has many\""), nil)
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	relationship := statements(start)[0].Relationship
	if relationship == nil {
		t.Fatal("not a relationship")
	}
	if relationship.From.Name != "A" || relationship.To.Name != "B" || relationship.Role.Label != "has many" {
		t.Fatal(relationship)
	}
	if relationship.Relation.Left.Kind != parser.CardOnlyOne || relationship.Relation.Right.Kind != parser.CardZeroOrMore {
		t.Fatal(relationship.Relation)
	}
	if relationship.Relation.RelType.Identifying {
		t.Fatal("dotted relationship must stay non-identifying")
	}
	if relationship.Relation.Span != (source.Span{Start: 18, End: 24}) {
		t.Fatal(relationship.Relation.Span)
	}
}

func TestLineSpellingsAndParentMarkerParse(t *testing.T) {
	for _, line := range []string{"..", "--", "to", "optionally to", ".-", "-."} {
		text := fmt.Sprintf("erDiagram\nA ||%s|| B: r", line)
		start, ds := parser.Parse([]byte(text), nil)
		if len(ds) != 0 {
			t.Fatal(text, ds)
		}
		relation := statements(start)[0].Relationship
		if relation == nil || relation.Relation.Left.Kind != parser.CardOnlyOne {
			t.Fatal(text, relation)
		}
		identifying := line == "--" || line == "to"
		if relation.Relation.RelType.Identifying != identifying {
			t.Fatal(text, relation.Relation.RelType)
		}
	}
}

func TestDirectionConsumesPrefixSuffixWithTBPrecedence(t *testing.T) {
	text := "erDiagram\nnoise direction LR then direction TB suffix\rtrailingdirection BTsuffix\n"
	start, ds := parser.Parse([]byte(text), nil)
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	nodes := statements(start)
	if len(nodes) != 2 {
		t.Fatal(nodes)
	}
	if nodes[0].Kind != parser.KindDirection {
		t.Fatal(nodes[0])
	}
	if nodes[0].Direction.Value != "TB" || nodes[0].Direction.Span != (source.Span{Start: 10, End: 53}) {
		t.Fatal(nodes[0].Direction)
	}
}

func TestClassDefComponents(t *testing.T) {
	text := "erDiagram\nclassDef red,blue fill:#abc,color:red;\nclass A,B red,blue\nstyle A,B stroke:#123\n"
	start, ds := parser.Parse([]byte(text), nil)
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	nodes := statements(start)
	if len(nodes) != 3 || nodes[0].ClassDef == nil {
		t.Fatal(nodes)
	}
	definition := nodes[0].ClassDef
	if len(definition.IDs.Names) != 2 || len(definition.Styles.Styles) != 2 {
		t.Fatal(definition)
	}
	var texts []string
	for _, c := range definition.Styles.Styles[0].Components {
		texts = append(texts, c.Text)
	}
	if fmt.Sprint(texts) != "[fill : # abc]" {
		t.Fatal(texts)
	}
}

func TestStyleModeSemicolonRetainsMode(t *testing.T) {
	tokens := parser.Lex([]byte("style A fill:red;class B red\nC"), nil)
	classFound, entityFound := false, false
	for _, tok := range tokens {
		if tok.Kind == "STYLE_TEXT" && tok.Text == "class" {
			classFound = true
		}
		if tok.Kind == "UNICODE_TEXT" && tok.Text == "C" {
			entityFound = true
		}
	}
	if !classFound || !entityFound {
		t.Fatal(classFound, entityFound)
	}
}

func TestAccessibilitySingleMultilineAndEmpty(t *testing.T) {
	text := "erDiagram\raccTitle: é\r\naccDescr: d\naccDescr {first\rsecond}\naccDescr {}"
	start, ds := parser.Parse([]byte(text), nil)
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	nodes := statements(start)
	var values []string
	for _, node := range nodes {
		if node.Kind != parser.KindAccessibility {
			continue
		}
		values = append(values, fmt.Sprintf("%v %q", node.Accessibility.Title, node.Accessibility.Value.Text))
	}
	want := []string{"true \"é\"", "false \"d\"", "false \"first\\rsecond\"", "false \"\""}
	if len(values) != len(want) {
		t.Fatal(values)
	}
	for i := range want {
		if values[i] != want[i] {
			t.Fatal(i, values)
		}
	}
	if nodes[0].Span != (source.Span{Start: 10, End: 22}) {
		t.Fatal(nodes[0].Span)
	}
}

func subChildren(sub *parser.SubgraphStatement) []*parser.Statement {
	var out []*parser.Statement
	for i := range sub.Document.Lines {
		if line := sub.Document.Lines[i].Statement; line != nil {
			out = append(out, line)
		}
	}
	return out
}

func TestNestedSubgraphTitleAndChildren(t *testing.T) {
	start, ds := parser.Parse([]byte("erDiagram\nsubgraph Outer[First Second]\nsubgraph Empty\nend\nA[Alias]\nend\nB"), nil)
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	sub := statements(start)[0].Subgraph
	if sub == nil || sub.Header.Title == nil || len(sub.Header.Title.Parts) != 2 {
		t.Fatal(sub)
	}
	if sub.Header.Title.Parts[0].Name != "First" || sub.Header.Title.Parts[1].Name != "Second" {
		t.Fatal(sub.Header.Title)
	}
	children := subChildren(sub)
	if len(children) != 2 {
		t.Fatal(children)
	}
}

func TestEmptyNestedSubgraphKeepsZeroLines(t *testing.T) {
	start, ds := parser.Parse([]byte("erDiagram\nsubgraph Outer[First Second]\nsubgraph Empty\nend\nA[Alias]\nend\nB"), nil)
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	sub := statements(start)[0].Subgraph
	if sub == nil {
		t.Fatal("not a subgraph")
	}
	children := subChildren(sub)
	if len(children) != 2 {
		t.Fatal(children)
	}
	nested := children[0].Subgraph
	if nested == nil || len(nested.Document.Lines) != 0 {
		t.Fatal(nested)
	}
}

func TestUnknownStatementRecoversAtPhysicalLines(t *testing.T) {
	start, ds := parser.Parse([]byte("erDiagram\n@ junk\r\nB\rC"), nil)
	wantDiag(t, ds, "er/unknown-statement", "unknown statement @", source.Span{Start: 10, End: 16})
	if len(statements(start)) != 2 {
		t.Fatal(start)
	}
}

func TestBadRelationshipRecoversWithoutAliasEndpoint(t *testing.T) {
	start, ds := parser.Parse([]byte("erDiagram\nA ||--|| B[Alias]: r\nC"), nil)
	wantDiag(t, ds, "er/unexpected-token", "unexpected [, expected one of: COLON", source.Span{Start: 20, End: 21})
	nodes := statements(start)
	if len(nodes) != 1 || nodes[0].Entity == nil || nodes[0].Entity.Name.Name != "C" {
		t.Fatal(nodes)
	}
}

func TestBadAttributeRecoversInsideBlockAndPreservesClose(t *testing.T) {
	start, ds := parser.Parse([]byte("erDiagram\nA {\nint @\nstring good\n}\nB"), nil)
	wantDiag(t, ds, "er/unexpected-token", "unexpected @, expected one of: ATTRIBUTE_WORD", source.Span{Start: 18, End: 19})
	nodes := statements(start)
	if len(nodes) != 2 {
		t.Fatal(nodes)
	}
	attributes := nodes[0].Entity.Attributes
	if attributes == nil || len(attributes.Attributes) != 1 || attributes.Attributes[0].Name.Word.Text != "good" {
		t.Fatal(attributes)
	}
}

func TestUnterminatedOpenersReportOneExactDiagnostic(t *testing.T) {
	for _, want := range [][3]any{
		{"erDiagram\n\"é", 10, "unterminated \""},
		{"erDiagram\nA { `é", 14, "unterminated `"},
		{"erDiagram\nA { int id", 12, "unterminated {"},
		{"erDiagram\nA { int id \"é", 21, "unterminated \""},
		{"erDiagram\naccDescr {é", 19, "unterminated {"},
		{"erDiagram\nsubgraph S\nA", 10, "unterminated subgraph"},
	} {
		text := want[0].(string)
		_, ds := parser.Parse([]byte(text), nil)
		wantDiag(t, ds, "er/unterminated", want[2].(string), source.Span{Start: want[1].(int), End: len(text)})
	}
}

func TestLevelSixtyFiveStopsWithSharedLimit(t *testing.T) {
	var b strings.Builder
	b.WriteString("erDiagram\n")
	for range 65 {
		b.WriteString("subgraph S\n")
	}
	for range 65 {
		b.WriteString("end\n")
	}
	_, ds := parser.Parse([]byte(b.String()), nil)
	wantDiag(t, ds, "limit/nesting-depth", "nesting depth exceeds 64", source.Span{Start: 714, End: 722})
}

func TestParentCardinalityUsesOnlyPunctuationLookahead(t *testing.T) {
	for _, line := range []string{"..", "--", ".-", "-."} {
		text := fmt.Sprintf("erDiagram\nA u%s|| B: r", line)
		start, ds := parser.Parse([]byte(text), nil)
		if len(ds) != 0 {
			t.Fatal(text, ds)
		}
		relation := statements(start)[0].Relationship
		if relation == nil || relation.Relation.Left.Kind != parser.CardMdParent || relation.Relation.Left.Span != (source.Span{Start: 12, End: 13}) {
			t.Fatal(text, relation)
		}
	}
	tokens := parser.Lex([]byte("user u|"), nil)
	if tokens[0].Kind != "UNICODE_TEXT" || tokens[1].Kind != "MD_PARENT" {
		t.Fatal(tokens)
	}
}

func TestStyleStatementSpansOmitTerminatingSeparator(t *testing.T) {
	start, ds := parser.Parse([]byte("erDiagram\nstyle A fill:red;\nclassDef red color:blue"), nil)
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	nodes := statements(start)
	if nodes[0].Span != (source.Span{Start: 10, End: 26}) || nodes[0].Style.Span != nodes[0].Span {
		t.Fatal(nodes[0])
	}
	if nodes[1].Span != (source.Span{Start: 28, End: 51}) || nodes[1].ClassDef.Span != nodes[1].Span {
		t.Fatal(nodes[1])
	}
}

func TestInvalidFirstAttributeRecoversToNextLine(t *testing.T) {
	start, ds := parser.Parse([]byte("erDiagram\nA {\n@ bad\nint good\n}"), nil)
	wantDiag(t, ds, "er/unexpected-token", "unexpected @, expected one of: ATTRIBUTE_WORD", source.Span{Start: 14, End: 15})
	attributes := entityOf(start).Attributes
	if attributes == nil || len(attributes.Attributes) != 1 || attributes.Attributes[0].Name.Word.Text != "good" {
		t.Fatal(attributes)
	}
}

func TestBadRelationshipPreservesEnclosingSubgraphClose(t *testing.T) {
	start, ds := parser.Parse([]byte("erDiagram\nsubgraph S\nA ||-- end\nB"), nil)
	wantDiag(t, ds, "er/unexpected-token",
		"unexpected end\n, expected one of: MD_PARENT, ONE_OR_MORE, ONLY_ONE, ZERO_OR_MORE, ZERO_OR_ONE",
		source.Span{Start: 28, End: 32})
	nodes := statements(start)
	if len(nodes) != 2 {
		t.Fatal(nodes)
	}
	sub := nodes[0].Subgraph
	if sub == nil {
		t.Fatal(nodes[0])
	}
	for i := range sub.Document.Lines {
		if sub.Document.Lines[i].Statement != nil {
			t.Fatal("malformed relationship left a partial statement")
		}
	}
}

func TestQuotedEmptyRole(t *testing.T) {
	start, ds := parser.Parse([]byte("erDiagram\nA ||--|| B: \"\""), nil)
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	role := statements(start)[0].Relationship.Role
	if role.Label != "" || role.Span != (source.Span{Start: 22, End: 24}) {
		t.Fatal(role)
	}
}

func TestQuoteRulePrecedence(t *testing.T) {
	tokens := parser.Lex([]byte("\"clean\" \"has%percent\" \"\""), nil)
	var got []string
	for _, tok := range tokens {
		got = append(got, tok.Kind)
	}
	if fmt.Sprint(got) != "[ENTITY_NAME WORD WORD EOF]" {
		t.Fatal(got)
	}
}

func TestNumericRelationshipEndpoints(t *testing.T) {
	start, ds := parser.Parse([]byte("erDiagram\n1 ||--|| 42: r\n2.5 {int x string? y}\n1"), nil)
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	relationship := statements(start)[0].Relationship
	if relationship == nil || relationship.From.Name != "1" || relationship.To.Name != "42" {
		t.Fatal(relationship)
	}
}

func TestDecimalEntityAttributes(t *testing.T) {
	start, ds := parser.Parse([]byte("erDiagram\n1 ||--|| 42: r\n2.5 {int x string? y}\n1"), nil)
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	entity := statements(start)[1].Entity
	if entity == nil || entity.Name.Name != "2.5" || entity.Attributes == nil || len(entity.Attributes.Attributes) != 2 {
		t.Fatal(entity)
	}
	question := entity.Attributes.Attributes[1].AttributeType.Question
	if question == nil || question.Span != (source.Span{Start: 42, End: 43}) {
		t.Fatal(question)
	}
}

func TestToPrefixedSubgraphIDRemainsWhole(t *testing.T) {
	start, ds := parser.Parse([]byte("erDiagram\nsubgraph TOP\nend\nA ||--|| TOP : links\nTOP ||--|| B : links"), nil)
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	nodes := statements(start)
	if len(nodes) != 3 {
		t.Fatal(nodes)
	}
	header := nodes[0].Subgraph.Header
	if header.ID.Name != "TOP" || header.ID.Span != (source.Span{Start: 19, End: 22}) {
		t.Fatal(header)
	}
}

func TestToPrefixedSubgraphIncomingRelationship(t *testing.T) {
	start, ds := parser.Parse([]byte("erDiagram\nsubgraph TOP\nend\nA ||--|| TOP : links\nTOP ||--|| B : links"), nil)
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	incoming := statements(start)[1].Relationship
	if incoming == nil || incoming.From.Name != "A" || incoming.To.Name != "TOP" || incoming.Role.Label != "links" {
		t.Fatal(incoming)
	}
	if incoming.To.Span != (source.Span{Start: 36, End: 39}) {
		t.Fatal(incoming.To.Span)
	}
	if incoming.Relation.Left.Kind != parser.CardOnlyOne || incoming.Relation.Right.Kind != parser.CardOnlyOne {
		t.Fatal(incoming.Relation)
	}
}

func TestToPrefixedSubgraphOutgoingRelationship(t *testing.T) {
	start, ds := parser.Parse([]byte("erDiagram\nsubgraph TOP\nend\nA ||--|| TOP : links\nTOP ||--|| B : links"), nil)
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	outgoing := statements(start)[2].Relationship
	if outgoing == nil || outgoing.From.Name != "TOP" || outgoing.To.Name != "B" {
		t.Fatal(outgoing)
	}
	if outgoing.From.Span != (source.Span{Start: 48, End: 51}) {
		t.Fatal(outgoing.From.Span)
	}
}
