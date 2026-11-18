package requirement

import (
	"slices"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/source"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/requirement"
)

func resolve(t *testing.T, src string) *Model {
	t.Helper()
	document, _ := parser.Parse([]byte(src), nil)
	model, _ := Resolve([]byte(src), document)
	return model
}

func valueList(values []Value) []string {
	out := make([]string, len(values))
	for i, v := range values {
		out[i] = v.Value
	}
	return out
}

func TestFieldsKeepFirstValueAndSpans(t *testing.T) {
	src := "requirementDiagram\nfunctionalRequirement R {\nid: first\nid: second\ntext: detail\nrisk: high\nverifyMethod: inspection\n}\n"
	node := resolve(t, src).Requirements[0]
	type content struct {
		name, kind, id, text, risk, verify string
		fields                             int
	}
	got := content{node.Name, node.Kind, node.Id, node.Text, node.Risk, node.VerifyMethod, len(node.Fields)}
	want := content{"R", "Functional Requirement", "first", "detail", "High", "Inspection", 5}
	if got != want {
		t.Fatal(got)
	}
	first := node.Fields[0]
	if spanText(t, src, first.Span) != "id: first" {
		t.Fatal(first.Span)
	}
	if spanText(t, src, first.KeywordSpan) != "id" {
		t.Fatal(first.KeywordSpan)
	}
	if spanText(t, src, first.ColonSpan) != ":" {
		t.Fatal(first.ColonSpan)
	}
	type delims struct{ open, close string }
	if got := (delims{spanText(t, src, node.Delimiters[0]), spanText(t, src, node.Delimiters[1])}); got != (delims{"{", "}"}) {
		t.Fatal(got)
	}
}

func spanText(t *testing.T, src string, span source.Span) string {
	t.Helper()
	if span.Start < 0 || span.End > len(src) || span.Start > span.End {
		t.Fatalf("span %v outside source", span)
	}
	return src[span.Start:span.End]
}

func TestEmptyDefinitionsHaveEmptyFieldsAndDefaultClasses(t *testing.T) {
	m := resolve(t, "requirementDiagram\nrequirement R {\n}\nelement E {\n}\n")
	r := &m.Requirements[0]
	type empty struct{ id, text, risk, verify string }
	if got := (empty{r.Id, r.Text, r.Risk, r.VerifyMethod}); got != (empty{}) {
		t.Fatal(got)
	}
	if !slices.Equal(valueList(r.Classes), []string{"default"}) {
		t.Fatal(valueList(r.Classes))
	}
	type element struct{ kind, docref string }
	if got := (element{m.Elements[0].Kind, m.Elements[0].Docref}); got != (element{}) {
		t.Fatal(got)
	}
	if !slices.Equal(m.Elements[0].Rows(), []string{"<<Element>>", "E"}) {
		t.Fatal(m.Elements[0].Rows())
	}
	if m.Direction != "TB" {
		t.Fatal(m.Direction)
	}
}

func TestDuplicateDefinitionsKeepFirstFields(t *testing.T) {
	m := resolve(t, "requirementDiagram\nrequirement R {\nid: first\n}\nphysicalRequirement R {\nid: ignored\n}\nrequirement S {\n}\nelement E {\ntype: service\ndocref: first\n}\nelement E {\ntype: ignored\n}\nelement F {\n}\n")
	type triple struct{ name, kind, id string }
	var got []triple
	for i := range m.Requirements {
		got = append(got, triple{m.Requirements[i].Name, m.Requirements[i].Kind, m.Requirements[i].Id})
	}
	want := []triple{{"R", "Requirement", "first"}, {"S", "Requirement", ""}}
	if !slices.Equal(got, want) {
		t.Fatal(got)
	}
	var elements []triple
	for i := range m.Elements {
		elements = append(elements, triple{m.Elements[i].Name, m.Elements[i].Kind, m.Elements[i].Docref})
	}
	wantElements := []triple{{"E", "service", "first"}, {"F", "", ""}}
	if !slices.Equal(elements, wantElements) {
		t.Fatal(elements)
	}
}

func TestNamespacesStaySeparateAndLookupPrefersRequirements(t *testing.T) {
	m := resolve(t, "requirementDiagram\nelement X {\n}\nrequirement X {\n}\nX - traces -> X\nstyle X fill:red\n")
	if len(m.Requirements) != 1 || len(m.Elements) != 1 {
		t.Fatal(len(m.Requirements), len(m.Elements))
	}
	r := m.Relationships[0]
	if r.FromNode.Element || r.ToNode.Element || r.FromNode.Index != 0 || r.ToNode.Index != 0 {
		t.Fatal(r.FromNode, r.ToNode)
	}
	if valueList(m.Requirements[0].Styles)[0] != "fill:red" || len(m.Elements[0].Styles) != 0 {
		t.Fatal(m.Requirements[0].Styles, m.Elements[0].Styles)
	}
}

func TestReversedAndUnresolvedRelationsKeepOrder(t *testing.T) {
	src := "requirementDiagram\nA <- contains - B\nA - copies -> B\nA - derives -> B\nA - satisfies -> B\nA - verifies -> B\nA - refines -> B\nA - traces -> A\n"
	m := resolve(t, src)
	if len(m.Requirements) != 0 || len(m.Elements) != 0 {
		t.Fatal(len(m.Requirements), len(m.Elements))
	}
	kinds := make([]string, len(m.Relationships))
	for i, r := range m.Relationships {
		kinds[i] = r.Kind
	}
	want := []string{"contains", "copies", "derives", "satisfies", "verifies", "refines", "traces"}
	if !slices.Equal(kinds, want) {
		t.Fatal(kinds)
	}
	first := m.Relationships[0]
	type relation struct {
		from, to, label  string
		fromNode, toNode *NodeRef
		fromSp           source.Span
	}
	got := relation{first.From.Value, first.To.Value, first.Label, first.FromNode, first.ToNode, first.From.Span}
	wantRelation := relation{"B", "A", "<<contains>>", nil, nil, source.Span{Start: 35, End: 36}}
	if got != wantRelation {
		t.Fatal(got)
	}
	if spanText(t, src, first.ArrowSpan) != "<-" {
		t.Fatal(first.ArrowSpan)
	}
}

func TestLaterDefinitionsResolveEndpointRecords(t *testing.T) {
	m := resolve(t, "requirementDiagram\nR - verifies -> E\nelement E {\n}\nrequirement R {\n}\n")
	r := m.Relationships[0]
	if r.FromNode == nil || r.FromNode.Element || r.ToNode == nil || !r.ToNode.Element {
		t.Fatal(r.FromNode, r.ToNode)
	}
}

func TestClassesAppendAndLateDefinitionsReachNodes(t *testing.T) {
	m := resolve(t, "requirementDiagram\nclassDef hot fill:red,color:blue\nrequirement R:::hot {\n}\nrequirement R:::unknown {\n}\nclass R hot\nclassDef hot stroke:black\n")
	node := &m.Requirements[0]
	if !slices.Equal(valueList(node.Classes), []string{"default", "hot", "unknown", "hot"}) {
		t.Fatal(valueList(node.Classes))
	}
	if !slices.Equal(valueList(node.Styles), []string{"fill:red", "color:blue", "fill:red", "color:blue", "stroke:black"}) {
		t.Fatal(valueList(node.Styles))
	}
	if !slices.Equal(valueList(m.ClassDefinitions[0].TextStyles), []string{"color:blue"}) {
		t.Fatal(valueList(m.ClassDefinitions[0].TextStyles))
	}
}

func TestDirectStylesStopAtFirstMissingTarget(t *testing.T) {
	m := resolve(t, "requirementDiagram\nrequirement A {\n}\nelement B {\n}\nstyle A,Missing,B fill:red,stroke:blue\nstyle A color:green\nclass Missing,B unknown\n")
	if !slices.Equal(valueList(m.Requirements[0].Styles), []string{"fill:red", "stroke:blue", "color:green"}) {
		t.Fatal(valueList(m.Requirements[0].Styles))
	}
	if len(m.Elements[0].Styles) != 0 {
		t.Fatal(m.Elements[0].Styles)
	}
	if !slices.Equal(valueList(m.Elements[0].Classes), []string{"default", "unknown"}) {
		t.Fatal(valueList(m.Elements[0].Classes))
	}
}

func TestDirectionsAndAccessibilityUseLastTrimmedValue(t *testing.T) {
	m := resolve(t, "accTitle: leading\nrequirementDiagram\ndirection LR\ndirection BT\naccTitle: final title   \naccDescr: first\naccDescr { final description }\n")
	if m.Direction != "BT" || m.AccTitle != "final title" || m.AccDescr != "final description" {
		t.Fatal(m.Direction, m.AccTitle, m.AccDescr)
	}
}

func TestEnumValuesMapToDisplayStrings(t *testing.T) {
	m := resolve(t, "requirementDiagram\ninterfaceRequirement A {\nrisk: medium\nverifyMethod: analysis\n}\nperformanceRequirement B {\nverifyMethod: demonstration\n}\nphysicalRequirement C {\n}\ndesignConstraint D {\n}\n")
	kinds := make([]string, len(m.Requirements))
	for i, r := range m.Requirements {
		kinds[i] = r.Kind
	}
	want := []string{"Interface Requirement", "Performance Requirement", "Physical Requirement", "Design Constraint"}
	if !slices.Equal(kinds, want) {
		t.Fatal(kinds)
	}
	if m.Requirements[0].Risk != "Medium" || m.Requirements[0].VerifyMethod != "Analysis" {
		t.Fatal(m.Requirements[0])
	}
}

func TestLabelsDecodeEntitiesOnce(t *testing.T) {
	src := "requirementDiagram\nrequirement \"R#38;\" {\ntext: \"#35;name; #65; #unknown;\"\n}\nstyle \"R#38;\" fill:#abc\n"
	node := &resolve(t, src).Requirements[0]
	if node.Name != "R#38;" || node.Text != "#name; A #unknown;" {
		t.Fatal(node.Name, node.Text)
	}
	if !slices.Equal(node.Rows(), []string{"<<Requirement>>", "R&", "Text: #name; A #unknown;"}) {
		t.Fatal(node.Rows())
	}
	if valueList(node.Styles)[0] != "fill:#abc" {
		t.Fatal(node.Styles)
	}
}

func TestEmptyFirstFieldWins(t *testing.T) {
	node := &resolve(t, "requirementDiagram\nrequirement R {\nid: \"\"\nid: later\n}\n").Requirements[0]
	if node.Id != "" || len(node.Fields) != 2 {
		t.Fatal(node.Id, len(node.Fields))
	}
	if !slices.Equal(node.Rows(), []string{"<<Requirement>>", "R"}) {
		t.Fatal(node.Rows())
	}
}

func TestRepeatedElementFieldsKeepFirstText(t *testing.T) {
	node := &resolve(t, "requirementDiagram\nelement E {\ndocref: first\ntype: service\ndocref: ignored\ntype: ignored\n}\n").Elements[0]
	if !slices.Equal(node.Rows(), []string{"<<Element>>", "E", "Type: service", "Doc Ref: first"}) {
		t.Fatal(node.Rows())
	}
	names := make([]string, len(node.Fields))
	for i, f := range node.Fields {
		names[i] = f.Name
	}
	if !slices.Equal(names, []string{"docref", "type", "docref", "type"}) {
		t.Fatal(names)
	}
}

func TestTextClassStylesSelectLowercaseColor(t *testing.T) {
	class := resolve(t, "requirementDiagram\nclassDef A fill:colorfill,COLOR:red,color:green\n").ClassDefinitions[0]
	if !slices.Equal(valueList(class.TextStyles), []string{"bgFill:colorfill", "color:green"}) {
		t.Fatal(valueList(class.TextStyles))
	}
	if !slices.Equal(valueList(class.Styles), []string{"fill:colorfill", "COLOR:red", "color:green"}) {
		t.Fatal(valueList(class.Styles))
	}
}
