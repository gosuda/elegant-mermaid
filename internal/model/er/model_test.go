package er

import (
	"fmt"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	erparser "github.com/gosuda/elegant-mermaid/internal/syntax/er"
)

func resolved(t *testing.T, text string) (*Model, []diag.Diagnostic) {
	t.Helper()
	start, ds := erparser.Parse([]byte(text), nil)
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	m, resolved := Resolve(nil, start)
	return m, resolved
}

func TestImplicitEntitiesKeepFirstInsertionOrder(t *testing.T) {
	m, ds := resolved(t, "erDiagram\nB ||--o{ A : owns\nA\nB\n")
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	if m.Entities[0].ID != "B" || m.Entities[1].ID != "A" {
		t.Fatal(m.Entities)
	}
	if fmt.Sprint(m.Entities[0].Classes) != "[default]" {
		t.Fatal(m.Entities[0].Classes)
	}
}

func TestFirstNonemptyAliasWinsAfterImplicitDeclaration(t *testing.T) {
	m, _ := resolved(t, "erDiagram\nA ||--|| B : owns\nA [First]\nA [Second]\n")
	if m.Entities[0].Label != "First" {
		t.Fatal(m.Entities[0])
	}
	if m.Relationships[0].From != "A" {
		t.Fatal(m.Relationships[0])
	}
}

func TestRepeatedBlocksAppendAttributesAndKeys(t *testing.T) {
	m, ds := resolved(t, "erDiagram\nA { int? id PK,FK,PK \"key\" }\nA { string id UK }\n")
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	attributes := m.Entities[0].Attributes
	if len(attributes) != 2 {
		t.Fatal(attributes)
	}
	if attributes[0].AttributeType != "int?" || fmt.Sprint(attributes[0].Keys) != "[PK FK PK]" || attributes[0].Comment != "key" || !attributes[0].Nullable {
		t.Fatal(attributes[0])
	}
	if attributes[1].Comment != "" {
		t.Fatal(attributes[1])
	}
}

func TestAttributesKeepBackticksAndFieldSpans(t *testing.T) {
	text := "erDiagram\nA { `long type` `field name` }\n"
	m, ds := resolved(t, text)
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	attribute := m.Entities[0].Attributes[0]
	if attribute.AttributeType != "long type" || attribute.Name != "field name" {
		t.Fatal(attribute)
	}
	if text[attribute.TypeSpan.Start:attribute.TypeSpan.End] != "`long type`" {
		t.Fatal(attribute.TypeSpan)
	}
	if text[attribute.NameSpan.Start:attribute.NameSpan.End] != "`field name`" {
		t.Fatal(attribute.NameSpan)
	}
}

func TestRepeatedSelfRelationshipsKeepMarkersAndDeclarationIndex(t *testing.T) {
	m, _ := resolved(t, "erDiagram\nA |o..|{ A : relates\nA }o--|| A : other\n")
	if len(m.Relationships) != 2 {
		t.Fatal(m.Relationships)
	}
	first, second := m.Relationships[0], m.Relationships[1]
	if first.MarkerStart != "one_or_more" || first.MarkerEnd != "zero_or_one" || first.Identifying || first.Index != 0 {
		t.Fatal(first)
	}
	if second.MarkerStart != "only_one" || second.MarkerEnd != "zero_or_more" || !second.Identifying || second.Index != 1 {
		t.Fatal(second)
	}
}

func TestSubgraphsKeepNestedEmptyGroupsAndLocalDirection(t *testing.T) {
	m, ds := resolved(t, "erDiagram\ndirection LR\nsubgraph Outer [Outer group]\n direction BT\n subgraph Inner\n A\n end\n subgraph Empty\n end\nend\ndirection RL\n")
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	if m.Direction != "RL" {
		t.Fatal(m.Direction)
	}
	want := []string{"Inner 2 1", "Empty 2 0", "Outer -1 2"}
	var got []string
	for i := range m.Groups {
		got = append(got, fmt.Sprintf("%s %d %d", m.Groups[i].ID, m.Groups[i].Parent, len(m.Groups[i].Members)))
	}
	if fmt.Sprint(got) != fmt.Sprint(want) {
		t.Fatal(got)
	}
	if m.Groups[2].Direction != "BT" || m.Groups[2].Label != "Outer group" {
		t.Fatal(m.Groups[2])
	}
}

func TestFirstCompletedGroupClaimsMembershipAndAliasOnlyReturnsNothing(t *testing.T) {
	m, _ := resolved(t, "erDiagram\nsubgraph First\nA\nB [Alias]\nend\nsubgraph Second\nA\nend\n")
	if len(m.Groups) != 2 || len(m.Groups[0].Members) != 1 || len(m.Groups[1].Members) != 0 {
		t.Fatal(m.Groups)
	}
	if m.Entities[0].Parent != 0 || m.Entities[1].Parent != -1 {
		t.Fatal(m.Entities)
	}
}

func TestEndpointBindingObservesSubgraphCompletion(t *testing.T) {
	m, _ := resolved(t, "erDiagram\nG ||--|| A : before\nsubgraph G\nB\nend\nG ||--|| A : after\n")
	if m.Relationships[0].FromTarget.Group || m.Relationships[0].FromTarget.Index != 0 {
		t.Fatal(m.Relationships[0].FromTarget)
	}
	if !m.Relationships[1].FromTarget.Group || m.Relationships[1].FromTarget.Index != 0 {
		t.Fatal(m.Relationships[1].FromTarget)
	}
}

func TestDefinitionsCompileLateAndMissingStyleTargetsAreIgnored(t *testing.T) {
	m, ds := resolved(t, "erDiagram\nclass Missing hot\nstyle Missing fill:red\nA:::hot\nstyle A stroke:blue\nclass A hot\nclassDef hot fill:#abc,color:red\nclassDef hot stroke:#123\n")
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	if len(m.Entities) != 1 {
		t.Fatal(m.Entities)
	}
	if fmt.Sprint(m.Entities[0].Classes) != "[default hot hot]" {
		t.Fatal(m.Entities[0].Classes)
	}
	if fmt.Sprint(m.Definitions[0].Styles) != "[fill:#abc color:red stroke:#123]" {
		t.Fatal(m.Definitions[0].Styles)
	}
	if fmt.Sprint(m.Definitions[0].TextStyles) != "[color:red]" {
		t.Fatal(m.Definitions[0].TextStyles)
	}
}

func TestAccessibilityTrimsAndReplaces(t *testing.T) {
	m, _ := resolved(t, "erDiagram\naccTitle: first\naccTitle: last \naccDescr: detail \nA\n")
	if m.AccTitle != "last" || m.AccDescr != "detail" {
		t.Fatal(m.AccTitle, m.AccDescr)
	}
}

func TestEmptyBlocksAndMissingAttributeFieldsKeepDefaults(t *testing.T) {
	m, ds := resolved(t, "erDiagram\nA {}\nA { string value }\n")
	if len(ds) != 0 || len(m.Entities) != 1 {
		t.Fatal(m.Entities)
	}
	attributes := m.Entities[0].Attributes
	if len(attributes) != 1 || len(attributes[0].Keys) != 0 || attributes[0].Comment != "" || attributes[0].Nullable {
		t.Fatal(attributes)
	}
}

func TestLabelEntitiesDecodeWithoutTouchingIdentityOrStyles(t *testing.T) {
	m, ds := resolved(t, "erDiagram\nA [\"A #amp; B\"]\nstyle A fill:#abc\nA ||--|| B : \"#35; #amp;\"\n")
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	if m.Entities[0].DisplayName() != "A & B" || m.Entities[0].ID != "A" {
		t.Fatal(m.Entities[0])
	}
	if fmt.Sprint(m.Entities[0].Styles) != "[fill:#abc]" {
		t.Fatal(m.Entities[0].Styles)
	}
	if m.Relationships[0].Label != "# &" {
		t.Fatal(m.Relationships[0].Label)
	}
}

func TestDuplicateSubgraphsKeepClosureRecordsAndLastLookup(t *testing.T) {
	m, ds := resolved(t, "erDiagram\nsubgraph G\nA\nend\nsubgraph G\nB\nend\nG ||--|| C : owns\n")
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	if len(m.Groups) != 2 || m.Groups[0].ID != "G" || m.Groups[1].ID != "G" {
		t.Fatal(m.Groups)
	}
	if !m.Relationships[0].FromTarget.Group || m.Relationships[0].FromTarget.Index != 1 {
		t.Fatal(m.Relationships[0].FromTarget)
	}
}
