package c4_test

import (
	"testing"
	"unicode/utf8"

	model "github.com/gosuda/elegant-mermaid/internal/model/c4"
	"github.com/gosuda/elegant-mermaid/internal/source"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/c4"
)

func resolve(t *testing.T, src string) *model.Model {
	t.Helper()
	start, ds := parser.Parse([]byte(src), nil)
	if len(ds) != 0 {
		t.Fatalf("parse diagnostics %v", ds)
	}
	m, more := model.Resolve([]byte(src), start)
	if len(more) != 0 {
		t.Fatalf("resolve diagnostics %v", more)
	}
	if m == nil {
		t.Fatal("nil model")
	}
	return m
}

func field(t *testing.T, fields []model.Field, name string) model.Text {
	t.Helper()
	for _, field := range fields {
		if field.Name == name {
			return field.Value
		}
	}
	t.Fatalf("missing field %q in %v", name, fields)
	return model.Text{}
}

func hasField(fields []model.Field, name string) bool {
	for _, field := range fields {
		if field.Name == name {
			return true
		}
	}
	return false
}

func TestAllHeadersKeepC4TypeAndDirection(t *testing.T) {
	for _, header := range []string{"C4Context", "C4Container", "C4Component", "C4Dynamic", "C4Deployment"} {
		m := resolve(t, header+"\nPerson(p, \"Person\")\n")
		if m.C4Type != header || m.Direction != "TB" {
			t.Fatalf("%s: type %q direction %q", header, m.C4Type, m.Direction)
		}
	}
	for _, direction := range []string{"TB", "BT", "LR", "RL"} {
		m := resolve(t, "direction "+direction)
		if m.Direction != direction || m.C4Type != "" {
			t.Fatalf("%s: direction %q type %q", direction, m.Direction, m.C4Type)
		}
	}
}

func TestElementVariantsKeepFamilyShapeAndExternalFlag(t *testing.T) {
	names := []string{
		"Person", "Person_Ext",
		"System", "System_Ext", "SystemDb", "SystemDb_Ext", "SystemQueue", "SystemQueue_Ext",
		"Container", "Container_Ext", "ContainerDb", "ContainerDb_Ext", "ContainerQueue", "ContainerQueue_Ext",
		"Component", "Component_Ext", "ComponentDb", "ComponentDb_Ext", "ComponentQueue", "ComponentQueue_Ext",
	}
	kinds := []string{
		"person", "external_person",
		"system", "external_system", "system_db", "external_system_db", "system_queue", "external_system_queue",
		"container", "external_container", "container_db", "external_container_db", "container_queue", "external_container_queue",
		"component", "external_component", "component_db", "external_component_db", "component_queue", "external_component_queue",
	}
	src := "C4Context\n"
	for i, name := range names {
		src += name + "(a" + string(rune('0'+i/10)) + string(rune('0'+i%10)) + ", \"Label\")\n"
	}
	m := resolve(t, src)
	if len(m.Elements) != len(names) {
		t.Fatalf("elements %d", len(m.Elements))
	}
	for i, element := range m.Elements {
		if element.Kind != kinds[i] {
			t.Fatalf("%s: kind %q", names[i], element.Kind)
		}
		if element.MacroName != names[i] {
			t.Fatalf("%s: macro %q", names[i], element.MacroName)
		}
	}
}

func assertUpdatedElementIdentity(t *testing.T, first model.Element) {
	t.Helper()
	if first.ID != "a" || first.Kind != "external_system" || first.Parent != "g" || first.Label.Value != "Last" {
		t.Fatalf("first %+v", first)
	}
}

func TestRepeatedElementUpdatesInPlaceKeepingFieldsAndPosition(t *testing.T) {
	m := resolve(t, "C4Context\nContainer(a, \"First\", \"Rust\", \"Description\")\nPerson(b, \"B\")\nBoundary(g, \"Group\") {\nSystem_Ext(a, \"Last\")\n}\n")
	if len(m.Elements) != 2 {
		t.Fatalf("elements %d", len(m.Elements))
	}
	first := m.Elements[0]
	assertUpdatedElementIdentity(t, first)
	if got := field(t, first.Fields, "descr").Value; got != "Description" {
		t.Fatalf("descr %q", got)
	}
	if got := field(t, first.Fields, "techn").Value; got != "Rust" {
		t.Fatalf("techn %q", got)
	}
	if m.Declarations[0].Target != model.DeclarationElement || m.Declarations[0].Index != 0 || m.Declarations[1].Index != 1 {
		t.Fatalf("declarations %+v", m.Declarations)
	}
}

func TestRequiredAliasIsPositionalAndMissingLabelIsEmpty(t *testing.T) {
	m := resolve(t, "C4Context\nPerson(a, \"First\")\nPerson(\"a\")\nPerson($alias=\"ignored\", \"Ignored\")\n")
	if len(m.Elements) != 1 || m.Elements[0].Label.Value != "" {
		t.Fatalf("elements %+v", m.Elements)
	}
}

func TestNamedArgumentsOverrideFieldsAndKeepSpans(t *testing.T) {
	src := "C4Context\nContainer(a, \"API\", $descr=\"Description\", $techn=\"Rust\", $arbitrary=\"value\")\n"
	m := resolve(t, src)
	element := m.Elements[0]
	var pairs [][2]string
	for _, field := range element.Fields {
		pairs = append(pairs, [2]string{field.Name, field.Value.Value})
	}
	want := [][2]string{{"techn", "Rust"}, {"descr", "Description"}, {"arbitrary", "value"}}
	if len(pairs) != len(want) {
		t.Fatalf("fields %v", pairs)
	}
	for i := range want {
		if pairs[i] != want[i] {
			t.Fatalf("fields %v", pairs)
		}
	}
	attribute := element.Attributes[2].Span
	if src[attribute.Start:attribute.End] != `$descr="Description"` {
		t.Fatalf("attribute span %q", src[attribute.Start:attribute.End])
	}
	if src[element.AliasSpan.Start:element.AliasSpan.End] != "a" {
		t.Fatalf("alias span %q", src[element.AliasSpan.Start:element.AliasSpan.End])
	}
	if src[element.MacroSpan.Start:element.MacroSpan.End] != "Container" {
		t.Fatalf("macro span %q", src[element.MacroSpan.Start:element.MacroSpan.End])
	}
}

func TestBoundariesRestoreScopeAndInsertHelperType(t *testing.T) {
	m := resolve(t, "C4Context\nEnterprise_Boundary(e, \"Enterprise\") {\nSystem_Boundary(s, \"System\") {\nContainer_Boundary(c, \"Container\") {\nPerson(a, \"A\")\n}\nPerson(b, \"B\")\n}\nPerson(d, \"D\")\n}\nPerson(z, \"Z\")\n")
	wantParents := [][2]string{{"e", ""}, {"s", "e"}, {"c", "s"}}
	if len(m.Boundaries) != len(wantParents) {
		t.Fatalf("boundaries %d", len(m.Boundaries))
	}
	for i, boundary := range m.Boundaries {
		if boundary.ID != wantParents[i][0] || boundary.Parent != wantParents[i][1] {
			t.Fatalf("boundary %+v", boundary)
		}
	}
	for i, want := range []string{"c", "s", "e", ""} {
		if m.Elements[i].Parent != want {
			t.Fatalf("element %s parent %q", m.Elements[i].ID, m.Elements[i].Parent)
		}
	}
	for i, want := range []string{"ENTERPRISE", "SYSTEM", "CONTAINER"} {
		if got := field(t, m.Boundaries[i].Fields, "type").Value; got != want {
			t.Fatalf("boundary %d type %q", i, got)
		}
	}
}

func TestRepeatedBoundaryResetsTypeAndKeepsPosition(t *testing.T) {
	m := resolve(t, "C4Context\nBoundary(a, \"First\", \"Custom\") {\nPerson(p, \"P\")\n}\nBoundary(a, \"Last\") {\nPerson(q, \"Q\")\n}\n")
	if len(m.Boundaries) != 1 {
		t.Fatalf("boundaries %d", len(m.Boundaries))
	}
	boundary := m.Boundaries[0]
	if boundary.Label.Value != "Last" {
		t.Fatalf("label %q", boundary.Label.Value)
	}
	if got := field(t, boundary.Fields, "type").Value; got != "system" {
		t.Fatalf("type %q", got)
	}
}

func TestDeploymentNodesKeepOrientationAndIgnoreSprite(t *testing.T) {
	m := resolve(t, "C4Deployment\nDeployment_Node(a, \"A\", \"Host\", \"Description\", \"ignored sprite\") {\nNode_L(b, \"B\") {\nNode_R(c, \"C\") {\nNode(d, \"D\") {\nPerson(p, \"P\")\n}\n}\n}\n}\n")
	want := []string{"node", "nodeL", "nodeR", "node"}
	for i, node := range want {
		if m.Boundaries[i].NodeType != node {
			t.Fatalf("boundary %d node type %q", i, m.Boundaries[i].NodeType)
		}
	}
	for _, boundary := range m.Boundaries {
		if hasField(boundary.Fields, "sprite") {
			t.Fatalf("deployment sprite assigned: %+v", boundary.Fields)
		}
	}
	if got := field(t, m.Boundaries[0].Fields, "descr").Value; got != "Description" {
		t.Fatalf("descr %q", got)
	}
}

func assertBackRelationPair(t *testing.T, relation model.Relation) {
	t.Helper()
	if relation.From.Value != "a" || relation.To.Value != "b" || relation.MacroName != "Rel_Back" || relation.Label.Value != "Back" {
		t.Fatalf("relation %+v", relation)
	}
	if got := field(t, relation.Fields, "techn").Value; got != "HTTP" {
		t.Fatalf("techn %q", got)
	}
}

func TestRelationMacrosKeepOrderedPairsAndRelIndex(t *testing.T) {
	m := resolve(t, "C4Dynamic\nRel(a, b, \"First\", \"HTTP\")\nBiRel(b, a, \"Both\")\nRel_Back(a, b, \"Back\")\nRelIndex(7, c, d, \"Indexed\")\nRel(a, \"b\")\n")
	if len(m.Elements) != 0 {
		t.Fatalf("elements %d", len(m.Elements))
	}
	if len(m.Relations) != 3 {
		t.Fatalf("relations %d", len(m.Relations))
	}
	assertBackRelationPair(t, m.Relations[0])
	if m.Relations[1].MacroName != "BiRel" || m.Relations[1].From.Value != "b" {
		t.Fatalf("birel %+v", m.Relations[1])
	}
	if m.Relations[2].MacroName != "Rel" || m.Relations[2].From.Value != "c" {
		t.Fatalf("rel index %+v", m.Relations[2])
	}
}

func TestDirectionalMacrosAreRetainedWithoutGeometryChanges(t *testing.T) {
	for _, name := range []string{"Rel_Up", "Rel_U", "Rel_Down", "Rel_D", "Rel_Left", "Rel_L", "Rel_Right", "Rel_R"} {
		m := resolve(t, "C4Context\n"+name+"(a, b, \"Label\")\n")
		if len(m.Relations) != 1 || m.Relations[0].MacroName != name {
			t.Fatalf("%s: relations %+v", name, m.Relations)
		}
		if m.Direction != "TB" {
			t.Fatalf("%s: direction %q", name, m.Direction)
		}
	}
}

func TestStylesTargetExistingElementsBeforeBoundaries(t *testing.T) {
	m := resolve(t, "C4Context\nUpdateElementStyle(a, \"ignored\")\nPerson(a, \"A\")\nBoundary(a, \"Boundary\") {\nPerson(b, \"B\")\n}\nUpdateElementStyle(a, \"red\", $techn=\"Metadata\")\nUpdateElementStyle(missing, \"ignored\")\n")
	element := m.Elements[0]
	var pairs [][2]string
	for _, field := range element.Styles {
		pairs = append(pairs, [2]string{field.Name, field.Value.Value})
	}
	if len(pairs) != 2 || pairs[0] != [2]string{"bgColor", "red"} || pairs[1] != [2]string{"techn", "Metadata"} {
		t.Fatalf("styles %v", pairs)
	}
	if len(m.Boundaries[0].Styles) != 0 {
		t.Fatalf("boundary styles %v", m.Boundaries[0].Styles)
	}
}

func TestElementStyleBindsAllNinePositionalSlots(t *testing.T) {
	m := resolve(t, "C4Context\nPerson(a, \"A\")\nUpdateElementStyle(a, \"bg\", \"font\", \"border\", \"shadow\", \"rect\", \"sprite\", \"techn\", \"legend\", \"legendSprite\", \"extra\", $shape=\"late\")\n")
	want := [][2]string{
		{"bgColor", "bg"},
		{"fontColor", "font"},
		{"borderColor", "border"},
		{"shadowing", "shadow"},
		{"shape", "rect"},
		{"sprite", "sprite"},
		{"techn", "techn"},
		{"legendText", "legend"},
		{"legendSprite", "legendSprite"},
	}
	styles := m.Elements[0].Styles
	if len(styles) != len(want) {
		t.Fatalf("styles %v", styles)
	}
	for i := range want {
		if got := [2]string{styles[i].Name, styles[i].Value.Value}; got != want[i] {
			t.Fatalf("style %d: %v", i, got)
		}
	}
	named := resolve(t, "C4Context\nPerson(a, \"A\")\nUpdateElementStyle(a, \"bg\", \"font\", \"border\", \"shadow\", \"rect\", $shape=\"named\", \"sprite\", \"techn\", \"legend\")\n")
	overrides := named.Elements[0].Styles
	wantOverrides := [][2]string{
		{"bgColor", "bg"},
		{"fontColor", "font"},
		{"borderColor", "border"},
		{"shadowing", "shadow"},
		{"shape", "named"},
		{"techn", "sprite"},
		{"legendText", "techn"},
		{"legendSprite", "legend"},
	}
	if len(overrides) != len(wantOverrides) {
		t.Fatalf("overrides %v", overrides)
	}
	for i := range wantOverrides {
		if got := [2]string{overrides[i].Name, overrides[i].Value.Value}; got != wantOverrides[i] {
			t.Fatalf("override %d: %v", i, got)
		}
	}
}

func TestRelationOffsetsKeepLeadingIntegers(t *testing.T) {
	m := resolve(t, "C4Context\nRel(a, b, \"Call\")\nUpdateRelStyle(a, b, \"red\", \"blue\", \"-12px\", \"unknown\")\nUpdateRelStyle(b, a, \"ignored\")\n")
	var pairs [][2]string
	for _, field := range m.Relations[0].Styles {
		pairs = append(pairs, [2]string{field.Name, field.Value.Value})
	}
	want := [][2]string{{"textColor", "red"}, {"lineColor", "blue"}, {"offsetX", "-12"}, {"offsetY", "unknown"}}
	if len(pairs) != len(want) {
		t.Fatalf("styles %v", pairs)
	}
	for i := range want {
		if pairs[i] != want[i] {
			t.Fatalf("styles %v", pairs)
		}
	}
}

func TestLayoutHintsAcceptOnlyPositiveLeadingIntegers(t *testing.T) {
	m := resolve(t, "C4Context\nUpdateLayoutConfig(\"3shapes\", \"2boundaries\")\nUpdateLayoutConfig(\"0\", \"invalid\")\nUpdateLayoutConfig($c4BoundaryInRow=\"5px\", $unused=\"9\")\n")
	var pairs [][2]string
	for _, field := range m.LayoutConfig {
		pairs = append(pairs, [2]string{field.Name, field.Value.Value})
	}
	want := [][2]string{{"c4ShapeInRow", "3"}, {"c4BoundaryInRow", "5"}}
	if len(pairs) != len(want) {
		t.Fatalf("layout config %v", pairs)
	}
	for i := range want {
		if pairs[i] != want[i] {
			t.Fatalf("layout config %v", pairs)
		}
	}
}

func TestAccessibilityFormsShareLastTitleAndDescription(t *testing.T) {
	m := resolve(t, "C4Context\ntitle First\naccTitle: Last\naccDescription Old\naccDescr: Middle\naccDescr {\n Final description \n}\nPerson(a, \"A\")\n")
	if m.AccTitle != "Last" || m.AccDescr != "Final description" {
		t.Fatalf("title %q description %q", m.AccTitle, m.AccDescr)
	}
	if len(m.Accessibility) != 5 {
		t.Fatalf("accessibility %v", m.Accessibility)
	}
}

func TestEmptyOptionalArgumentsResetAndExtraArgumentsIgnored(t *testing.T) {
	m := resolve(t, "C4Context\nSystem(a, \"First\", \"Before\")\nSystem(a, \"Last\", \"\", \"sprite\", \"tags\", \"link\", $descr=\"ignored\")\n")
	element := m.Elements[0]
	if got := field(t, element.Fields, "descr").Value; got != "" {
		t.Fatalf("descr %q", got)
	}
	if element.Label.Value != "Last" {
		t.Fatalf("label %q", element.Label.Value)
	}
	if len(element.Attributes) != 7 {
		t.Fatalf("attributes %d", len(element.Attributes))
	}
}

func TestNamedLabelOverrideDoesNotOutliveRequiredLabel(t *testing.T) {
	m := resolve(t, "C4Context\nPerson(p, \"First\", $label=\"Override\")\nPerson(p, \"Last\")\n")
	if m.Elements[0].Label.Value != "Last" {
		t.Fatalf("label %q", m.Elements[0].Label.Value)
	}
}

func TestBoundaryStyleAndDeploymentSpriteStayMetadata(t *testing.T) {
	m := resolve(t, "C4Context\nSystem_Boundary(g, \"Group\", $type=\"Custom\") {\nPerson(p, \"P\")\n}\nUpdateElementStyle(g, $shape=\"cloud\")\n")
	boundary := m.Boundaries[0]
	if got := field(t, boundary.Fields, "type").Value; got != "Custom" {
		t.Fatalf("type %q", got)
	}
	if len(boundary.Styles) != 1 || boundary.Styles[0].Name != "shape" || boundary.Styles[0].Value.Value != "cloud" {
		t.Fatalf("styles %+v", boundary.Styles)
	}
}

func TestEmptyCollectionsAreNil(t *testing.T) {
	m := resolve(t, "C4Context\nPerson(a, \"A\")\n")
	if m.Boundaries != nil || m.Relations != nil || m.LayoutConfig != nil || m.Accessibility != nil {
		t.Fatalf("empty collections are not nil: %+v", m)
	}
}

func assertRuneBoundarySpan(t *testing.T, src string, span source.Span, label string) {
	t.Helper()
	if !utf8.RuneStart(src[span.Start]) || !utf8.RuneStart(src[span.End]) {
		t.Fatalf("%s %v not on a UTF-8 boundary", label, span)
	}
}

func assertMetadataRawSpans(t *testing.T, src string, items []parser.Statement) {
	t.Helper()
	for i, want := range []string{" Demo ", " Details "} {
		value := items[i].Other.Value
		if string(value.Raw) != want {
			t.Fatalf("value %q", string(value.Raw))
		}
		assertRuneBoundarySpan(t, src, value.Span, "value span")
	}
}

func assertAccessibilityEntrySpans(t *testing.T, src string, m *model.Model, items []parser.Statement) {
	t.Helper()
	if len(m.Accessibility) != 2 {
		t.Fatalf("accessibility %v", m.Accessibility)
	}
	for i, entry := range m.Accessibility {
		if entry.Span.Start != items[i].Span.Start || entry.Span.End != items[i].Span.End {
			t.Fatalf("accessibility span %v", entry.Span)
		}
		assertRuneBoundarySpan(t, src, entry.Span, "accessibility span")
	}
}

func TestUnicodeSeparatorMetadataResolvesTrimmedText(t *testing.T) {
	src := "C4Context\ntitle\u00a0 Demo \naccDescription\u2003 Details \nPerson(a, \"A\")\n"
	start, ds := parser.Parse([]byte(src), nil)
	if len(ds) != 0 {
		t.Fatalf("parse diagnostics %v", ds)
	}
	assertMetadataRawSpans(t, src, start.MermaidDoc.GraphConfig.Statements.Items)
	m, more := model.Resolve([]byte(src), start)
	if len(more) != 0 {
		t.Fatalf("resolve diagnostics %v", more)
	}
	if m.AccTitle != "Demo" || m.AccDescr != "Details" {
		t.Fatalf("title %q description %q", m.AccTitle, m.AccDescr)
	}
	assertAccessibilityEntrySpans(t, src, m, start.MermaidDoc.GraphConfig.Statements.Items)
}
