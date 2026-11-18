package c4

import (
	"strconv"
	"strings"
	"unicode"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/c4"
)

type Text struct {
	Value string
	Span  source.Span
}

type Field struct {
	Name  string
	Value Text
	Span  source.Span
}

type Element struct {
	ID         string
	AliasSpan  source.Span
	MacroName  string
	MacroSpan  source.Span
	Kind       string
	Parent     string
	Label      Text
	Fields     []Field
	Styles     []Field
	Attributes []Field
	Span       source.Span
	Wrap       bool
}

type Boundary struct {
	ID         string
	AliasSpan  source.Span
	MacroName  string
	MacroSpan  source.Span
	NodeType   string
	Parent     string
	Label      Text
	Fields     []Field
	Styles     []Field
	Attributes []Field
	Span       source.Span
	Wrap       bool
}

type Relation struct {
	From       Text
	To         Text
	Label      Text
	MacroName  string
	MacroSpan  source.Span
	Fields     []Field
	Styles     []Field
	Attributes []Field
	Span       source.Span
	Wrap       bool
}

type DeclarationTarget uint8

const (
	DeclarationElement DeclarationTarget = iota
	DeclarationBoundary
)

type Declaration struct {
	Target DeclarationTarget
	Index  int
}

type AliasOccurrence struct {
	Declaration Declaration
	Span        source.Span
}

type UsageKind uint8

const (
	UsageRelation UsageKind = iota
	UsageElementStyle
	UsageRelationStyle
)

type Usage struct {
	Kind     UsageKind
	Relation int
	From     Text
	To       Text
}

type Model struct {
	C4Type        string
	Direction     string
	Elements      []Element
	Boundaries    []Boundary
	Relations     []Relation
	Declarations  []Declaration
	Aliases       []AliasOccurrence
	Usages        []Usage
	AccTitle      string
	AccDescr      string
	Accessibility []Text
	LayoutConfig  []Field
}

func Resolve(_ []byte, file *syn.Start) (*Model, []diag.Diagnostic) {
	model := &Model{Direction: "TB"}
	switch {
	case file.Direction != nil:
		model.Direction = directionValue(file.Direction.Direction)
	case file.MermaidDoc != nil:
		config := &file.MermaidDoc.GraphConfig
		model.C4Type = string(config.Header.Raw)
		model.statements(config.Statements.Items, "")
	}
	return model, nil
}

func directionValue(token syn.Token) string {
	value := strings.TrimSpace(string(token.Raw))
	for strings.HasPrefix(value, "direction") {
		value = value[len("direction"):]
	}
	return strings.TrimSpace(value)
}

func (m *Model) statements(statements []syn.Statement, parent string) {
	for i := range statements {
		statement := &statements[i]
		switch {
		case statement.Other != nil:
			m.accessibility(statement.Other)
		case statement.Diagram != nil:
			m.diagram(statement.Diagram, parent)
		}
	}
}

func (m *Model) accessibility(statement *syn.OtherStatement) {
	value := text(statement.Value)
	if statement.Form == "title" || statement.Form == "acc_title" {
		m.AccTitle = value.Value
	} else {
		m.AccDescr = value.Value
	}
	m.Accessibility = append(m.Accessibility, Text{Value: value.Value, Span: statement.Span})
}

func (m *Model) diagram(statement *syn.DiagramStatement, parent string) {
	if statement.Boundary != nil {
		id, ok := m.boundary(statement.Boundary, parent)
		if ok {
			m.statements(statement.Boundary.Body.Items, id)
		}
		return
	}
	if statement.Call != nil {
		m.call(*statement.Call, parent)
	}
}

type callRef struct {
	name      string
	attrs     *syn.Attributes
	macroSpan source.Span
	span      source.Span
}

func (m *Model) call(statement syn.CallStatement, parent string) {
	call := callRef{name: string(statement.Macro.Raw), attrs: &statement.Attributes, macroSpan: statement.Macro.Span, span: statement.Span}
	switch {
	case call.name == "UpdateElementStyle":
		m.elementStyle(call.attrs)
	case call.name == "UpdateRelStyle":
		m.relationStyle(call.attrs)
	case call.name == "UpdateLayoutConfig":
		m.layoutHint(call.attrs)
	case isRelation(call.name):
		m.relation(call)
	default:
		m.element(call, parent)
	}
}

func isRelation(name string) bool {
	return strings.HasPrefix(name, "Rel") || name == "BiRel"
}

func (m *Model) element(call callRef, parent string) {
	alias, ok := positional(call.attrs, 0)
	if !ok {
		return
	}
	index := elementIndex(m.Elements, alias.Value)
	element := newElement(call, parent, alias)
	target := index
	if target < 0 {
		target = len(m.Elements)
	}
	m.Aliases = append(m.Aliases, AliasOccurrence{Declaration{DeclarationElement, target}, alias.Span})
	if index >= 0 {
		element.Fields = m.Elements[index].Fields
		element.Styles = m.Elements[index].Styles
	}
	element.Fields = withoutName(element.Fields, "label")
	signature := elementSignature(call.name)
	defaultTextFields(&element.Fields, signature)
	applyOptional(call.attrs, 2, signature, &element.Fields)
	syncLabel(&element.Label, element.Fields)
	if index >= 0 {
		m.Elements[index] = element
		return
	}
	m.Declarations = append(m.Declarations, Declaration{Target: DeclarationElement, Index: len(m.Elements)})
	m.Elements = append(m.Elements, element)
}

func elementIndex(elements []Element, id string) int {
	for i := range elements {
		if elements[i].ID == id {
			return i
		}
	}
	return -1
}

func elementSignature(name string) []string {
	if strings.HasPrefix(name, "Container") || strings.HasPrefix(name, "Component") {
		return []string{"techn", "descr", "sprite", "tags", "link"}
	}
	return []string{"descr", "sprite", "tags", "link"}
}

func (m *Model) boundary(statement *syn.BoundaryStatement, parent string) (string, bool) {
	start := &statement.Start.Start
	call := callRef{name: string(start.Macro.Raw), attrs: &start.Attributes, macroSpan: start.Macro.Span, span: statement.Span}
	alias, ok := positional(call.attrs, 0)
	if !ok {
		return "", false
	}
	index := boundaryIndex(m.Boundaries, alias.Value)
	boundary := newBoundary(call, parent, alias)
	target := index
	if target < 0 {
		target = len(m.Boundaries)
	}
	m.Aliases = append(m.Aliases, AliasOccurrence{Declaration{DeclarationBoundary, target}, alias.Span})
	if index >= 0 {
		boundary.Fields = m.Boundaries[index].Fields
		boundary.Styles = m.Boundaries[index].Styles
	}
	boundary.Fields = withoutName(boundary.Fields, "label")
	boundaryFields(call, &boundary.Fields)
	syncLabel(&boundary.Label, boundary.Fields)
	if index >= 0 {
		m.Boundaries[index] = boundary
		return boundary.ID, true
	}
	m.Declarations = append(m.Declarations, Declaration{Target: DeclarationBoundary, Index: len(m.Boundaries)})
	m.Boundaries = append(m.Boundaries, boundary)
	return boundary.ID, true
}

func boundaryIndex(boundaries []Boundary, id string) int {
	for i := range boundaries {
		if boundaries[i].ID == id {
			return i
		}
	}
	return -1
}

func (m *Model) relation(call callRef) {
	offset := 0
	if call.name == "RelIndex" {
		offset = 1
	}
	from, ok := positional(call.attrs, offset)
	if !ok {
		return
	}
	to, ok := positional(call.attrs, offset+1)
	if !ok {
		return
	}
	label, ok := positional(call.attrs, offset+2)
	if !ok {
		return
	}
	index := relationIndex(m.Relations, from.Value, to.Value)
	target := index
	if target < 0 {
		target = len(m.Relations)
	}
	m.Usages = append(m.Usages, Usage{Kind: UsageRelation, Relation: target, From: Text{Span: from.Span}, To: Text{Span: to.Span}})
	relation := newRelation(call, from, to, label)
	if index >= 0 {
		relation.Fields = m.Relations[index].Fields
		relation.Styles = m.Relations[index].Styles
	}
	relation.Fields = withoutName(relation.Fields, "label")
	signature := []string{"techn", "descr", "sprite", "tags", "link"}
	defaultTextFields(&relation.Fields, signature)
	applyOptional(call.attrs, offset+3, signature, &relation.Fields)
	syncLabel(&relation.Label, relation.Fields)
	if index >= 0 {
		m.Relations[index] = relation
		return
	}
	m.Relations = append(m.Relations, relation)
}

func relationIndex(relations []Relation, from, to string) int {
	for i := range relations {
		if relations[i].From.Value == from && relations[i].To.Value == to {
			return i
		}
	}
	return -1
}

func (m *Model) elementStyle(attrs *syn.Attributes) {
	alias, ok := positional(attrs, 0)
	if !ok {
		return
	}
	m.Usages = append(m.Usages, Usage{Kind: UsageElementStyle, From: alias})
	if index := elementIndex(m.Elements, alias.Value); index >= 0 {
		applyElementStyle(attrs, &m.Elements[index].Styles)
		return
	}
	if index := boundaryIndex(m.Boundaries, alias.Value); index >= 0 {
		applyElementStyle(attrs, &m.Boundaries[index].Styles)
	}
}

const styleNameCount = 9

func applyElementStyle(attrs *syn.Attributes, fields *[]Field) {
	count := min(len(attrs.Items)-1, styleNameCount)
	for i := range count {
		setField(fields, attributeField(&attrs.Items[i+1], styleNameAt(i)))
	}
}

func styleNameAt(index int) string {
	switch index {
	case 0:
		return "bgColor"
	case 1:
		return "fontColor"
	case 2:
		return "borderColor"
	case 3:
		return "shadowing"
	case 4:
		return "shape"
	case 5:
		return "sprite"
	case 6:
		return "techn"
	case 7:
		return "legendText"
	}
	return "legendSprite"
}

func (m *Model) relationStyle(attrs *syn.Attributes) {
	from, ok := positional(attrs, 0)
	if !ok {
		return
	}
	to, ok := positional(attrs, 1)
	if !ok {
		return
	}
	m.Usages = append(m.Usages, Usage{Kind: UsageRelationStyle, From: from, To: to})
	index := relationIndex(m.Relations, from.Value, to.Value)
	if index < 0 {
		return
	}
	styles := &m.Relations[index].Styles
	applyOptional(attrs, 2, []string{"textColor", "lineColor", "offsetX", "offsetY"}, styles)
	normalizeOffsets(*styles)
}

func (m *Model) layoutHint(attrs *syn.Attributes) {
	var fields []Field
	applyOptional(attrs, 0, []string{"c4ShapeInRow", "c4BoundaryInRow"}, &fields)
	for _, field := range fields {
		if field.Name != "c4ShapeInRow" && field.Name != "c4BoundaryInRow" {
			continue
		}
		value, ok := leadingInteger(field.Value.Value)
		if !ok || value < 1 {
			continue
		}
		field.Value.Value = strconv.FormatInt(value, 10)
		setField(&m.LayoutConfig, field)
	}
}

func newElement(call callRef, parent string, alias Text) Element {
	label, _ := positional(call.attrs, 1)
	return Element{
		ID:         alias.Value,
		AliasSpan:  alias.Span,
		MacroName:  call.name,
		MacroSpan:  call.macroSpan,
		Kind:       elementKind(call.name),
		Parent:     parent,
		Label:      label,
		Attributes: attributeFields(call.attrs),
		Span:       call.span,
	}
}

func newBoundary(call callRef, parent string, alias Text) Boundary {
	label, _ := positional(call.attrs, 1)
	return Boundary{
		ID:         alias.Value,
		AliasSpan:  alias.Span,
		MacroName:  call.name,
		MacroSpan:  call.macroSpan,
		NodeType:   nodeType(call.name),
		Parent:     parent,
		Label:      label,
		Attributes: attributeFields(call.attrs),
		Span:       call.span,
	}
}

func newRelation(call callRef, from, to, label Text) Relation {
	macroName := call.name
	if macroName == "RelIndex" {
		macroName = "Rel"
	}
	return Relation{
		From:       from,
		To:         to,
		Label:      label,
		MacroName:  macroName,
		MacroSpan:  call.macroSpan,
		Attributes: attributeFields(call.attrs),
		Span:       call.span,
	}
}

func boundaryFields(call callRef, fields *[]Field) {
	setField(fields, Field{Name: "type", Value: Text{Value: boundaryType(call.name), Span: call.attrs.Span}, Span: call.attrs.Span})
	switch call.name {
	case "Enterprise_Boundary", "System_Boundary", "Container_Boundary":
		applyOptional(call.attrs, 2, []string{"tags", "link"}, fields)
	case "Boundary":
		applyOptional(call.attrs, 2, []string{"type", "tags", "link"}, fields)
	default:
		defaultTextFields(fields, []string{"descr"})
		applyOptional(call.attrs, 2, []string{"type", "descr"}, fields)
		applyOptional(call.attrs, 5, []string{"tags", "link"}, fields)
	}
}

func boundaryType(name string) string {
	switch name {
	case "Enterprise_Boundary":
		return "ENTERPRISE"
	case "System_Boundary":
		return "SYSTEM"
	case "Container_Boundary":
		return "CONTAINER"
	case "Boundary":
		return "system"
	}
	return "node"
}

func nodeType(name string) string {
	switch name {
	case "Node_L":
		return "nodeL"
	case "Node_R":
		return "nodeR"
	case "Node", "Deployment_Node":
		return "node"
	}
	return ""
}

func elementKind(name string) string {
	base, prefix := name, ""
	if family, found := strings.CutSuffix(name, "_Ext"); found {
		base, prefix = family, "external_"
	}
	family, suffix := base, ""
	if trimmed, found := strings.CutSuffix(base, "Db"); found {
		family, suffix = trimmed, "_db"
	} else if trimmed, found := strings.CutSuffix(base, "Queue"); found {
		family, suffix = trimmed, "_queue"
	}
	return prefix + strings.ToLower(family) + suffix
}

func text(token syn.Token) Text {
	return Text{Value: strings.TrimSpace(string(token.Raw)), Span: token.Span}
}

func positional(attrs *syn.Attributes, index int) (Text, bool) {
	if index >= len(attrs.Items) {
		return Text{}, false
	}
	attribute := &attrs.Items[index]
	switch {
	case attribute.Positional != nil:
		return text(*attribute.Positional), true
	case attribute.Empty != nil:
		return Text{Span: attribute.Span}, true
	}
	return Text{}, false
}

func attributeFields(attrs *syn.Attributes) []Field {
	fields := make([]Field, 0, len(attrs.Items))
	for i := range attrs.Items {
		fields = append(fields, attributeField(&attrs.Items[i], strconv.Itoa(i)))
	}
	return fields
}

func attributeField(attribute *syn.Attribute, name string) Field {
	switch {
	case attribute.Key != nil:
		return Field{Name: keyName(attribute.Key.Raw), Value: text(*attribute.Value), Span: attribute.Span}
	case attribute.Positional != nil:
		return Field{Name: name, Value: text(*attribute.Positional), Span: attribute.Span}
	}
	return Field{Name: name, Value: Text{Span: attribute.Span}, Span: attribute.Span}
}

func keyName(raw []byte) string {
	return strings.TrimSpace(string(raw))
}

func applyOptional(attrs *syn.Attributes, start int, names []string, fields *[]Field) {
	for i := 0; i < len(names) && start+i < len(attrs.Items); i++ {
		setField(fields, attributeField(&attrs.Items[start+i], names[i]))
	}
}

func setField(fields *[]Field, field Field) {
	for i := range *fields {
		if (*fields)[i].Name == field.Name {
			(*fields)[i] = field
			return
		}
	}
	*fields = append(*fields, field)
}

func defaultTextFields(fields *[]Field, names []string) {
	for _, name := range names {
		if name != "techn" && name != "descr" {
			continue
		}
		if hasField(*fields, name) {
			continue
		}
		*fields = append(*fields, Field{Name: name})
	}
}

func hasField(fields []Field, name string) bool {
	for i := range fields {
		if fields[i].Name == name {
			return true
		}
	}
	return false
}

func withoutName(fields []Field, name string) []Field {
	out := make([]Field, 0, len(fields))
	for _, field := range fields {
		if field.Name != name {
			out = append(out, field)
		}
	}
	return out
}

func syncLabel(label *Text, fields []Field) {
	for i := range fields {
		if fields[i].Name == "label" {
			*label = fields[i].Value
			return
		}
	}
}

func leadingInteger(value string) (int64, bool) {
	value = strings.TrimLeftFunc(value, unicode.IsSpace)
	digits := value
	if strings.HasPrefix(value, "+") || strings.HasPrefix(value, "-") {
		digits = value[1:]
	}
	length := 0
	for length < len(digits) && digits[length] >= '0' && digits[length] <= '9' {
		length++
	}
	if length == 0 {
		return 0, false
	}
	parsed, err := strconv.ParseInt(value[:len(value)-len(digits)+length], 10, 64)
	if err != nil {
		return 0, false
	}
	return parsed, true
}

func normalizeOffsets(fields []Field) {
	for i := range fields {
		field := &fields[i]
		if field.Name != "offsetX" && field.Name != "offsetY" {
			continue
		}
		if value, ok := leadingInteger(field.Value.Value); ok {
			field.Value.Value = strconv.FormatInt(value, 10)
		}
	}
}
