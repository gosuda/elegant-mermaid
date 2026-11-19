package requirement

import (
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/requirement"
)

type Value struct {
	Value string
	Span  source.Span
}

type Field struct {
	Name        string
	Value       Value
	Span        source.Span
	KeywordSpan source.Span
	ColonSpan   source.Span
}

type Requirement struct {
	Name, Kind, Id, Text, Risk, VerifyMethod string
	Span, NameSpan, TypeSpan                 source.Span
	Delimiters                               [2]source.Span
	Fields                                   []Field
	Classes, Styles                          []Value
}

type Element struct {
	Name, Kind, Docref string
	Span, NameSpan     source.Span
	Delimiters         [2]source.Span
	Fields             []Field
	Classes, Styles    []Value
}

type NodeRef struct {
	Index   int
	Element bool
}

type Relation struct {
	From, To            Value
	FromNode, ToNode    *NodeRef
	Kind, Label         string
	Span                source.Span
	TypeSpan, ArrowSpan source.Span
	LineSpan            source.Span
}

type ClassDefinition struct {
	Name               Value
	Styles, TextStyles []Value
}

type Declaration struct {
	Node NodeRef
	Span source.Span
}

type IDDeclaration struct {
	Requirement, Field int
	Discarded          Value
}

type Model struct {
	Requirements     []Requirement
	Elements         []Element
	Relationships    []Relation
	Declarations     []Declaration
	IDDeclarations   []IDDeclaration
	ClassDefinitions []ClassDefinition
	Direction        string
	AccTitle         string
	AccDescr         string
}

func Resolve(_ []byte, document *syn.Start) (*Model, []diag.Diagnostic) {
	m := &Model{Direction: "TB"}
	for i := range document.Directives {
		m.directive(&document.Directives[i])
	}
	for i := range document.Diagram.Statements {
		m.statement(&document.Diagram.Statements[i].Kind)
	}
	for i := range m.Relationships {
		r := &m.Relationships[i]
		r.FromNode = lookup(m.Requirements, m.Elements, r.From.Value)
		r.ToNode = lookup(m.Requirements, m.Elements, r.To.Value)
	}
	return m, nil
}

func lookup(requirements []Requirement, elements []Element, name string) *NodeRef {
	for i := range requirements {
		if requirements[i].Name == name {
			return &NodeRef{Index: i}
		}
	}
	for i := range elements {
		if elements[i].Name == name {
			return &NodeRef{Index: i, Element: true}
		}
	}
	return nil
}

func fieldValue(fields []Field, name string) string {
	for i := range fields {
		if fields[i].Name == name {
			return fields[i].Value.Value
		}
	}
	return ""
}

func (m *Model) statement(s *syn.StatementKind) {
	switch s.Kind {
	case "Requirement":
		m.requirement(s.Requirement)
	case "Element":
		m.element(s.Element)
	case "Relationship":
		m.relationship(s.Relationship)
	case "Directive":
		m.directive(s.Directive)
	case "Direction":
		m.Direction = s.Direction.Value
	case "ClassDef":
		m.defineClass(s.ClassDef)
	case "Class":
		m.assignClasses(s.Class)
	case "Style":
		m.style(s.Style)
	}
}

func (m *Model) requirement(d *syn.RequirementDef) {
	index := m.RequirementIndex(d.Name.Value)
	if index < 0 {
		index = len(m.Requirements)
	}
	m.Declarations = append(m.Declarations, Declaration{Node: NodeRef{Index: index}, Span: d.Name.Span})
	for i, field := range d.Body.Fields {
		if field.Value.Kind != "Id" {
			continue
		}
		if index == len(m.Requirements) && syntax.DecodeEntities(field.Value.Id.Value) == field.Value.Id.Value {
			m.IDDeclarations = append(m.IDDeclarations, IDDeclaration{Requirement: index, Field: i})
		} else {
			m.IDDeclarations = append(m.IDDeclarations, IDDeclaration{Requirement: -1, Discarded: Value{Value: field.Value.Id.Value, Span: field.Value.Id.Span}})
		}
	}
	if m.RequirementIndex(d.Name.Value) < 0 {
		fields := requirementFields(&d.Body)
		m.Requirements = append(m.Requirements, Requirement{
			Name:         d.Name.Value,
			Kind:         d.RequirementType.Value,
			Id:           fieldValue(fields, "id"),
			Text:         fieldValue(fields, "text"),
			Risk:         fieldValue(fields, "risk"),
			VerifyMethod: fieldValue(fields, "verifyMethod"),
			Span:         d.Span,
			NameSpan:     d.Name.Span,
			TypeSpan:     d.RequirementType.Span,
			Delimiters:   d.Delimiters,
			Fields:       fields,
			Classes:      []Value{{Value: "default", Span: d.Name.Span}},
		})
	}
	m.inlineClasses(d.Name.Value, d.Classes)
}

func (m *Model) RequirementIndex(name string) int {
	for i := range m.Requirements {
		if m.Requirements[i].Name == name {
			return i
		}
	}
	return -1
}

func (m *Model) element(d *syn.ElementDef) {
	index := m.ElementIndex(d.Name.Value)
	if index < 0 {
		index = len(m.Elements)
	}
	m.Declarations = append(m.Declarations, Declaration{Node: NodeRef{Index: index, Element: true}, Span: d.Name.Span})
	if m.ElementIndex(d.Name.Value) < 0 {
		fields := elementFields(&d.Body)
		m.Elements = append(m.Elements, Element{
			Name:       d.Name.Value,
			Kind:       fieldValue(fields, "type"),
			Docref:     fieldValue(fields, "docref"),
			Span:       d.Span,
			NameSpan:   d.Name.Span,
			Delimiters: d.Delimiters,
			Fields:     fields,
			Classes:    []Value{{Value: "default", Span: d.Name.Span}},
		})
	}
	m.inlineClasses(d.Name.Value, d.Classes)
}

func (m *Model) ElementIndex(name string) int {
	for i := range m.Elements {
		if m.Elements[i].Name == name {
			return i
		}
	}
	return -1
}

func (m *Model) relationship(r *syn.RelationshipDef) {
	from, to := r.Left, r.Right
	if r.Reversed {
		from, to = r.Right, r.Left
	}
	m.Relationships = append(m.Relationships, Relation{
		From:      Value{Value: from.Value, Span: from.Span},
		To:        Value{Value: to.Value, Span: to.Span},
		Kind:      r.Relationship.Value,
		Label:     "<<" + r.Relationship.Value + ">>",
		Span:      r.Span,
		TypeSpan:  r.Relationship.Span,
		ArrowSpan: r.Arrow.Span,
		LineSpan:  r.Line,
	})
}

func (m *Model) directive(d *syn.Directive) {
	text := strings.TrimSpace(d.Value.Text)
	if d.Title {
		m.AccTitle = text
	} else {
		m.AccDescr = text
	}
}

func (m *Model) nodeMetadata(name string) (classes *[]Value, styles *[]Value) {
	if i := m.RequirementIndex(name); i >= 0 {
		return &m.Requirements[i].Classes, &m.Requirements[i].Styles
	}
	if i := m.ElementIndex(name); i >= 0 {
		return &m.Elements[i].Classes, &m.Elements[i].Styles
	}
	return nil, nil
}

func (m *Model) inlineClasses(name string, classes *syn.IdList) {
	if classes == nil {
		return
	}
	m.applyClasses(name, names(classes))
}

func (m *Model) applyClasses(name string, classes []Value) {
	var styles []Value
	for _, class := range classes {
		for i := range m.ClassDefinitions {
			if m.ClassDefinitions[i].Name.Value == class.Value {
				styles = append(styles, m.ClassDefinitions[i].Styles...)
				break
			}
		}
	}
	if assigned, direct := m.nodeMetadata(name); assigned != nil {
		*assigned = append(*assigned, classes...)
		*direct = append(*direct, styles...)
	}
}

func (m *Model) assignClasses(s *syn.ClassStatement) {
	classes := names(&s.Classes)
	for i := range s.Targets.Names {
		m.applyClasses(s.Targets.Names[i].Value, classes)
	}
}

func (m *Model) style(s *syn.StyleStatement) {
	values := styleValues(&s.Styles)
	for i := range s.Ids.Names {
		_, direct := m.nodeMetadata(s.Ids.Names[i].Value)
		if direct == nil {
			break
		}
		*direct = append(*direct, splitStyles(values)...)
	}
}

func (m *Model) defineClass(s *syn.ClassDefStatement) {
	additions := styleValues(&s.Styles)
	for _, name := range names(&s.Ids) {
		m.extendDefinition(name, additions)
	}
}

func (m *Model) extendDefinition(name Value, additions []Value) {
	var textStyles []Value
	for _, style := range additions {
		if strings.Contains(style.Value, "color") {
			textStyles = append(textStyles, Value{Value: strings.Replace(style.Value, "fill", "bgFill", 1), Span: style.Span})
		}
	}
	for i := range m.ClassDefinitions {
		if m.ClassDefinitions[i].Name.Value == name.Value {
			def := &m.ClassDefinitions[i]
			def.Styles = append(def.Styles, additions...)
			def.TextStyles = append(def.TextStyles, textStyles...)
			m.appendDefinitionStyles(name.Value, additions)
			return
		}
	}
	m.ClassDefinitions = append(m.ClassDefinitions, ClassDefinition{Name: name, Styles: slices.Clone(additions), TextStyles: textStyles})
	m.appendDefinitionStyles(name.Value, additions)
}

func (m *Model) appendDefinitionStyles(name string, additions []Value) {
	for i := range m.Requirements {
		appendClassStyles(&m.Requirements[i].Classes, &m.Requirements[i].Styles, name, additions)
	}
	for i := range m.Elements {
		appendClassStyles(&m.Elements[i].Classes, &m.Elements[i].Styles, name, additions)
	}
}

func names(ids *syn.IdList) []Value {
	out := make([]Value, len(ids.Names))
	for i, id := range ids.Names {
		out[i] = Value{Value: id.Value, Span: id.Span}
	}
	return out
}

func styleValues(styles *syn.StylesOpt) []Value {
	out := make([]Value, len(styles.Styles))
	for i, style := range styles.Styles {
		var text strings.Builder
		for _, component := range style.Components {
			text.WriteString(component.Text)
		}
		out[i] = Value{Value: text.String(), Span: style.Span}
	}
	return out
}

func splitStyles(styles []Value) []Value {
	var out []Value
	for _, style := range styles {
		for part := range strings.SplitSeq(style.Value, ",") {
			out = append(out, Value{Value: part, Span: style.Span})
		}
	}
	return out
}

func appendClassStyles(classes *[]Value, styles *[]Value, name string, additions []Value) {
	for _, class := range *classes {
		if class.Value == name {
			*styles = append(*styles, splitStyles(additions)...)
			return
		}
	}
}

func requirementFields(body *syn.RequirementBody) []Field {
	fields := make([]Field, len(body.Fields))
	for i, field := range body.Fields {
		name, text, span := "", "", field.Value.Id.Span
		switch field.Value.Kind {
		case "Id":
			name, text = "id", field.Value.Id.Value
		case "Text":
			name, text = "text", field.Value.Text.Value
		case "Risk":
			name, text = "risk", field.Value.Risk.Value
		default:
			name, text = "verifyMethod", field.Value.Verify.Value
		}
		fields[i] = Field{
			Name:        name,
			Value:       Value{Value: syntax.DecodeEntities(text), Span: span},
			Span:        field.Span,
			KeywordSpan: field.Keyword.Span,
			ColonSpan:   field.Colon,
		}
	}
	return fields
}

func elementFields(body *syn.ElementBody) []Field {
	fields := make([]Field, len(body.Fields))
	for i, field := range body.Fields {
		name, text, span := "docref", field.Value.Ref.Value, field.Value.Ref.Span
		if field.Value.Kind == "Type" {
			name, text, span = "type", field.Value.Type.Value, field.Value.Type.Span
		}
		fields[i] = Field{
			Name:        name,
			Value:       Value{Value: syntax.DecodeEntities(text), Span: span},
			Span:        field.Span,
			KeywordSpan: field.Keyword.Span,
			ColonSpan:   field.Colon,
		}
	}
	return fields
}

func (r *Requirement) Rows() []string {
	rows := []string{"<<" + r.Kind + ">>", syntax.DecodeEntities(r.Name)}
	rows = appendRow(rows, "ID", r.Id)
	rows = appendRow(rows, "Text", r.Text)
	rows = appendRow(rows, "Risk", r.Risk)
	rows = appendRow(rows, "Verification", r.VerifyMethod)
	return rows
}

func (e *Element) Rows() []string {
	rows := []string{"<<Element>>", syntax.DecodeEntities(e.Name)}
	rows = appendRow(rows, "Type", e.Kind)
	rows = appendRow(rows, "Doc Ref", e.Docref)
	return rows
}

func appendRow(rows []string, label, text string) []string {
	if text == "" {
		return rows
	}
	return append(rows, label+": "+text)
}
