package class

import (
	"fmt"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/class"
)

type Member struct {
	Text, Name, Visibility, Parameters, ReturnType string
	Method, Static, Abstract                       bool
	Span                                           source.Span
}
type Class struct {
	ID, Label, Generic, Parent, CSS, Owner string
	Attributes, Methods                    []Member
	Annotations, Styles, TextStyles        []string
	Span                                   source.Span
	Interface                              bool
}
type Namespace struct {
	ID, Label, Parent string
	Explicit          bool
	Span              source.Span
}
type Note struct {
	ID, Target, Text, Parent string
	Span                     source.Span
}
type Relation struct {
	From, To, Label, FromMultiplicity, ToMultiplicity, MarkerStart, MarkerEnd, Line string
	Span, FromSpan, ToSpan                                                          source.Span
}
type Click struct {
	Target, Action, Value, Arguments, Tooltip, LinkTarget string
	Args                                                  []string
}
type StyleDefinition struct {
	Name               string
	Styles, TextStyles []string
}
type Model struct {
	Classes                       []Class
	Namespaces                    []Namespace
	Notes                         []Note
	Relations                     []Relation
	Clicks                        []Click
	Definitions                   []StyleDefinition
	Direction, AccTitle, AccDescr string
}
type resolver struct {
	model      *Model
	diags      []diag.Diagnostic
	interfaces int
	taken      map[string]bool
	notes      int
}

func Resolve(_ []byte, file *syn.File) (*Model, []diag.Diagnostic) {
	r := resolver{model: &Model{Direction: "TB"}, taken: make(map[string]bool)}
	r.reserve(file.Statements, "")
	r.statements(file.Statements, "")
	diag.Sort(r.diags)
	return r.model, r.diags
}

func (r *resolver) index(id string) int {
	for i := range r.model.Classes {
		if r.model.Classes[i].ID == id {
			return i
		}
	}
	return -1
}

func (r *resolver) ensure(name syn.ClassName) int {
	i := r.index(name.Value)
	if i >= 0 {
		return i
	}
	r.model.Classes = append(r.model.Classes, Class{ID: name.Value, Label: decodeEntities(name.Value), Generic: name.Generic, CSS: "default", Span: name.Span})
	return len(r.model.Classes) - 1
}

func (r *resolver) statements(statements syn.Statements, parent string) {
	for _, statement := range statements {
		r.statement(statement, parent)
	}
}

func (r *resolver) statement(s syn.Statement, parent string) {
	switch {
	case s.Class != nil:
		r.class(s.Class, parent)
	case s.Namespace != nil:
		r.namespace(s.Namespace, parent)
	case s.Member != nil:
		i := r.ensure(s.Member.Name)
		r.member(i, s.Member.Text, s.Member.Span)
	case s.Relation != nil:
		r.relation(s.Relation)
	case s.Annotation != nil:
		r.annotation(s.Annotation)
	case s.Note != nil:
		r.note(s.Note, parent)
	default:
		r.presentation(s)
	}
}

func (r *resolver) presentation(s syn.Statement) {
	switch {
	case s.Style != nil:
		r.style(s.Kind, s.Style)
	case s.Click != nil:
		r.click(s.Click)
	default:
		r.metadata(s)
	}
}

func (r *resolver) metadata(s syn.Statement) {
	switch s.Kind {
	case "direction":
		if s.Value == "TB" || s.Value == "BT" || s.Value == "LR" || s.Value == "RL" {
			r.model.Direction = s.Value
		}
	case "accTitle":
		r.model.AccTitle = s.Value
	case "accDescr":
		r.model.AccDescr = s.Value
	}
}

func (r *resolver) class(s *syn.ClassStatement, parent string) {
	i := r.ensure(s.Identifier.Name)
	c := &r.model.Classes[i]
	if parent != "" {
		c.Parent = parent
	}
	if s.Identifier.HasLabel {
		c.Label = decodeEntities(s.Identifier.Label)
	}
	if s.CSS != "" {
		c.CSS += " " + s.CSS
	}
	if s.Annotation != "" {
		c.Annotations = append(c.Annotations, s.Annotation)
	}
	for _, token := range s.Members.Tokens {
		r.member(i, token.Text, token.Span)
	}
}

func (r *resolver) namespace(s *syn.NamespaceStatement, parent string) {
	id := s.Identifier.Name.Value
	if parent != "" {
		id = parent + "." + id
	}
	prefix, previous := "", ""
	for part := range strings.SplitSeq(id, ".") {
		prefix += part
		r.ensureNamespace(prefix, part, previous, s.Span)
		previous, prefix = prefix, prefix+"."
	}
	r.explicitNamespace(id, s.Identifier.Label)
	r.statements(s.Children, id)
}

func (r *resolver) explicitNamespace(id, label string) {
	for i := range r.model.Namespaces {
		if r.model.Namespaces[i].ID != id {
			continue
		}
		r.model.Namespaces[i].Explicit = true
		if label != "" {
			r.model.Namespaces[i].Label = decodeEntities(label)
		}
	}
}

func (r *resolver) ensureNamespace(id, label, parent string, span source.Span) {
	for _, n := range r.model.Namespaces {
		if n.ID == id {
			return
		}
	}
	r.model.Namespaces = append(r.model.Namespaces, Namespace{ID: id, Label: label, Parent: parent, Span: span})
}

func (r *resolver) annotation(a *syn.AnnotationStatement) {
	i := r.index(a.Name.Value)
	if i < 0 {
		r.diags = append(r.diags, diag.Diagnostic{Code: "class/annotation-target-unknown", Severity: diag.SeverityError, Message: "annotation references unknown class " + a.Name.Value, Span: a.Name.Span})
		return
	}
	r.model.Classes[i].Annotations = append(r.model.Classes[i].Annotations, a.Annotation)
}

func (r *resolver) note(n *syn.NoteStatement, parent string) {
	target := n.Name.Value
	if r.index(target) < 0 {
		target = ""
	}
	r.model.Notes = append(r.model.Notes, Note{ID: r.generatedID("note", &r.notes), Target: target, Text: decodeEntities(n.Text), Parent: parent, Span: n.Span})
}

func (r *resolver) member(i int, text string, span source.Span) {
	text = strings.TrimSpace(text)
	if text == "" {
		return
	}
	c := &r.model.Classes[i]
	if annotation, found := strings.CutPrefix(text, "<<"); found {
		if annotation, found = strings.CutSuffix(annotation, ">>"); found {
			c.Annotations = append(c.Annotations, annotation)
			return
		}
	}
	member := ParseMember(text, span)
	if member.Method {
		c.Methods = append(c.Methods, member)
	} else {
		c.Attributes = append(c.Attributes, member)
	}
}

func relationMarker(marker syn.RelationType) string {
	switch marker {
	case "o":
		return "aggregation"
	case "<|", "|>":
		return "extension"
	case "*":
		return "composition"
	case "<", ">":
		return "dependency"
	case "()":
		return "lollipop"
	}
	return "none"
}

func (r *resolver) relation(s *syn.RelationStatement) {
	a, b := s.From, s.To
	if s.Relation.Start == "()" && s.Relation.End == "" {
		a = r.interfaceName(a, b)
	}
	if s.Relation.End == "()" && s.Relation.Start == "" {
		b = r.interfaceName(b, a)
	}
	r.ensure(a)
	r.ensure(b)
	line := "solid"
	if s.Relation.Line == ".." {
		line = "dashed"
	}
	r.model.Relations = append(r.model.Relations, Relation{From: a.Value, To: b.Value, Label: decodeEntities(s.Label), FromMultiplicity: strings.TrimSpace(s.FromMultiplicity), ToMultiplicity: strings.TrimSpace(s.ToMultiplicity), MarkerStart: relationMarker(s.Relation.Start), MarkerEnd: relationMarker(s.Relation.End), Line: line, Span: s.Span, FromSpan: s.From.Span, ToSpan: s.To.Span})
}

func (r *resolver) interfaceName(name, owner syn.ClassName) syn.ClassName {
	id := r.generatedID("interface", &r.interfaces)
	label := name.Value
	name.Value = id
	i := r.ensure(name)
	r.model.Classes[i].Label = label
	r.model.Classes[i].Interface = true
	r.model.Classes[i].Owner = owner.Value
	return name
}

func (r *resolver) generatedID(prefix string, ordinal *int) string {
	for {
		id := fmt.Sprintf("%s%d", prefix, *ordinal)
		*ordinal++
		if !r.taken[id] {
			r.taken[id] = true
			return id
		}
	}
}
func (r *resolver) reserve(statements syn.Statements, parent string) {
	for _, s := range statements {
		switch {
		case s.Class != nil:
			r.taken[s.Class.Identifier.Name.Value] = true
		case s.Member != nil:
			r.taken[s.Member.Name.Value] = true
		case s.Relation != nil:
			r.taken[s.Relation.From.Value] = true
			r.taken[s.Relation.To.Value] = true
		case s.Namespace != nil:
			id := s.Namespace.Identifier.Name.Value
			if parent != "" {
				id = parent + "." + id
			}
			prefix := ""
			for part := range strings.SplitSeq(id, ".") {
				prefix += part
				r.taken[prefix] = true
				prefix += "."
			}
			r.reserve(s.Namespace.Children, id)
		}
	}
}
