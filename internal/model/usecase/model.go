package usecase

import (
	"fmt"
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/usecase"
)

type Kind uint8

const (
	KindActor Kind = iota
	KindUsecase
	KindBoundary
	KindJSON
)

func (k Kind) String() string {
	return [...]string{"actor", "usecase", "boundary", "json"}[k]
}

type Field struct{ Key, Value string }

type JSONKind uint8

const (
	JSONObject JSONKind = iota
	JSONArray
	JSONScalar
)

type JSON struct {
	Kind   JSONKind
	Keys   []string
	Values []JSON
	Scalar string
}

type Node struct {
	ID, Label       string
	LabelKind       syn.LabelKind
	Kind            Kind
	Shape, Parent   string
	Members         []string
	Stereotype      string
	Classes, Styles []string
	Metadata        []Field
	ActorType, Icon string
	Business        bool
	BoundaryType    string
	JSON            *JSON
	Span, FirstSpan source.Span
	Generated       bool
}

type Relation struct {
	ID                     string
	Explicit               bool
	From, To, Kind, Label  string
	MarkerStart, MarkerEnd string
	MinLength              int
	Animate                bool
	Animation              string
	Span                   source.Span
	Classes, Styles        []string
}

type Note struct {
	ID, Target, Text string
	Span             source.Span
}

type Definition struct{ Name, Text string }

type Model struct {
	Nodes              []Node
	Relations          []Relation
	Notes              []Note
	Definitions        []Definition
	Direction          string
	AccTitle, AccDescr string
	edgeSymbols        []edgeSymbol
}

type edgeSymbol struct {
	id   string
	span source.Span
}

func Resolve(src []byte, start *syn.Start) (*Model, []diag.Diagnostic) {
	var statements []*syn.Statement
	for i := range start.Lines {
		if st := start.Lines[i].Statement; st != nil {
			statements = append(statements, st)
		}
	}
	m := &Model{Direction: "TB"}
	var ds []diag.Diagnostic
	for _, st := range statements {
		m.collect(st, &ds)
	}
	for _, st := range statements {
		m.reserveEdge(st, &ds)
	}
	for _, st := range statements {
		m.connect(st, &ds)
	}
	for _, st := range statements {
		m.configure(src, st, &ds)
	}
	for i := range m.Nodes {
		validateNode(&m.Nodes[i], &ds)
	}
	for i := range m.Relations {
		m.validateRelation(&m.Relations[i], &ds)
	}
	slices.SortStableFunc(m.Nodes, func(a, b Node) int { return a.FirstSpan.Start - b.FirstSpan.Start })
	diag.Sort(ds)
	return m, ds
}

func issue(code, message string, span source.Span) diag.Diagnostic {
	return diag.Diagnostic{Code: code, Severity: diag.SeverityError, Message: message, Span: span}
}

func conflict(id, reason string, later, earlier source.Span) diag.Diagnostic {
	d := issue("usecase/declaration-conflict", fmt.Sprintf("conflicting declaration of %s: %s", id, reason), later)
	d.Related = []diag.Related{{Span: earlier, Message: "first declared here"}}
	return d
}

func unresolved(kind, id string, span source.Span) diag.Diagnostic {
	return issue("usecase/unresolved-target", fmt.Sprintf("unresolved %s target %s", kind, id), span)
}

func isQuoted(token syn.Token) bool {
	return token.Kind == "PLAIN_STRING" || token.Kind == "MARKDOWN_STRING"
}

func content(token syn.Token) string {
	switch token.Kind {
	case "PLAIN_STRING":
		return token.Text[1 : len(token.Text)-1]
	case "MARKDOWN_STRING":
		return token.Text[2 : len(token.Text)-2]
	}
	return token.Text
}

func identity(token syn.Token) string {
	text := content(token)
	if !isQuoted(token) {
		return text
	}
	return strings.Map(func(r rune) rune {
		if r < 0x80 && (r == '_' || 'a' <= r && r <= 'z' || 'A' <= r && r <= 'Z' || '0' <= r && r <= '9') {
			return r
		}
		return '_'
	}, text)
}

func classes(suffix *syn.ClassSuffix) []string {
	var result []string
	if suffix != nil {
		for _, token := range suffix.Classes {
			result = appendUnique(result, token.Text)
		}
	}
	return result
}

func appendUnique(target []string, values ...string) []string {
	for _, value := range values {
		if !slices.Contains(target, value) {
			target = append(target, value)
		}
	}
	return target
}

func newNode(token syn.Token, label *syn.NodeLabel, kind Kind, span source.Span) Node {
	node := Node{
		ID: identity(token), Label: content(token), Kind: kind, Shape: "usecaseEllipse", ActorType: "normal", BoundaryType: "rect",
		Span: span, FirstSpan: span, Generated: isQuoted(token),
	}
	switch token.Kind {
	case "PLAIN_STRING":
		node.LabelKind = syn.LabelQuoted
	case "MARKDOWN_STRING":
		node.LabelKind = syn.LabelMarkdown
	}
	if label != nil {
		node.Label, node.LabelKind = label.Text, label.Kind
	}
	return node
}

func entity(name *syn.EntityName, parent string) Node {
	node := newNode(name.ID, name.Label, KindUsecase, name.Span)
	if name.Delimiters != nil && name.Delimiters.Open.Text == "[" {
		node.Shape = "rect"
	}
	node.Parent = parent
	node.Classes = classes(name.Classes)
	node.Stereotype = stereotype(name.Stereotype)
	return node
}

func stereotype(s *syn.Stereotype) string {
	if s == nil {
		return ""
	}
	return strings.TrimSpace(s.Content.Text)
}

func explicit(name *syn.EntityName) bool {
	return name.Label != nil || isQuoted(name.ID) || name.Metadata != nil || name.Stereotype != nil
}

func declarationDifference(a, b *Node) string {
	if reason := identityDifference(a, b); reason != "" {
		return reason
	}
	return contentDifference(a, b)
}

func identityDifference(a, b *Node) string {
	switch {
	case a.Generated || b.Generated:
		return "duplicate generated id"
	case a.Kind != b.Kind:
		return "different kind"
	case a.Kind == KindJSON:
		return "duplicate JSON id"
	}
	return ""
}

func contentDifference(a, b *Node) string {
	switch {
	case a.Label != b.Label || a.LabelKind != b.LabelKind:
		return "different label"
	case a.Shape != b.Shape:
		return "different shape"
	case a.Parent != b.Parent:
		return "different parent boundary"
	case a.Stereotype != b.Stereotype:
		return "different stereotype"
	case !sameMetadata(a.Metadata, b.Metadata):
		return "different metadata"
	}
	return ""
}

func sameMetadata(a, b []Field) bool {
	return len(a) == len(b) && !slices.ContainsFunc(a, func(f Field) bool { return !slices.Contains(b, f) })
}

func boundaryMembers(members []string, element *syn.BoundaryElement) []string {
	switch {
	case element.Actor != nil:
		for i := range element.Actor.Items {
			members = appendUnique(members, identity(element.Actor.Items[i].Name.ID))
		}
	case element.Entity != nil:
		members = appendUnique(members, identity(element.Entity.Name.ID))
	}
	return members
}

func jsonObject(object *syn.JsonObject) JSON {
	result := JSON{Kind: JSONObject}
	for i := range object.Properties {
		result.Keys = append(result.Keys, object.Properties[i].Key.Text)
		result.Values = append(result.Values, jsonValue(&object.Properties[i].Value))
	}
	return result
}

func jsonValue(value *syn.JsonValue) JSON {
	switch value.Kind {
	case syn.JSONObject:
		return jsonObject(&value.Object)
	case syn.JSONArray:
		result := JSON{Kind: JSONArray}
		for i := range value.Array {
			result.Values = append(result.Values, jsonValue(&value.Array[i]))
		}
		return result
	}
	return JSON{Kind: JSONScalar, Scalar: value.Scalar.Text}
}
