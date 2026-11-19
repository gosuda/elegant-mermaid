package state

import (
	"fmt"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/state"
)

type location struct {
	scope  int
	parent Parent
}

type stateSeed struct {
	id     string
	idSpan source.Span
	span   source.Span
	kind   StateKind
}

type membership struct {
	parent Parent
	state  int
}

type resolver struct {
	model       Model
	states      map[string]int
	classes     map[string]int
	links       map[string]int
	memberships map[membership]struct{}
	divider     int
	interaction []diag.Diagnostic
}

func Resolve(_ []byte, doc *syn.Start) (*Model, []diag.Diagnostic) {
	r := &resolver{
		states:      map[string]int{},
		classes:     map[string]int{},
		links:       map[string]int{},
		memberships: map[membership]struct{}{},
	}
	r.model.Occurrences = occurrences(&doc.Document)
	r.model.Scopes = append(r.model.Scopes, Scope{ID: "root", Parent: None, Direction: "TB"})
	r.document(&doc.Document, location{scope: 0})
	diagnostics := r.groupDescriptions()
	diagnostics = append(diagnostics, r.interaction...)
	return &r.model, diagnostics
}

func (r *resolver) groupDescriptions() []diag.Diagnostic {
	var out []diag.Diagnostic
	for _, group := range r.model.Composites {
		state := &r.model.States[group.State]
		if len(state.Descriptions) < 2 {
			continue
		}
		out = append(out, diag.Diagnostic{
			Code:     "state/group-description",
			Severity: diag.SeverityError,
			Message:  fmt.Sprintf("composite state %s cannot have additional descriptions", state.ID),
			Span:     state.Descriptions[1].Span,
		})
	}
	return out
}

func (r *resolver) state(seed stateSeed, at location) int {
	if index, ok := r.states[seed.id]; ok {
		return index
	}
	index := len(r.model.States)
	r.states[seed.id] = index
	r.model.States = append(r.model.States, State{
		ID:        seed.id,
		IDSpan:    seed.idSpan,
		Span:      seed.span,
		Kind:      seed.kind,
		Parent:    at.parent,
		Scope:     at.scope,
		Composite: None,
		Note:      None,
	})
	return index
}

func (r *resolver) endpoint(id *syn.IDStatement, role EndpointRole, at location) Endpoint {
	raw := strings.TrimSpace(id.ID.Text)
	if raw != "[*]" {
		role = RoleOrdinary
	}
	name := raw
	switch role {
	case RoleStart:
		name = r.model.Scopes[at.scope].ID + "_start"
	case RoleEnd:
		name = r.model.Scopes[at.scope].ID + "_end"
	}
	state := r.state(stateSeed{id: name, idSpan: id.ID.Span, span: id.Span, kind: KindDefault}, at)
	r.model.States[state].Occurrences = append(r.model.States[state].Occurrences, Occurrence{Span: id.Span, IDSpan: id.ID.Span, Scope: at.scope, Role: role})
	if id.CSSClass != nil {
		r.model.States[state].Classes = append(r.model.States[state].Classes, text(*id.CSSClass))
	}
	r.member(state, at.parent)
	return Endpoint{State: state, Span: id.Span, IDSpan: id.ID.Span, Scope: at.scope, Role: role}
}

func (r *resolver) member(state int, parent Parent) {
	if parent.Kind == ParentNone {
		return
	}
	r.model.States[state].Parent = parent
	key := membership{parent: parent, state: state}
	if _, seen := r.memberships[key]; seen {
		return
	}
	r.memberships[key] = struct{}{}
	if parent.Kind == ParentRegion {
		r.model.Regions[parent.Index].Children = append(r.model.Regions[parent.Index].Children, state)
		return
	}
	if group := r.model.States[parent.Index].Composite; group != None {
		r.model.Composites[group].Children = append(r.model.Composites[group].Children, state)
	}
}

func (r *resolver) description(state int, token syn.Token) {
	value := strings.TrimSpace(strings.TrimPrefix(strings.TrimSpace(token.Text), ":"))
	if value == "" {
		return
	}
	r.model.States[state].Descriptions = append(r.model.States[state].Descriptions, Text{Value: value, Span: token.Span})
}

func (r *resolver) document(document *syn.Document, at location) {
	for i := range document.Lines {
		if statement := document.Lines[i].Statement; statement != nil {
			r.statement(statement, at)
		}
	}
}

func (r *resolver) statement(statement *syn.Statement, at location) {
	switch node := statement.Node.(type) {
	case *syn.IDDeclaration:
		endpoint := r.endpoint(&node.ID, RoleStart, at)
		if node.Description != nil {
			r.description(endpoint.State, *node.Description)
		}
	case *syn.Transition:
		r.transition(statement, node, at)
	case *syn.Composite:
		r.composite(statement, node, at)
	case *syn.Stereotype:
		r.stereotype(statement, node, at)
	case *syn.Note:
		r.note(statement, node, at)
	default:
		r.directive(statement, at)
	}
}

func (r *resolver) transition(statement *syn.Statement, node *syn.Transition, at location) {
	from := r.endpoint(&node.From, RoleStart, at)
	to := r.endpoint(&node.To, RoleEnd, at)
	transition := Transition{From: from, To: to, Span: statement.Span, ArrowSpan: node.Arrow.Span, Scope: at.scope}
	if node.Description != nil {
		value := strings.TrimSpace(strings.TrimLeft(strings.TrimSpace(node.Description.Text), ":"))
		transition.Label = &Text{Value: value, Span: node.Description.Span}
	}
	r.model.Transitions = append(r.model.Transitions, transition)
}

func (r *resolver) stereotype(statement *syn.Statement, node *syn.Stereotype, at location) {
	kind := KindChoice
	switch node.Kind {
	case syn.StereotypeFork:
		kind = KindFork
	case syn.StereotypeJoin:
		kind = KindJoin
	}
	index := r.state(stateSeed{id: strings.TrimSpace(node.ID.Text), idSpan: node.ID.Span, span: statement.Span, kind: kind}, at)
	r.member(index, at.parent)
	r.model.States[index].Occurrences = append(r.model.States[index].Occurrences, Occurrence{Span: statement.Span, IDSpan: node.ID.Span, Scope: at.scope, Role: RoleOrdinary})
}

func (r *resolver) note(statement *syn.Statement, node *syn.Note, at location) {
	index := r.state(stateSeed{id: strings.TrimSpace(node.Target.Text), idSpan: node.Target.Span, span: statement.Span, kind: KindDefault}, at)
	r.member(index, at.parent)
	note := len(r.model.Notes)
	r.model.Notes = append(r.model.Notes, Note{
		Target:       index,
		Position:     strings.ReplaceAll(node.Position.Value, "_", " "),
		Text:         text(node.Text),
		Span:         statement.Span,
		TargetSpan:   node.Target.Span,
		PositionSpan: node.Position.Span,
		Scope:        at.scope,
	})
	r.model.States[index].Note = note
}

func occurrences(doc *syn.Document) []StatementOccurrence {
	var out []StatementOccurrence
	for _, line := range doc.Lines {
		if line.Statement == nil {
			continue
		}
		s := line.Statement
		o := StatementOccurrence{Span: s.Span}
		switch n := s.Node.(type) {
		case *syn.IDDeclaration:
			o.ID = n.ID.ID.Text
		case *syn.Composite:
			o.ID = n.ID.Text
			if n.Body != nil {
				o.HasBody = true
				o.Body = occurrences(n.Body)
				o.StatementCount = statementCount(n.Body)
			}
		case *syn.Transition:
			o.From, o.To = n.From.ID.Text, n.To.ID.Text
			if n.Description != nil {
				o.Label = n.Description.Text
			}
		default:
			continue
		}
		out = append(out, o)
	}
	return out
}

func statementCount(doc *syn.Document) int {
	count := 0
	for _, line := range doc.Lines {
		if line.Statement != nil {
			count++
		}
	}
	return count
}
