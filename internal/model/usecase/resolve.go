package usecase

import (
	"fmt"
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/usecase"
)

func (m *Model) node(id string) *Node {
	for i := range m.Nodes {
		if m.Nodes[i].ID == id {
			return &m.Nodes[i]
		}
	}
	return nil
}

func (m *Model) relationByID(id string) *Relation {
	return m.findRelation(func(r *Relation) bool { return r.ID == id })
}

func (m *Model) explicitRelation(id string) *Relation {
	return m.findRelation(func(r *Relation) bool { return r.Explicit && r.ID == id })
}

func (m *Model) findRelation(match func(*Relation) bool) *Relation {
	for i := range m.Relations {
		if match(&m.Relations[i]) {
			return &m.Relations[i]
		}
	}
	return nil
}

func (m *Model) edgeSymbol(id string) (source.Span, bool) {
	for _, s := range m.edgeSymbols {
		if s.id == id {
			return s.span, true
		}
	}
	return source.Span{}, false
}

func (m *Model) collect(st *syn.Statement, ds *[]diag.Diagnostic) {
	switch {
	case st.Actor != nil:
		for i := range st.Actor.Items {
			m.actor(&st.Actor.Items[i], "", ds)
		}
		m.endpointDeclaration(st.Actor.Relation, ds)
	case st.Entity != nil:
		if st.Entity.Relation == nil || explicit(&st.Entity.Name) {
			m.declareEntity(&st.Entity.Name, "", ds)
		}
		m.endpointDeclaration(st.Entity.Relation, ds)
	case st.SystemBoundary != nil:
		m.boundary(st.SystemBoundary, ds)
	case st.JSON != nil:
		node := newNode(st.JSON.ID, nil, KindJSON, st.JSON.Span)
		node.Shape = "rect"
		object := jsonObject(&st.JSON.Object)
		node.JSON = &object
		node.Classes = classes(st.JSON.Classes)
		m.declare(node, ds)
	}
}

func (m *Model) endpointDeclaration(tail *syn.RelationTail, ds *[]diag.Diagnostic) {
	if tail != nil && explicit(&tail.Endpoint) {
		m.declareEntity(&tail.Endpoint, "", ds)
	}
}

func relationTail(st *syn.Statement) *syn.RelationTail {
	switch {
	case st.Actor != nil:
		return st.Actor.Relation
	case st.Entity != nil:
		return st.Entity.Relation
	}
	return nil
}

func (m *Model) reserveEdge(st *syn.Statement, ds *[]diag.Diagnostic) {
	tail := relationTail(st)
	if tail == nil || tail.ID == nil {
		return
	}
	token := *tail.ID
	var earlier source.Span
	var found bool
	if node := m.node(token.Text); node != nil {
		earlier, found = node.Span, true
	} else {
		earlier, found = m.edgeSymbol(token.Text)
	}
	if found {
		later, first := token.Span, earlier
		if token.Span.Start < earlier.Start {
			later, first = earlier, token.Span
		}
		*ds = append(*ds, conflict(token.Text, "duplicate symbol id", later, first))
	}
	m.edgeSymbols = append(m.edgeSymbols, edgeSymbol{id: token.Text, span: token.Span})
}

func (m *Model) declare(incoming Node, ds *[]diag.Diagnostic) {
	previous := m.node(incoming.ID)
	if previous == nil {
		m.Nodes = append(m.Nodes, incoming)
		return
	}
	if reason := declarationDifference(previous, &incoming); reason != "" {
		*ds = append(*ds, conflict(incoming.ID, reason, incoming.Span, previous.Span))
		return
	}
	previous.Classes = appendUnique(previous.Classes, incoming.Classes...)
}

func (m *Model) actor(item *syn.ActorItem, parent string, ds *[]diag.Diagnostic) {
	node := newNode(item.Name.ID, item.Name.Label, KindActor, item.Span)
	node.Shape = "usecaseActor"
	node.Parent = parent
	node.Classes = classes(item.Classes)
	node.Stereotype = stereotype(item.Stereotype)
	applyMetadata(&node, item.Metadata, ds)
	m.declare(node, ds)
}

func (m *Model) declareEntity(name *syn.EntityName, parent string, ds *[]diag.Diagnostic) {
	node := entity(name, parent)
	if name.Metadata != nil {
		applyMetadata(&node, &name.Metadata.Metadata, ds)
	}
	m.declare(node, ds)
}

func (m *Model) boundary(st *syn.SystemBoundaryStatement, ds *[]diag.Diagnostic) {
	node := newNode(st.Name.ID, st.Name.Label, KindBoundary, st.Span)
	node.Shape = "rect"
	node.Classes = classes(st.Classes)
	applyMetadata(&node, st.Metadata, ds)
	id := node.ID
	elements := st.Content.Elements
	for i := range elements {
		node.Members = boundaryMembers(node.Members, &elements[i])
	}
	m.declare(node, ds)
	for i := range elements {
		m.boundaryElement(&elements[i], id, ds)
	}
}

func (m *Model) boundaryElement(element *syn.BoundaryElement, parent string, ds *[]diag.Diagnostic) {
	switch {
	case element.Actor != nil:
		for i := range element.Actor.Items {
			m.actor(&element.Actor.Items[i], parent, ds)
		}
	case element.Entity != nil:
		m.declareEntity(&element.Entity.Name, parent, ds)
	}
}

func (m *Model) occurrence(id string, span source.Span) {
	if node := m.node(id); node != nil && span.Start < node.FirstSpan.Start {
		node.FirstSpan = span
	}
}

func (m *Model) reference(name *syn.EntityName, ds *[]diag.Diagnostic) string {
	id := identity(name.ID)
	if !explicit(name) && name.Classes != nil {
		*ds = append(*ds, issue("usecase/reference-class-suffix", fmt.Sprintf("endpoint %s uses classes without a declaration", id), name.Span))
	}
	if node := m.node(id); node != nil {
		if name.Span.Start < node.FirstSpan.Start {
			node.FirstSpan = name.Span
		}
	} else if _, symbol := m.edgeSymbol(id); !symbol {
		m.Nodes = append(m.Nodes, entity(name, ""))
	}
	return id
}

func (m *Model) connect(st *syn.Statement, ds *[]diag.Diagnostic) {
	switch {
	case st.Actor != nil:
		if len(st.Actor.Items) > 0 && st.Actor.Relation != nil {
			m.addRelation(identity(st.Actor.Items[0].Name.ID), st.Actor.Relation, st.Span, ds)
		}
	case st.Entity != nil:
		if st.Entity.Relation != nil {
			from := m.reference(&st.Entity.Name, ds)
			m.addRelation(from, st.Entity.Relation, st.Span, ds)
		}
	}
}

func (m *Model) addRelation(from string, tail *syn.RelationTail, span source.Span, ds *[]diag.Diagnostic) {
	to := m.reference(&tail.Endpoint, ds)
	var id string
	if tail.ID != nil {
		id = tail.ID.Text
	} else {
		id = fmt.Sprintf("edge-%d", m.anonymousRelations())
	}
	if m.relationByID(id) != nil {
		return
	}
	relation := Relation{ID: id, Explicit: tail.ID != nil, From: from, To: to, Kind: "association", MarkerStart: "none", MarkerEnd: "none", MinLength: 1, Span: span}
	applyArrow(&relation, &tail.Arrow)
	m.Relations = append(m.Relations, relation)
}

func (m *Model) anonymousRelations() int {
	n := 0
	for i := range m.Relations {
		if !m.Relations[i].Explicit {
			n++
		}
	}
	return n
}

func (m *Model) configure(src []byte, st *syn.Statement, ds *[]diag.Diagnostic) {
	switch {
	case st.Direction != nil:
		m.Direction = canonicalDirection(st.Direction.Direction.Text)
	case st.AccTitle != nil:
		m.AccTitle = strings.TrimSpace(st.AccTitle.Value)
	case st.AccDescr != nil:
		m.AccDescr = strings.TrimSpace(st.AccDescr.Value)
	case st.MetadataAssignment != nil:
		m.assignment(st.MetadataAssignment, ds)
	case st.Note != nil:
		m.note(st.Note, ds)
	case st.ClassDef != nil:
		m.definition(src, st.ClassDef)
	case st.Class != nil:
		m.applyClassStatement(st.Class, ds)
	case st.Style != nil:
		m.applyStyle(src, st.Style, ds)
	}
}

func canonicalDirection(direction string) string {
	if direction == "TD" {
		return "TB"
	}
	return direction
}

func (m *Model) applyClassStatement(st *syn.ClassStatement, ds *[]diag.Diagnostic) {
	for _, target := range st.Targets {
		m.applyClasses(target, st.Classes, ds)
	}
}

func (m *Model) assignment(st *syn.MetadataAssignmentStatement, ds *[]diag.Diagnostic) {
	id := identity(st.Target.Token)
	m.occurrence(id, st.Target.Span)
	if node := m.node(id); node != nil {
		applyMetadata(node, &st.Metadata, ds)
		return
	}
	if edge := m.explicitRelation(id); edge != nil {
		for i := range st.Metadata.Properties {
			applyEdgeMetadata(edge, &st.Metadata.Properties[i], ds)
		}
		return
	}
	*ds = append(*ds, unresolved("metadata", id, st.Target.Span))
}

func (m *Model) note(st *syn.NoteStatement, ds *[]diag.Diagnostic) {
	target := st.Target.Text
	m.occurrence(target, st.Target.Span)
	if node := m.node(target); node == nil || node.Kind != KindActor && node.Kind != KindUsecase {
		*ds = append(*ds, unresolved("note", target, st.Target.Span))
		return
	}
	for ordinal := len(m.Notes); ; ordinal++ {
		id := fmt.Sprintf("note-%d", ordinal)
		if m.node(id) == nil && m.relationByID(id) == nil && !m.hasNote(id) {
			m.Notes = append(m.Notes, Note{ID: id, Target: target, Text: st.Label.Text, Span: st.Span})
			return
		}
	}
}

func (m *Model) hasNote(id string) bool {
	return slices.ContainsFunc(m.Notes, func(n Note) bool { return n.ID == id })
}

func (m *Model) definition(src []byte, st *syn.ClassDefStatement) {
	text := string(src[st.Styles.Span.Start:st.Styles.Span.End])
	for _, class := range st.Classes {
		if i := slices.IndexFunc(m.Definitions, func(d Definition) bool { return d.Name == class.Text }); i >= 0 {
			m.Definitions[i].Text = text
		} else {
			m.Definitions = append(m.Definitions, Definition{Name: class.Text, Text: text})
		}
	}
}

func (m *Model) styled(target syn.Token) (*Node, *Relation) {
	m.occurrence(target.Text, target.Span)
	if node := m.node(target.Text); node != nil && !node.Generated {
		return node, nil
	}
	return nil, m.explicitRelation(target.Text)
}

func (m *Model) applyClasses(target syn.Token, values []syn.Token, ds *[]diag.Diagnostic) {
	node, edge := m.styled(target)
	for _, value := range values {
		switch {
		case node != nil:
			node.Classes = appendUnique(node.Classes, value.Text)
		case edge != nil:
			edge.Classes = appendUnique(edge.Classes, value.Text)
		}
	}
	if node == nil && edge == nil {
		*ds = append(*ds, unresolved("class", target.Text, target.Span))
	}
}

func (m *Model) applyStyle(src []byte, st *syn.StyleStatement, ds *[]diag.Diagnostic) {
	text := string(src[st.Styles.Span.Start:st.Styles.Span.End])
	node, edge := m.styled(st.Target)
	switch {
	case node != nil:
		node.Styles = append(node.Styles, text)
	case edge != nil:
		edge.Styles = append(edge.Styles, text)
	default:
		*ds = append(*ds, unresolved("style", st.Target.Text, st.Target.Span))
	}
}

func (m *Model) validateRelation(edge *Relation, ds *[]diag.Diagnostic) {
	from, to := m.node(edge.From), m.node(edge.To)
	reason := relationshipError(edge, from, to)
	if reason == "" {
		return
	}
	d := issue("usecase/invalid-relationship", fmt.Sprintf("invalid %s relationship: %s", edge.Kind, reason), edge.Span)
	endpoint := to
	if from != nil && from.Kind == KindBoundary {
		endpoint = from
	}
	if endpoint != nil {
		d.Related = []diag.Related{{Span: endpoint.Span, Message: "endpoint declared here"}}
	}
	*ds = append(*ds, d)
}

func relationshipError(edge *Relation, from, to *Node) string {
	if from == nil || to == nil {
		return "edge symbols cannot be endpoints"
	}
	if from.Kind == KindBoundary || to.Kind == KindBoundary {
		return "boundaries cannot be endpoints"
	}
	switch edge.Kind {
	case "include", "extend":
		return includeError(from, to)
	case "generalization":
		return generalizationError(from, to)
	}
	return jsonEndpointError(edge, from, to)
}

func includeError(from, to *Node) string {
	if from.Kind != KindUsecase || to.Kind != KindUsecase {
		return "both endpoints must be use cases"
	}
	return ""
}

func generalizationError(from, to *Node) string {
	if from.Kind != to.Kind || from.Kind != KindActor && from.Kind != KindUsecase {
		return "both endpoints must be actors or both use cases"
	}
	return ""
}

func jsonEndpointError(edge *Relation, from, to *Node) string {
	if (from.Kind == KindJSON || to.Kind == KindJSON) && (!plainMarker(edge.MarkerStart) || !plainMarker(edge.MarkerEnd)) {
		return "JSON endpoints require a solid point or markerless association"
	}
	return ""
}

func plainMarker(marker string) bool { return marker == "none" || marker == "point" }
