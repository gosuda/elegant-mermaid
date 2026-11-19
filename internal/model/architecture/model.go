package architecture

import (
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/architecture"
)

const maxPadding = 1024

type Group struct {
	ID     string
	Icon   string
	Title  string
	Parent string
	Span   source.Span
	IDSpan source.Span
}

type Node struct {
	ID       string
	Junction bool
	Icon     string
	IconText string
	Title    string
	Parent   string
	Span     source.Span
	IDSpan   source.Span
}

type Edge struct {
	From      string
	To        string
	FromSide  string
	ToSide    string
	FromInto  bool
	ToInto    bool
	FromGroup bool
	ToGroup   bool
	Title     string
	Span      source.Span
}

type Alignment struct {
	Direction string
	Members   []string
	Span      source.Span
}

type ConfigEntry struct {
	Key   string
	Value int64
}

type EdgeDeclaration struct {
	EdgeIndex int
	Rejected  *Edge
}

type Model struct {
	HeaderSpan          source.Span
	ElementDeclarations int
	EdgeDeclarations    []EdgeDeclaration
	AccTitle            string
	AccDescr            string
	Title               string
	Groups              []Group
	Nodes               []Node
	Edges               []Edge
	Alignments          []Alignment
	Config              []ConfigEntry
}

type registration struct {
	group  bool
	idSpan source.Span
}

type resolver struct {
	model      *Model
	diags      []diag.Diagnostic
	registered map[string]registration
}

func Resolve(src []byte, document *syn.Architecture) (*Model, []diag.Diagnostic) {
	r := &resolver{model: &Model{}, registered: map[string]registration{}}
	r.model.HeaderSpan = document.Header.Span
	for _, statement := range document.Statements {
		switch statement.Kind.(type) {
		case *syn.Group, *syn.Service, *syn.Junction:
			r.model.ElementDeclarations++
		}
	}
	r.readConfig(src)
	r.metadata(document)
	r.groups(document)
	r.nodes(document)
	r.edges(document)
	r.alignments(document)
	return r.model, r.diags
}

func (r *resolver) readConfig(src []byte) {
	pre := syntax.Preprocess(src)
	var blocks []syntax.ConfigValue
	if pre.HasConfig {
		blocks = append(blocks, pre.Config)
	}
	if pre.HasInit {
		blocks = append(blocks, pre.Init)
	}
	values := map[string]int64{}
	for _, block := range blocks {
		readSizes(block, values)
	}
	for _, key := range []string{"iconSize", "padding"} {
		if value, ok := values[key]; ok {
			r.model.Config = append(r.model.Config, ConfigEntry{Key: key, Value: value})
		}
	}
}

func readSizes(block syntax.ConfigValue, values map[string]int64) {
	if block.Kind != syntax.ValueMapping {
		return
	}
	i := slices.IndexFunc(block.Entries, func(e syntax.ConfigEntry) bool { return e.Key == "architecture" })
	if i < 0 || block.Entries[i].Value.Kind != syntax.ValueMapping {
		return
	}
	for _, field := range block.Entries[i].Value.Entries {
		readSize(field, values)
	}
}

func readSize(field syntax.ConfigEntry, values map[string]int64) {
	if field.Key != "padding" && field.Key != "iconSize" || field.Value.Kind != syntax.ValueInteger {
		return
	}
	if value, ok := parseNonNegative(field.Value.Text); ok && (field.Key == "padding" || value > 0) {
		values[field.Key] = value
	}
}

func parseNonNegative(text string) (int64, bool) {
	var value int64
	for i := range len(text) {
		c := text[i]
		if c < '0' || c > '9' || value > maxPadding {
			return 0, false
		}
		value = value*10 + int64(c-'0')
	}
	return value, len(text) > 0 && value <= maxPadding
}

func (r *resolver) issue(code, message string, span source.Span) {
	r.diags = append(r.diags, syn.Diagnostic(code, message, span))
}

func (r *resolver) duplicate(id string, span source.Span, first source.Span) {
	d := syn.Diagnostic("architecture/duplicate-id", "id "+id+" is already in use", span)
	d.Related = []diag.Related{{Span: first, Message: "first declared here"}}
	r.diags = append(r.diags, d)
}

func (r *resolver) metadata(document *syn.Architecture) {
	for _, statement := range document.Statements {
		items, ok := statement.Kind.(*syn.TitleAndAccessibilities)
		if !ok {
			continue
		}
		for _, item := range items.Items {
			switch item.Field {
			case "title":
				r.model.Title = item.Value
			case "accTitle":
				r.model.AccTitle = item.Value
			default:
				r.model.AccDescr = item.Value
			}
		}
	}
}

func (r *resolver) free(id syn.Value) bool {
	first, taken := r.registered[id.Text]
	if taken {
		r.duplicate(id.Text, id.Span, first.idSpan)
	}
	return !taken
}

func (r *resolver) record(id syn.Value, group bool) {
	r.registered[id.Text] = registration{group: group, idSpan: id.Span}
}

func (r *resolver) validParent(id syn.Value, parent *syn.Value) bool {
	if parent == nil {
		return true
	}
	switch known, found := r.registered[parent.Text]; {
	case id.Text == parent.Text:
		r.issue("architecture/self-parent", "element "+id.Text+" cannot contain itself", parent.Span)
	case !found:
		r.issue("architecture/parent-not-found", "parent "+parent.Text+" does not exist", parent.Span)
	case !known.group:
		r.issue("architecture/parent-not-group", "parent "+parent.Text+" is not a group", parent.Span)
	default:
		return true
	}
	return false
}

func parentID(parent *syn.Value) string {
	if parent == nil {
		return ""
	}
	return parent.Text
}

func text(value *syn.Value) string {
	if value == nil {
		return ""
	}
	return value.Text
}

func (r *resolver) groups(document *syn.Architecture) {
	for _, statement := range document.Statements {
		node, ok := statement.Kind.(*syn.Group)
		if !ok {
			continue
		}
		if !r.free(node.ID) || !r.validParent(node.ID, node.In) {
			continue
		}
		r.record(node.ID, true)
		r.model.Groups = append(r.model.Groups, Group{ID: node.ID.Text, Icon: text(node.Icon), Title: text(node.Title), Parent: parentID(node.In), Span: statement.Span, IDSpan: node.ID.Span})
	}
}

func (r *resolver) nodes(document *syn.Architecture) {
	for _, junction := range []bool{false, true} {
		for _, statement := range document.Statements {
			r.node(statement, junction)
		}
	}
	slices.SortFunc(r.model.Nodes, func(a, b Node) int { return a.Span.Start - b.Span.Start })
}

func (r *resolver) node(statement syn.Statement, junction bool) {
	var node Node
	var id syn.Value
	var parent *syn.Value
	switch kind := statement.Kind.(type) {
	case *syn.Service:
		if junction {
			return
		}
		id, parent = kind.ID, kind.In
		node = Node{Icon: text(kind.Icon), IconText: text(kind.IconText), Title: text(kind.Title)}
	case *syn.Junction:
		if !junction {
			return
		}
		id, parent = kind.ID, kind.In
		node = Node{Junction: true}
	default:
		return
	}
	if !r.free(id) || !r.validParent(id, parent) {
		return
	}
	r.record(id, false)
	node.ID, node.Parent, node.Span, node.IDSpan = id.Text, parentID(parent), statement.Span, id.Span
	r.model.Nodes = append(r.model.Nodes, node)
}

func (r *resolver) edges(document *syn.Architecture) {
	for _, statement := range document.Statements {
		if node, ok := statement.Kind.(*syn.Edge); ok {
			index := len(r.model.Edges)
			r.edge(statement.Span, node)
			declaration := EdgeDeclaration{EdgeIndex: index}
			if len(r.model.Edges) == index {
				declaration.EdgeIndex = -1
				declaration.Rejected = &Edge{
					From: node.LhsID.Text, To: node.RhsID.Text, FromSide: node.LhsDir.Text, ToSide: node.RhsDir.Text,
					FromInto: node.LhsInto != nil, ToInto: node.RhsInto != nil, FromGroup: node.LhsGroup != nil, ToGroup: node.RhsGroup != nil,
					Span: statement.Span,
				}
			}
			r.model.EdgeDeclarations = append(r.model.EdgeDeclarations, declaration)
		}
	}
}

func (r *resolver) isNode(id syn.Value) bool {
	if r.registered[id.Text].group {
		r.issue("architecture/endpoint-not-node", "edge endpoint "+id.Text+" is not a service or junction", id.Span)
		return false
	}
	return true
}

func (r *resolver) parentOf(id string) string {
	i := slices.IndexFunc(r.model.Nodes, func(n Node) bool { return n.ID == id })
	return r.model.Nodes[i].Parent
}

func (r *resolver) edge(span source.Span, node *syn.Edge) {
	if !r.exists(node.LhsID) || !r.exists(node.RhsID) || !r.isNode(node.LhsID) || !r.isNode(node.RhsID) {
		return
	}
	left, right := r.parentOf(node.LhsID.Text), r.parentOf(node.RhsID.Text)
	if left != "" && left == right {
		for _, end := range []struct {
			id       syn.Value
			modifier *source.Span
		}{{node.LhsID, node.LhsGroup}, {node.RhsID, node.RhsGroup}} {
			if end.modifier != nil {
				r.issue("architecture/group-boundary-not-crossed", "endpoint "+end.id.Text+" has a group modifier but the edge stays in one group", *end.modifier)
				return
			}
		}
	}
	r.model.Edges = append(r.model.Edges, Edge{
		From: node.LhsID.Text, To: node.RhsID.Text, FromSide: node.LhsDir.Text, ToSide: node.RhsDir.Text,
		FromInto: node.LhsInto != nil, ToInto: node.RhsInto != nil, FromGroup: node.LhsGroup != nil, ToGroup: node.RhsGroup != nil,
		Title: text(node.Title), Span: span,
	})
}

func (r *resolver) exists(id syn.Value) bool {
	_, ok := r.registered[id.Text]
	if !ok {
		r.issue("architecture/endpoint-not-found", "edge endpoint "+id.Text+" does not exist", id.Span)
	}
	return ok
}

func (r *resolver) alignments(document *syn.Architecture) {
	for _, statement := range document.Statements {
		node, ok := statement.Kind.(*syn.Alignment)
		if !ok {
			continue
		}
		if members, ok := r.members(node); ok {
			r.model.Alignments = append(r.model.Alignments, Alignment{Direction: node.Direction.Text, Members: members, Span: statement.Span})
		}
	}
}

func (r *resolver) members(node *syn.Alignment) ([]string, bool) {
	seen := map[string]struct{}{}
	out := make([]string, 0, len(node.Members))
	for _, member := range node.Members {
		if known, ok := r.registered[member.Text]; !ok || known.group {
			r.issue("architecture/align-member-not-node", "alignment member "+member.Text+" is not a service or junction", member.Span)
			return nil, false
		}
		if _, repeated := seen[member.Text]; repeated {
			r.issue("architecture/align-duplicate-member", "alignment lists "+member.Text+" more than once", member.Span)
			return nil, false
		}
		seen[member.Text] = struct{}{}
		out = append(out, member.Text)
	}
	return out, true
}
