package kanban

import (
	"strconv"
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/kanban"
)

const (
	codeItemsWithoutSection = "kanban/items-without-section"
	codeMalformedMetadata   = "kanban/malformed-metadata"
	codeInvalidShape        = "kanban/invalid-shape"
	codeNoNode              = "kanban/decoration-without-node"

	defaultNodePadding  = 10
	defaultNodeMaxWidth = 200
)

func Resolve(src []byte, document *syn.Start) (*Model, []diag.Diagnostic) {
	r := &resolver{src: src, model: &Model{Config: readConfig(src)}, offender: -1}
	for _, item := range document.Document.Items {
		r.statement(item.Statement)
	}
	return r.model, r.diags
}

type resolver struct {
	src      []byte
	model    *Model
	diags    []diag.Diagnostic
	counter  int
	offender int
}

func (r *resolver) report(code, message string, span source.Span) {
	r.diags = append(r.diags, syn.Diagnostic(code, message, span))
}

func (r *resolver) statement(statement syn.Statement) {
	switch {
	case statement.Node != nil:
		r.insert(statement)
	case statement.Icon != nil:
		r.decorate(statement.Icon, func(n *Node) { n.Icon = syntax.DecodeEntities(normalizeNewlines(statement.Icon.Text)) })
	case statement.Class != nil:
		r.decorate(statement.Class, func(n *Node) { n.Class = syntax.DecodeEntities(normalizeNewlines(statement.Class.Text)) })
	}
}

func (r *resolver) decorate(token *syn.Token, apply func(*Node)) {
	if len(r.model.Nodes) == 0 {
		r.report(codeNoNode, "decoration requires a preceding node", token.Span)
		return
	}
	apply(&r.model.Nodes[len(r.model.Nodes)-1])
}

func (r *resolver) insert(statement syn.Statement) {
	node := r.nodeOf(statement)
	if statement.Data != nil && !r.applyMetadata(&node, statement.Data) {
		return
	}
	parent, ok := r.sectionFor(node.Level)
	if !ok {
		return
	}
	node.Index = len(r.model.Nodes)
	node.Parent = NoParent
	if parent >= 0 {
		node.Parent = parent
		node.ParentID = r.model.Nodes[parent].ID
	} else {
		r.model.Sections = append(r.model.Sections, node.Index)
	}
	r.model.Nodes = append(r.model.Nodes, node)
}

func (r *resolver) nodeOf(statement syn.Statement) Node {
	ast := statement.Node
	first := ast.Open
	if ast.ID != nil {
		first = ast.ID
	}
	level, anchor := 0, first.Span
	if statement.Indent != nil {
		level, anchor = utf8.RuneCountInString(statement.Indent.Text), statement.Indent.Span
	}
	identity, descr, kind := "", "", TypeDefault
	if ast.Open == nil {
		identity, descr = ast.ID.Text, ast.ID.Text
	} else {
		identity, descr, kind = ast.Descr.Text, ast.Descr.Text, typeOf(ast.Open.Text, ast.Close.Text)
		if ast.ID != nil {
			identity = ast.ID.Text
		}
	}
	node := Node{
		ID:      r.identifier(syntax.DecodeEntities(normalizeNewlines(identity))),
		Level:   level,
		Label:   syntax.DecodeEntities(normalizeNewlines(descr)),
		Width:   r.model.Config.NodeMaxWidth,
		Padding: r.model.Config.NodePadding,
		Type:    kind,
		Anchor:  anchor,
		Span:    ast.Span,
	}
	if kind == TypeRoundedRect || kind == TypeRect || kind == TypeHexagon {
		node.Padding *= 2
	}
	return node
}

func (r *resolver) identifier(id string) string {
	if id != "" {
		return id
	}
	generated := "kbn" + strconv.Itoa(r.counter)
	r.counter++
	return generated
}

func normalizeNewlines(text string) string {
	return strings.ReplaceAll(strings.ReplaceAll(text, "\r\n", "\n"), "\r", "\n")
}

func typeOf(open, closing string) NodeType {
	switch open {
	case "[":
		return TypeRect
	case "(":
		if closing == ")" {
			return TypeRoundedRect
		}
		return TypeCloud
	case "((":
		return TypeCircle
	case ")":
		return TypeCloud
	case "))":
		return TypeBang
	case "{{":
		return TypeHexagon
	}
	return TypeDefault
}

func (r *resolver) sectionFor(level int) (int, bool) {
	nodes := r.model.Nodes
	base := level
	if len(nodes) > 0 {
		base = nodes[0].Level
	}
	last := -1
	for i := len(nodes) - 1; i >= 0; i-- {
		if nodes[i].Level == base && last < 0 {
			last = i
		}
		if nodes[i].Level < base {
			r.rejectBelow(i)
			return 0, false
		}
	}
	if level == base {
		return NoParent, true
	}
	return last, true
}

func (r *resolver) rejectBelow(offender int) {
	if r.offender == offender {
		return
	}
	r.offender = offender
	node := r.model.Nodes[offender]
	r.report(codeItemsWithoutSection, "items without section detected at "+node.Label, node.Anchor)
}

func readConfig(src []byte) Config {
	pre := syntax.Preprocess(src)
	config := Config{NodePadding: defaultNodePadding, NodeMaxWidth: defaultNodeMaxWidth}
	for _, block := range []syntax.ConfigValue{pre.Config, pre.Init} {
		readBlock(&config, block)
	}
	return config
}

func readBlock(config *Config, block syntax.ConfigValue) {
	if block.Kind != syntax.ValueMapping {
		return
	}
	for _, entry := range block.Entries {
		if entry.Value.Kind != syntax.ValueMapping {
			continue
		}
		switch entry.Key {
		case "kanban":
			readFields(entry.Value, config.setKanban)
		case "mindmap":
			readFields(entry.Value, config.setMindmap)
		}
	}
}

func (c *Config) setKanban(key string, value int64) {
	switch {
	case key == "padding":
		c.Padding, c.PaddingSet = value, true
	case key == "sectionWidth" && value > 0:
		c.SectionWidth, c.SectionWidthSet = value, true
	}
}

func (c *Config) setMindmap(key string, value int64) {
	switch key {
	case "padding":
		c.NodePadding = value
	case "maxNodeWidth":
		c.NodeMaxWidth = value
	}
}

func readFields(block syntax.ConfigValue, apply func(string, int64)) {
	for _, field := range block.Entries {
		value, err := strconv.ParseInt(field.Value.Text, 10, 64)
		if field.Value.Kind != syntax.ValueInteger || err != nil || value < 0 {
			continue
		}
		apply(field.Key, value)
	}
}
