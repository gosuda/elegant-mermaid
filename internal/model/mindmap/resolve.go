package mindmap

import (
	"slices"
	"strconv"
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/mindmap"
)

const (
	codeSecondRoot = "mindmap/second-root"
	codeNoTarget   = "mindmap/decoration-target-missing"
)

func Resolve(src []byte, document *syn.Start) (*Model, []diag.Diagnostic) {
	r := &resolver{model: &Model{Config: readConfig(src)}}
	for _, item := range document.Document.Items {
		r.statement(item.Statement)
	}
	return r.model, r.diags
}

type resolver struct {
	model *Model
	diags []diag.Diagnostic
	base  int
}

func (r *resolver) statement(statement syn.Statement) {
	switch {
	case statement.Node != nil:
		r.insert(statement)
	case statement.Icon != nil:
		r.decorate(statement.Icon, func(n *Node) { n.Icon = normalizeNewlines(statement.Icon.Text) })
	case statement.Class != nil:
		r.decorate(statement.Class, func(n *Node) { n.Class = normalizeNewlines(statement.Class.Text) })
	}
}

func (r *resolver) decorate(token *syn.Token, apply func(*Node)) {
	if len(r.model.Nodes) == 0 {
		r.diags = append(r.diags, syn.Diagnostic(codeNoTarget, "decoration has no preceding node", token.Span))
		return
	}
	apply(&r.model.Nodes[len(r.model.Nodes)-1])
}

func (r *resolver) insert(statement syn.Statement) {
	node := nodeOf(statement.Node)
	raw := 0
	if statement.Indent != nil {
		raw = utf8.RuneCountInString(statement.Indent.Text)
	}
	node.Index = len(r.model.Nodes)
	node.Parent = NoParent
	if node.Index == 0 {
		r.base = raw
	}
	node.Level = raw - r.base
	if node.Index > 0 {
		parent := r.parentOf(node.Level)
		if parent == NoParent {
			message := "node " + node.Label + " has no parent; only one root is allowed"
			r.diags = append(r.diags, syn.Diagnostic(codeSecondRoot, message, node.Span))
			return
		}
		node.Parent = parent
		r.model.Nodes[parent].Children = append(r.model.Nodes[parent].Children, node.Index)
	}
	r.model.Nodes = append(r.model.Nodes, node)
}

func (r *resolver) parentOf(level int) int {
	for i := len(r.model.Nodes) - 1; i >= 0; i-- {
		if r.model.Nodes[i].Level < level {
			return i
		}
	}
	return NoParent
}

func nodeOf(ast *syn.Node) Node {
	node := Node{Span: ast.Span, Markdown: ast.Description == syn.DescriptionMarkdown}
	if ast.Open == nil {
		node.SourceID = normalizeNewlines(ast.ID.Text)
		node.Description = node.SourceID
	} else {
		node.Description = normalizeNewlines(ast.Descr.Text)
		node.SourceID = node.Description
		if ast.ID != nil {
			node.SourceID = normalizeNewlines(ast.ID.Text)
		}
		node.Shape = shapeOf(ast.Open.Text, ast.Close.Text)
	}
	node.Label = syntax.DecodeEntities(strings.TrimSpace(node.Description))
	return node
}

func normalizeNewlines(text string) string {
	return strings.ReplaceAll(strings.ReplaceAll(text, "\r\n", "\n"), "\r", "\n")
}

func shapeOf(open, closing string) Shape {
	switch open {
	case "[":
		return ShapeSquare
	case "(":
		if closing == ")" {
			return ShapeRounded
		}
		return ShapeCloud
	case "((":
		return ShapeCircle
	case ")":
		return ShapeCloud
	case "))":
		return ShapeBang
	case "{{":
		return ShapeHexagon
	}
	return ShapeDefault
}

func readConfig(src []byte) Config {
	pre := syntax.Preprocess(src)
	var config Config
	for _, block := range []syntax.ConfigValue{pre.Config, pre.Init} {
		readBlock(&config, block)
	}
	return config
}

func readBlock(config *Config, block syntax.ConfigValue) {
	if block.Kind != syntax.ValueMapping {
		return
	}
	i := slices.IndexFunc(block.Entries, func(e syntax.ConfigEntry) bool { return e.Key == "mindmap" })
	if i < 0 || block.Entries[i].Value.Kind != syntax.ValueMapping {
		return
	}
	for _, field := range block.Entries[i].Value.Entries {
		value, err := strconv.ParseInt(field.Value.Text, 10, 64)
		if field.Value.Kind != syntax.ValueInteger || err != nil || value < 0 {
			continue
		}
		switch field.Key {
		case "padding":
			config.Padding, config.PaddingSet = value, true
		case "maxNodeWidth":
			config.MaxNodeWidth, config.MaxNodeWidthSet = value, true
		}
	}
}
