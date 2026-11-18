package treeview

import (
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/treeview"
)

const (
	codeNesting  = "limit/nesting-depth"
	maxDepth     = 64
	configKey    = "treeView"
	nestingHelp  = "Reduce the nesting to 64 levels or fewer."
	nestingError = "nesting depth exceeds 64"
)

func Resolve(src []byte, document *syn.TreeView) (*Model, []diag.Diagnostic) {
	m := &Model{Config: readConfig(src)}
	m.Nodes = append(m.Nodes, Node{Parent: NoParent, Level: RootLevel, Name: RootName, Directory: true})
	r := &resolver{model: m, stack: []int{0}}
	for _, node := range document.Nodes {
		r.insert(node)
	}
	m.Title, m.AccTitle, m.AccDescr = value(document.Title), value(document.AccTitle), value(document.AccDescr)
	return m, r.diags
}

func value(t *syn.Token) string {
	if t == nil {
		return ""
	}
	return t.Value
}

type resolver struct {
	model *Model
	stack []int
	diags []diag.Diagnostic
	deep  bool
}

func (r *resolver) insert(ast syn.TreeNode) {
	level := 0
	if ast.Indent != nil {
		level = len(ast.Indent.Text)
	}
	for len(r.stack) > 1 && level <= r.model.Nodes[r.stack[len(r.stack)-1]].Level {
		r.stack = r.stack[:len(r.stack)-1]
	}
	parent := r.stack[len(r.stack)-1]
	node := nodeOf(ast, level)
	node.Index = len(r.model.Nodes)
	node.Parent = parent
	node.Depth = r.model.Nodes[parent].Depth + 1
	r.model.Nodes[parent].Children = append(r.model.Nodes[parent].Children, node.Index)
	r.model.Nodes = append(r.model.Nodes, node)
	r.stack = append(r.stack, node.Index)
	r.checkDepth(node)
}

func (r *resolver) checkDepth(node Node) {
	if r.deep || node.Depth <= maxDepth {
		return
	}
	r.deep = true
	d := syn.Diagnostic(codeNesting, nestingError, node.Span)
	d.Help = nestingHelp
	r.diags = append(r.diags, d)
}

func nodeOf(ast syn.TreeNode, level int) Node {
	name := ast.Name.Value
	node := Node{Level: level, Span: ast.Span}
	if rest, ok := strings.CutSuffix(name, "/"); ok {
		name, node.Directory = rest, true
	}
	node.Name = name
	if ast.Class != nil {
		node.Class = ast.Class.Value
	}
	if ast.Icon != nil {
		node.Icon = ast.Icon.Value
		if node.Icon == "" {
			node.Icon = IconNone
		}
	}
	if ast.Desc != nil {
		node.Description = ast.Desc.Value
	}
	return node
}

func readConfig(src []byte) Config {
	pre := syntax.Preprocess(src)
	var config Config
	for _, block := range []syntax.ConfigValue{pre.Config, pre.Init} {
		config.read(block)
	}
	return config
}

func (c *Config) read(block syntax.ConfigValue) {
	if block.Kind != syntax.ValueMapping {
		return
	}
	i := slices.IndexFunc(block.Entries, func(e syntax.ConfigEntry) bool { return e.Key == configKey })
	if i < 0 || block.Entries[i].Value.Kind != syntax.ValueMapping {
		return
	}
	for _, field := range block.Entries[i].Value.Entries {
		target := c.field(field.Key)
		thousandths, ok := syntax.Thousandths(field.Value)
		if target == nil || !ok || thousandths < 0 {
			continue
		}
		*target = Length{Thousandths: thousandths, Set: true}
	}
}

func (c *Config) field(key string) *Length {
	switch key {
	case "rowIndent":
		return &c.RowIndent
	case "paddingX":
		return &c.PaddingX
	case "paddingY":
		return &c.PaddingY
	case "lineThickness":
		return &c.LineThickness
	}
	return nil
}
