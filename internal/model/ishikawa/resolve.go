package ishikawa

import (
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/ishikawa"
)

const codeNesting = "limit/nesting-depth"

type active struct {
	level int
	node  int
}

type resolver struct {
	model *Model
	diags []diag.Diagnostic
	stack []active
	base  int
	based bool
}

func Resolve(_ []byte, document *syn.Start) (*Model, []diag.Diagnostic) {
	r := &resolver{model: &Model{}}
	for _, item := range document.Document.Items {
		if text := item.Statement.Text; text != nil {
			r.add(item.Statement, text)
		}
	}
	return r.model, r.diags
}

func (r *resolver) add(statement syn.Statement, text *syn.Token) {
	raw := 0
	if statement.Indent != nil {
		raw = utf8.RuneCountInString(statement.Indent.Text)
	}
	node := Node{Index: len(r.model.Nodes), Parent: NoParent, Label: syntax.DecodeEntities(strings.TrimFunc(text.Text, syn.IsSpace)), Span: text.Span}
	if len(r.model.Nodes) == 0 {
		r.model.Nodes = append(r.model.Nodes, node)
		r.stack = []active{{level: 0, node: 0}}
		return
	}
	if !r.based {
		r.base, r.based = raw, true
	}
	level := max(raw-r.base+1, 1)
	for len(r.stack) > 1 && r.stack[len(r.stack)-1].level >= level {
		r.stack = r.stack[:len(r.stack)-1]
	}
	if len(r.stack) > MaxDepth {
		r.diags = append(r.diags, syn.Diagnostic(codeNesting, "nesting depth exceeds 64", text.Span))
		return
	}
	parent := r.stack[len(r.stack)-1].node
	node.Parent, node.Depth = parent, len(r.stack)
	r.model.Nodes[parent].Children = append(r.model.Nodes[parent].Children, node.Index)
	r.model.Nodes = append(r.model.Nodes, node)
	r.stack = append(r.stack, active{level: level, node: node.Index})
}
