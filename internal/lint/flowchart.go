package lint

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	flowmodel "github.com/gosuda/elegant-mermaid/internal/model/flowchart"
)

const (
	kindFlowchart = "flowchart"
	firstDeclared = "first declared here"
)

func flowchartRules() map[string]ruleFunc {
	return map[string]ruleFunc{
		"flowchart/duplicate-ids":         flowchart(duplicateIDs),
		"flowchart/label-at-in-unquoted":  flowchart(labelAtInUnquoted),
		"flowchart/subgraph-id-collision": flowchart(subgraphIDCollision),
	}
}

func flowchartOnly(rule ruleFunc) ruleFunc {
	return func(a *Analysis, row Row) []diag.Diagnostic {
		if a.Block.Kind != kindFlowchart {
			return nil
		}
		return rule(a, row)
	}
}

func flowchart(rule func(m *flowmodel.Model, row Row) []diag.Diagnostic) ruleFunc {
	return flowchartOnly(func(a *Analysis, row Row) []diag.Diagnostic {
		return rule(a.Flowchart(), row)
	})
}

func duplicateIDs(m *flowmodel.Model, row Row) []diag.Diagnostic {
	var out []diag.Diagnostic
	for i := range m.Nodes {
		out = append(out, conflictingDecls(&m.Nodes[i], row)...)
	}
	return out
}

func conflictingDecls(n *flowmodel.Node, row Row) []diag.Diagnostic {
	var first *flowmodel.Decl
	var out []diag.Diagnostic
	for i := range n.Decls {
		d := &n.Decls[i]
		switch {
		case !d.HasLabel:
		case first == nil:
			first = d
		case d.Label != first.Label:
			found := diagnostic(row, row.Summary, d.ID)
			found.Related = []diag.Related{{Span: first.ID, Message: firstDeclared}}
			out = append(out, found)
		}
	}
	return out
}

func subgraphIDCollision(m *flowmodel.Model, row Row) []diag.Diagnostic {
	var out []diag.Diagnostic
	for _, span := range m.SubgraphCollisions {
		out = append(out, diagnostic(row, row.Summary, span))
	}
	return out
}

func labelAtInUnquoted(m *flowmodel.Model, row Row) []diag.Diagnostic {
	var out []diag.Diagnostic
	for _, span := range m.UnquotedAtSpans {
		out = append(out, diagnostic(row, row.Summary, span))
	}
	return out
}
