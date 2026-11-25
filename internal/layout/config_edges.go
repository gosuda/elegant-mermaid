package layout

import (
	"cmp"
	"slices"

	agentflowmodel "github.com/gosuda/elegant-mermaid/internal/model/agentflow"
	archmodel "github.com/gosuda/elegant-mermaid/internal/model/architecture"
	blockmodel "github.com/gosuda/elegant-mermaid/internal/model/block"
	c4model "github.com/gosuda/elegant-mermaid/internal/model/c4"
	classmodel "github.com/gosuda/elegant-mermaid/internal/model/class"
	cynefinmodel "github.com/gosuda/elegant-mermaid/internal/model/cynefin"
	ermodel "github.com/gosuda/elegant-mermaid/internal/model/er"
	flowmodel "github.com/gosuda/elegant-mermaid/internal/model/flowchart"
	gitmodel "github.com/gosuda/elegant-mermaid/internal/model/gitgraph"
	ishikawamodel "github.com/gosuda/elegant-mermaid/internal/model/ishikawa"
	mindmapmodel "github.com/gosuda/elegant-mermaid/internal/model/mindmap"
	reqmodel "github.com/gosuda/elegant-mermaid/internal/model/requirement"
	sankeymodel "github.com/gosuda/elegant-mermaid/internal/model/sankey"
	sequencemodel "github.com/gosuda/elegant-mermaid/internal/model/sequence"
	statemodel "github.com/gosuda/elegant-mermaid/internal/model/state"
	treeviewmodel "github.com/gosuda/elegant-mermaid/internal/model/treeview"
	usecasemodel "github.com/gosuda/elegant-mermaid/internal/model/usecase"
	wardleymodel "github.com/gosuda/elegant-mermaid/internal/model/wardley"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

// These are resolved semantic records. Layout-only connectors, containment,
// chart curves, and schedule operands do not create config-counted edges.
var edgeStatementCollectors = map[string]func(*Diagram) []source.Span{
	"flowchart": func(d *Diagram) []source.Span {
		return edgeSpansOf(d.flowchart.Edges, func(e flowmodel.Edge) source.Span { return e.StatementSpan })
	},
	"swimlane": func(d *Diagram) []source.Span {
		return edgeSpansOf(d.swimlane.Flowchart.Edges, func(e flowmodel.Edge) source.Span { return e.StatementSpan })
	},
	"agentflow": func(d *Diagram) []source.Span {
		return edgeSpansOf(d.agentflow.Edges, func(e agentflowmodel.Edge) source.Span { return e.StatementSpan })
	},
	"architecture": func(d *Diagram) []source.Span {
		return edgeSpansOf(d.architecture.Edges, func(e archmodel.Edge) source.Span { return e.Span })
	},
	"block": func(d *Diagram) []source.Span {
		return edgeSpansOf(d.block.Edges, func(e blockmodel.Edge) source.Span { return e.StatementSpan })
	},
	"c4": func(d *Diagram) []source.Span {
		return edgeSpansOf(d.c4.Relations, func(e c4model.Relation) source.Span { return e.Span })
	},
	"class": func(d *Diagram) []source.Span {
		return edgeSpansOf(d.class.Relations, func(e classmodel.Relation) source.Span { return e.Span })
	},
	"cynefin": func(d *Diagram) []source.Span {
		return edgeSpansOf(d.cynefin.Transitions, func(e cynefinmodel.Transition) source.Span { return e.Span })
	},
	"er": func(d *Diagram) []source.Span {
		return edgeSpansOf(d.er.Relationships, func(e ermodel.Relationship) source.Span { return e.Span })
	},
	"requirement": func(d *Diagram) []source.Span {
		return edgeSpansOf(d.requirement.Relationships, func(e reqmodel.Relation) source.Span { return e.Span })
	},
	"sankey": func(d *Diagram) []source.Span {
		return edgeSpansOf(d.sankey.Links, func(e sankeymodel.Link) source.Span { return e.Span })
	},
	"state": func(d *Diagram) []source.Span {
		return edgeSpansOf(d.state.Transitions, func(e statemodel.Transition) source.Span { return e.Span })
	},
	"usecase": func(d *Diagram) []source.Span {
		return edgeSpansOf(d.usecase.Relations, func(e usecasemodel.Relation) source.Span { return e.Span })
	},
	"wardley": func(d *Diagram) []source.Span {
		return edgeSpansOf(d.wardley.Links, func(e wardleymodel.Link) source.Span { return e.Span })
	},
	"eventmodeling": (*Diagram).eventEdgeSpans,
	"gitgraph":      (*Diagram).gitEdgeSpans,
	"ishikawa": func(d *Diagram) []source.Span {
		return parentEdgeSpans(d.ishikawa.Nodes, func(n ishikawamodel.Node) (int, source.Span) { return n.Parent, n.Span })
	},
	"mindmap": func(d *Diagram) []source.Span {
		return parentEdgeSpans(d.mindmap.Nodes, func(n mindmapmodel.Node) (int, source.Span) { return n.Parent, n.Span })
	},
	"treeview": func(d *Diagram) []source.Span {
		return parentEdgeSpans(d.treeview.Nodes, func(n treeviewmodel.Node) (int, source.Span) { return n.Parent, n.Span })
	},
	"sequence": (*Diagram).sequenceEdgeSpans,
}

func (d *Diagram) resolvedEdgeSpans() []source.Span {
	if collect := edgeStatementCollectors[d.Kind]; collect != nil {
		return collect(d)
	}
	return nil
}

func edgeSpansOf[T any](edges []T, span func(T) source.Span) []source.Span {
	spans := make([]source.Span, len(edges))
	for i, edge := range edges {
		spans[i] = span(edge)
	}
	return spans
}

func parentEdgeSpans[T any](nodes []T, relation func(T) (int, source.Span)) []source.Span {
	var spans []source.Span
	for _, node := range nodes {
		if parent, span := relation(node); parent >= 0 {
			spans = append(spans, span)
		}
	}
	return spans
}

func (d *Diagram) eventEdgeSpans() []source.Span {
	spans := make([]source.Span, len(d.eventmodeling.Relations))
	for i, edge := range d.eventmodeling.Relations {
		spans[i] = d.eventmodeling.Frames[edge.Target].StatementSpan
	}
	return spans
}

func (d *Diagram) gitEdgeSpans() []source.Span {
	commits := slices.Clone(d.gitgraph.Commits)
	slices.SortStableFunc(commits, func(a, b gitmodel.Commit) int { return cmp.Compare(a.Seq, b.Seq) })
	var spans []source.Span
	for _, commit := range commits {
		for range commit.Parents {
			spans = append(spans, commit.Span)
		}
		if commit.Pick != "" {
			spans = append(spans, commit.Span)
		}
	}
	return spans
}

func (d *Diagram) sequenceEdgeSpans() []source.Span {
	var spans []source.Span
	for _, event := range d.sequence.Events {
		if message, ok := event.(*sequencemodel.Message); ok {
			spans = append(spans, message.Span)
		}
	}
	return spans
}
