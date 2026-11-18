package state

import (
	"fmt"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/source"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/state"
)

type compositeFrame struct {
	state int
	name  string
	span  source.Span
	body  *syn.Document
	at    location
}

func (r *resolver) composite(statement *syn.Statement, node *syn.Composite, at location) {
	r.model.Directives = append(r.model.Directives, Directive{Span: statement.Span, Scope: at.scope, TokenSpans: compositeTokenSpans(node)})
	if node.Description == nil && node.Body == nil {
		return
	}
	trimmed := strings.TrimSpace(node.ID.Text)
	segments := strings.Split(trimmed, ":")
	name := trimmed
	if node.Body == nil {
		name = strings.TrimSpace(segments[0])
	}
	index := r.state(stateSeed{id: name, idSpan: node.ID.Span, span: statement.Span, kind: KindDefault}, at)
	r.member(index, at.parent)
	r.model.States[index].Occurrences = append(r.model.States[index].Occurrences, Occurrence{Span: statement.Span, IDSpan: node.ID.Span, Scope: at.scope, Role: RoleOrdinary})
	if node.Description != nil {
		r.description(index, *node.Description)
	}
	if node.Body == nil {
		r.inlineDescription(index, node.ID, segments)
		return
	}
	r.compositeBody(compositeFrame{state: index, name: name, span: statement.Span, body: node.Body, at: at}, node.Delimiters)
}

func (r *resolver) inlineDescription(state int, id syn.Token, segments []string) {
	if len(segments) < 2 || strings.TrimSpace(segments[1]) == "" {
		return
	}
	value := segments[1]
	start := id.Span.Start + strings.IndexByte(id.Text, ':') + 1
	r.model.States[state].Descriptions = append(r.model.States[state].Descriptions, Text{Value: strings.TrimSpace(value), Span: source.Span{Start: start, End: start + len(value)}})
}

func (r *resolver) compositeBody(frame compositeFrame, delimiters *syn.Delimiters) {
	if r.model.States[frame.state].Composite != None {
		return
	}
	childScope := len(r.model.Scopes)
	r.model.Scopes = append(r.model.Scopes, Scope{ID: frame.name, Parent: frame.at.scope, Direction: "TB"})
	group := len(r.model.Composites)
	bounds := syn.Delimiters{Open: frame.body.Span, Close: frame.body.Span}
	if delimiters != nil {
		bounds = *delimiters
	}
	r.model.Composites = append(r.model.Composites, Composite{State: frame.state, Scope: childScope, Span: frame.span, OpenSpan: bounds.Open, CloseSpan: bounds.Close})
	r.model.States[frame.state].Composite = group
	if !hasRegions(frame.body) {
		r.document(frame.body, location{scope: childScope, parent: Parent{Kind: ParentState, Index: frame.state}})
		return
	}
	r.regions(group, childScope, frame.body, bounds)
}

func (r *resolver) regions(group, scope int, body *syn.Document, bounds syn.Delimiters) {
	region := r.region(group, scope, bounds.Open.End, nil)
	for i := range body.Lines {
		statement := body.Lines[i].Statement
		if statement == nil {
			continue
		}
		if _, ok := statement.Node.(*syn.Concurrent); ok {
			separator := statement.Span
			r.model.Regions[region].Span.End = statement.Span.Start
			region = r.region(group, scope, statement.Span.End, &separator)
			continue
		}
		r.statement(statement, location{scope: scope, parent: Parent{Kind: ParentRegion, Index: region}})
	}
	r.model.Regions[region].Span.End = bounds.Close.Start
}

func (r *resolver) region(group, scope, start int, separator *source.Span) int {
	index := len(r.model.Regions)
	id := fmt.Sprintf("%s_region_%d", r.model.Scopes[scope].ID, r.divider)
	r.divider++
	r.model.Regions = append(r.model.Regions, Region{ID: id, Parent: group, Scope: scope, Span: source.Span{Start: start, End: start}, Separator: separator})
	r.model.Composites[group].Regions = append(r.model.Composites[group].Regions, index)
	return index
}

func hasRegions(body *syn.Document) bool {
	for i := range body.Lines {
		if statement := body.Lines[i].Statement; statement != nil {
			if _, ok := statement.Node.(*syn.Concurrent); ok {
				return true
			}
		}
	}
	return false
}

func compositeTokenSpans(node *syn.Composite) []source.Span {
	spans := []source.Span{node.ID.Span}
	if node.Description != nil {
		spans = append(spans, node.Description.Span)
	}
	if node.Delimiters != nil {
		spans = append(spans, node.Delimiters.Open, node.Delimiters.Close)
	}
	return spans
}
