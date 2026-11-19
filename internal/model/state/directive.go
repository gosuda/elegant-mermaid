package state

import (
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/interaction"
	"github.com/gosuda/elegant-mermaid/internal/source"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/state"
)

func (r *resolver) directive(statement *syn.Statement, at location) {
	r.model.Directives = append(r.model.Directives, Directive{Span: statement.Span, Scope: at.scope, TokenSpans: directiveTokenSpans(statement)})
	switch node := statement.Node.(type) {
	case *syn.ClassDefStatement:
		r.classDefinition(node)
	case *syn.StyleStatement:
		r.style(statement, node, at)
	case *syn.CSSClassStatement:
		r.cssClass(statement, node, at)
	case *syn.Direction:
		span := node.Span
		r.model.Scopes[at.scope].Direction = node.Value
		r.model.Scopes[at.scope].DirectionSpan = &span
	case *syn.Click:
		r.click(statement, node, at)
	case *syn.Accessibility:
		r.accessibility(node)
	}
}

func (r *resolver) style(statement *syn.Statement, node *syn.StyleStatement, at location) {
	for _, target := range components(node.Targets) {
		index := r.state(stateSeed{id: target.Value, idSpan: target.Span, span: statement.Span, kind: KindDefault}, at)
		r.member(index, at.parent)
		r.model.States[index].Styles = styles(node.Styles)
	}
}

func (r *resolver) cssClass(statement *syn.Statement, node *syn.CSSClassStatement, at location) {
	for _, target := range components(node.Targets) {
		index := r.state(stateSeed{id: target.Value, idSpan: target.Span, span: statement.Span, kind: KindDefault}, at)
		r.member(index, at.parent)
		r.model.States[index].Classes = append(r.model.States[index].Classes, text(node.Class))
	}
}

func (r *resolver) click(statement *syn.Statement, node *syn.Click, at location) {
	if _, ok := interaction.SafeURL(node.URL.Text); !ok {
		r.interaction = append(r.interaction, diag.Diagnostic{
			Code:     "interaction/unsafe-url",
			Severity: diag.SeverityWarning,
			Message:  "link URL is not allowed",
			Span:     node.URL.Span,
			Help:     "Use an http, https, or mailto link.",
		})
	}
	name := strings.TrimSpace(node.Target.ID.Text)
	link := Link{
		Target:     name,
		TargetSpan: node.Target.Span,
		URL:        Text{Value: node.URL.Text, Span: node.URL.Span},
		Span:       statement.Span,
		Scope:      at.scope,
	}
	if node.Tooltip != nil {
		link.Tooltip = &Text{Value: node.Tooltip.Text, Span: node.Tooltip.Span}
	}
	if index, ok := r.links[name]; ok {
		r.model.Links[index] = link
		return
	}
	r.links[name] = len(r.model.Links)
	r.model.Links = append(r.model.Links, link)
}

func (r *resolver) accessibility(node *syn.Accessibility) {
	value := text(node.Value)
	if node.Title {
		r.model.AccTitle = &value
		return
	}
	r.model.AccDescr = &value
}

func (r *resolver) classDefinition(node *syn.ClassDefStatement) {
	id := strings.TrimSpace(node.ID.Text)
	index, ok := r.classes[id]
	if !ok {
		index = len(r.model.ClassDefinitions)
		r.classes[id] = index
		r.model.ClassDefinitions = append(r.model.ClassDefinitions, ClassDefinition{ID: id, IDSpan: node.ID.Span, Span: node.Span})
	}
	definition := &r.model.ClassDefinitions[index]
	for _, component := range styles(node.Styles) {
		if strings.Contains(component.Value, "color") {
			value := strings.Replace(strings.Replace(component.Value, "fill", "bgFill", 1), "color", "fill", 1)
			definition.TextStyles = append(definition.TextStyles, Text{Value: value, Span: component.Span})
		}
		definition.Styles = append(definition.Styles, component)
	}
}

func directiveTokenSpans(statement *syn.Statement) []source.Span {
	switch node := statement.Node.(type) {
	case *syn.ClassDefStatement:
		return []source.Span{node.ID.Span, node.Styles.Span}
	case *syn.StyleStatement:
		return []source.Span{node.Targets.Span, node.Styles.Span}
	case *syn.CSSClassStatement:
		return []source.Span{node.Targets.Span, node.Class.Span}
	case *syn.Direction:
		return []source.Span{node.Span}
	case *syn.Click:
		return clickTokenSpans(node)
	case *syn.Accessibility:
		return []source.Span{node.Value.Span}
	case *syn.Scale:
		return []source.Span{node.Value.Span}
	case *syn.FloatingNote:
		return []source.Span{node.Text.Span, node.ID.Span}
	}
	return nil
}

func clickTokenSpans(node *syn.Click) []source.Span {
	spans := []source.Span{node.Target.Span, node.Target.ID.Span, node.URL.Span}
	if node.Target.CSSClass != nil {
		spans = append(spans, node.Target.CSSClass.Span)
	}
	if node.Tooltip != nil {
		spans = append(spans, node.Tooltip.Span)
	}
	return spans
}

func text(token syn.Token) Text {
	return Text{Value: strings.TrimSpace(token.Text), Span: token.Span}
}

func components(token syn.Token) []Text {
	parts := strings.Split(token.Text, ",")
	out := make([]Text, 0, len(parts))
	offset := token.Span.Start
	for _, part := range parts {
		out = append(out, Text{Value: strings.TrimSpace(part), Span: source.Span{Start: offset, End: offset + len(part)}})
		offset += len(part) + 1
	}
	return out
}

func styles(token syn.Token) []Text {
	out := components(token)
	for i := range out {
		out[i].Value = strings.TrimSpace(strings.ReplaceAll(out[i].Value, ";", ""))
	}
	return out
}
