package timeline

import (
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/timeline"
)

const codeEventWithoutPeriod = "timeline/event-without-period"

func Resolve(_ []byte, document *syn.Start) (*Model, []diag.Diagnostic) {
	m := &Model{Direction: "LR"}
	if document.Header.Direction == "TD" {
		m.Direction = "TD"
	}
	var diags []diag.Diagnostic
	for _, line := range document.Document.Lines {
		if line.Statement == nil {
			continue
		}
		if d, bad := m.statement(line.Statement.Kind); bad {
			diags = append(diags, d)
		}
	}
	return m, diags
}

func (m *Model) statement(kind syn.StatementKind) (diag.Diagnostic, bool) {
	switch node := kind.(type) {
	case *syn.Title:
		m.Title = node.Token.Value
		m.TitleLabel = label(m.Title)
	case *syn.AccTitle:
		m.AccTitle = trim(node.Value.Value)
	case *syn.AccDescr:
		m.AccDescr = description(node.Value.Value)
	case *syn.AccDescrBlock:
		m.AccDescr = description(node.Value.Value)
	case *syn.Section:
		m.Sections = append(m.Sections, Section{Name: node.Token.Value, Label: label(node.Token.Value), Span: node.Token.Span})
	case *syn.PeriodStatement:
		m.addPeriod(node.Token)
	case *syn.EventStatement:
		return m.addEvent(node.Token)
	}
	return diag.Diagnostic{}, false
}

func (m *Model) addPeriod(token syn.Token) {
	p := Period{Text: token.Value, Label: label(token.Value), Section: NoSection, Span: token.Span}
	if n := len(m.Sections); n > 0 {
		p.Section, p.SectionName = n-1, m.Sections[n-1].Name
	}
	m.Periods = append(m.Periods, p)
}

func (m *Model) addEvent(token syn.Token) (diag.Diagnostic, bool) {
	if len(m.Periods) == 0 {
		return syn.Diagnostic(codeEventWithoutPeriod, "event has no preceding period", token.Span), true
	}
	last := &m.Periods[len(m.Periods)-1]
	last.Events = append(last.Events, Event{Text: token.Value, Label: label(token.Value), Span: token.Span})
	return diag.Diagnostic{}, false
}

func trim(text string) string { return strings.TrimFunc(text, syn.IsSpace) }

func description(text string) string {
	text = trim(text)
	var out strings.Builder
	for i := 0; i < len(text); {
		c := text[i]
		out.WriteByte(c)
		i++
		if c != '\n' {
			continue
		}
		for i < len(text) {
			r, n := utf8.DecodeRuneInString(text[i:])
			if !syn.IsSpace(r) {
				break
			}
			i += n
		}
	}
	return out.String()
}

func label(text string) string { return syntax.DecodeEntities(trim(text)) }
