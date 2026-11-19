package cynefin

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax/langium"
)

const kindID = "cynefin"

var headerKinds = []string{"cynefin-beta", "cynefin-beta:"}

func Parse(src []byte, removed []source.Span) (*Cynefin, []diag.Diagnostic) {
	text := string(src)
	p := &parser{Cursor: langium.NewCursor(kindID, text, removed, grammar)}
	p.SkipNewlines()
	doc := &Cynefin{}
	doc.Header = p.header()
	p.SkipNewlines()
	p.body(doc)
	doc.Span = source.Span{Start: doc.Header.Span.Start, End: len(text)}
	return doc, p.Diags
}

type parser struct {
	*langium.Cursor
}

func (p *parser) header() Token {
	switch p.Kind() {
	case "cynefin-beta", "cynefin-beta:":
		return p.Take()
	}
	p.Unexpected(headerKinds...)
	p.SkipLine()
	return Token{}
}

func (p *parser) body(doc *Cynefin) {
	for {
		switch kind := p.Kind(); {
		case kind == "EOF":
			return
		case kind == "UNTERMINATED":
			p.Unterminated()
			return
		case kind == "NEWLINE":
			p.Take()
		case kind == "DOMAIN_NAME" && p.Ahead(1).Kind == "-->":
			p.transition(doc)
		case kind == "DOMAIN_NAME":
			p.domain(doc)
		case langium.IsMetadata(kind):
			p.metadata(doc)
		default:
			p.Unknown()
		}
	}
}

func (p *parser) domain(doc *Cynefin) {
	block := DomainBlock{Domain: p.Take()}
	end := block.Domain.Span.End
	for {
		p.SkipNewlines()
		if p.Kind() != "STRING" {
			break
		}
		token := p.Take()
		block.Items = append(block.Items, DomainItem{Span: token.Span, Label: Value{Text: token.Text, Span: token.Span}})
		end = token.Span.End
	}
	block.Span = source.Span{Start: block.Domain.Span.Start, End: end}
	doc.Domains = append(doc.Domains, block)
}

func (p *parser) transition(doc *Cynefin) {
	node := Transition{From: p.Take()}
	p.Take()
	if p.Kind() != "DOMAIN_NAME" {
		p.Unexpected("DOMAIN_NAME")
		p.SkipLine()
		return
	}
	node.To = p.Take()
	expected := []string{":"}
	if p.Kind() == ":" {
		p.Take()
		if p.Kind() != "STRING" {
			p.Unexpected("STRING")
			p.SkipLine()
			return
		}
		label := p.Take()
		node.Label = &Value{Text: label.Text, Span: label.Span}
		expected = nil
	}
	if !p.Finish(expected...) {
		return
	}
	node.Span = source.Span{Start: node.From.Span.Start, End: p.End}
	doc.Transitions = append(doc.Transitions, node)
}

func (p *parser) metadata(doc *Cynefin) {
	field, token, ok := p.Metadata()
	if !ok {
		return
	}
	value := &Value{Text: token.Text, Span: token.Span}
	switch field {
	case "accDescr":
		doc.AccDescr = value
	case "accTitle":
		doc.AccTitle = value
	default:
		doc.Title = value
	}
}
