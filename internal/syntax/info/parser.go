package info

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax/langium"
)

const kindID = "info"

var grammar = langium.Grammar{
	Keywords: []langium.Keyword{{Text: "showInfo", Guard: true}, {Text: "info", Guard: true}},
}

var afterShowInfo = []string{"ACC_DESCR", "ACC_TITLE", "EOF", "TITLE"}

func Parse(src []byte, removed []source.Span) (*Info, []diag.Diagnostic) {
	text := string(src)
	p := &parser{Cursor: langium.NewCursor(kindID, text, removed, grammar)}
	p.SkipNewlines()
	doc := &Info{}
	doc.Header = p.header()
	p.SkipNewlines()
	p.body(doc)
	doc.Span = source.Span{Start: doc.Header.Span.Start, End: len(text)}
	return doc, p.Diags
}

type parser struct {
	*langium.Cursor
	fragment bool
}

func (p *parser) header() Token {
	if p.Kind() == "info" {
		return p.Take()
	}
	p.Unexpected("info")
	p.SkipLine()
	return Token{}
}

func (p *parser) body(doc *Info) {
	for {
		switch kind := p.Kind(); {
		case kind == "EOF":
			return
		case kind == "UNTERMINATED":
			p.Unterminated()
			return
		case kind == "NEWLINE":
			p.Take()
		case kind == "showInfo":
			p.showInfo(doc)
		case langium.IsMetadata(kind):
			p.metadata(doc)
		default:
			p.Unknown()
		}
	}
}

func (p *parser) showInfo(doc *Info) {
	if doc.ShowInfo != nil || p.fragment {
		p.Unexpected(afterShowInfo...)
		p.SkipLine()
		return
	}
	token := p.Take()
	doc.ShowInfo = &token
}

func (p *parser) metadata(doc *Info) {
	p.fragment = true
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
