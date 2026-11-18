package kanban

import "github.com/gosuda/elegant-mermaid/internal/source"

type Token struct {
	Kind  string
	Text  string
	Span  source.Span
	Quote Description
}

type Start struct {
	Span     source.Span
	Leading  []Token
	Header   Token
	Document Document
}

type Document struct {
	Span  source.Span
	Items []Item
}

type Item struct {
	Statement Statement
	Stop      Stop
}

type Statement struct {
	Span   source.Span
	Indent *Token
	Node   *Node
	Data   *ShapeData
	Icon   *Token
	Class  *Token
	Blank  *Token
}

type Stop struct {
	Span   source.Span
	Tokens []Token
}

type Description uint8

const (
	DescriptionBare Description = iota
	DescriptionPlain
	DescriptionQuoted
	DescriptionMarkdown
)

type Node struct {
	Span        source.Span
	ID          *Token
	Open        *Token
	Descr       *Token
	Close       *Token
	Description Description
}

type ShapeData struct {
	Span   source.Span
	Tokens []Token
}

func (d ShapeData) Value() string {
	var text []byte
	for _, token := range d.Tokens {
		text = append(text, token.Text...)
	}
	return string(text)
}
