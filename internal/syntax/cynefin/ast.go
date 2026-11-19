package cynefin

import (
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax/langium"
)

type Token = langium.Token

type Value struct {
	Text string
	Span source.Span
}

type DomainItem struct {
	Span  source.Span
	Label Value
}

type DomainBlock struct {
	Span   source.Span
	Domain Token
	Items  []DomainItem
}

type Transition struct {
	Span  source.Span
	From  Token
	To    Token
	Label *Value
}

type Cynefin struct {
	Span        source.Span
	Header      Token
	Domains     []DomainBlock
	Transitions []Transition
	Title       *Value
	AccTitle    *Value
	AccDescr    *Value
}
