package ishikawa

import "github.com/gosuda/elegant-mermaid/internal/source"

type Token struct {
	Kind string
	Text string
	Span source.Span
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
	Text   *Token
	Blank  *Token
}

type Stop struct {
	Span   source.Span
	Tokens []Token
}
