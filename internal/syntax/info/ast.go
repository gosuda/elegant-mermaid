package info

import (
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax/langium"
)

type Token = langium.Token

type Value struct {
	Text string
	Span source.Span
}

type Info struct {
	Span     source.Span
	Header   Token
	ShowInfo *Token
	Title    *Value
	AccTitle *Value
	AccDescr *Value
}
