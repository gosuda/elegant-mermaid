package venn

import "github.com/gosuda/elegant-mermaid/internal/source"

type Token struct {
	Kind string
	Text string
	Span source.Span
}

type Start struct {
	Span     source.Span
	Leading  OptNewlines
	Header   Token
	Document Document
}

type OptNewlines struct {
	Span     source.Span
	Newlines []Token
}

type Document struct {
	Span  source.Span
	Lines []Line
}

type Line struct {
	Span      source.Span
	Newline   *Token
	Statement *Statement
}

type Statement struct {
	Span source.Span
	Kind StatementKind
}

type StatementKind interface {
	statementKind()
}

type Number struct {
	Span source.Span
	Text string
}

type Identifier struct {
	Span source.Span
	Kind string
	Text string
}

type IdentifierList struct {
	Span source.Span
	IDs  []Identifier
}

type Title struct {
	Span  source.Span
	Token Token
}

type Set struct {
	Span    source.Span
	ID      Identifier
	Label   *Token
	Size    *Number
	Keyword Token
}

type Union struct {
	Span    source.Span
	IDs     IdentifierList
	Label   *Token
	Size    *Number
	Keyword Token
}

type Text struct {
	Span    source.Span
	Targets IdentifierList
	ID      Identifier
	Label   *Token
	Keyword Token
}

type IndentedTextTail struct {
	Span  source.Span
	ID    Identifier
	Label *Token
}

type IndentedText struct {
	Span    source.Span
	Tail    IndentedTextTail
	Keyword Token
}

type ValueToken struct {
	Span source.Span
	Kind string
	Text string
}

type ValueTokens struct {
	Span   source.Span
	Tokens []ValueToken
}

type StyleValue struct {
	Span   source.Span
	String *Token
	Tokens *ValueTokens
}

type StyleField struct {
	Span  source.Span
	Key   Token
	Value StyleValue
}

type StylesOpt struct {
	Span   source.Span
	Fields []StyleField
}

type Style struct {
	Span    source.Span
	Targets IdentifierList
	Styles  StylesOpt
	Keyword Token
}

func (*Title) statementKind()        {}
func (*Set) statementKind()          {}
func (*Union) statementKind()        {}
func (*Text) statementKind()         {}
func (*IndentedText) statementKind() {}
func (*Style) statementKind()        {}
