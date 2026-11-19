package gitgraph

import "github.com/gosuda/elegant-mermaid/internal/source"

type Token struct {
	Kind string
	Text string
	Span source.Span
}

type Start struct {
	Span       source.Span
	Header     Token
	Direction  *Token
	Statements []Statement
}

type Statement struct {
	Span source.Span
	Kind StatementKind
}

type StatementKind interface {
	statementKind()
}

type Value struct {
	Text string
	Span source.Span
}

type Order struct {
	Value int64
	Span  source.Span
}

type Commit struct {
	Keyword source.Span
	ID      *Value
	Message *Value
	Tags    []Value
	Type    *Value
}

type Branch struct {
	Keyword source.Span
	Name    Value
	Order   *Order
}

type Merge struct {
	Keyword source.Span
	Branch  Value
	ID      *Value
	Tags    []Value
	Type    *Value
}

type Checkout struct {
	Keyword source.Span
	Switch  bool
	Branch  Value
}

type CherryPicking struct {
	Keyword source.Span
	ID      *Value
	Tags    []Value
	Parent  *Value
}

type Metadata struct {
	Field string
	Value string
}

func (*Commit) statementKind()        {}
func (*Branch) statementKind()        {}
func (*Merge) statementKind()         {}
func (*Checkout) statementKind()      {}
func (*CherryPicking) statementKind() {}
func (*Metadata) statementKind()      {}
