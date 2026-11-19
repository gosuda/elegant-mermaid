package architecture

import "github.com/gosuda/elegant-mermaid/internal/source"

type Token struct {
	Kind string
	Text string
	Span source.Span
}

type Value struct {
	Text string
	Span source.Span
}

type Architecture struct {
	Span       source.Span
	Header     Token
	Statements []Statement
}

type Statement struct {
	Span source.Span
	Kind StatementKind
}

type StatementKind interface {
	statementKind()
}

type Group struct {
	Keyword source.Span
	ID      Value
	Icon    *Value
	Title   *Value
	In      *Value
}

type Service struct {
	Keyword  source.Span
	ID       Value
	IconText *Value
	Icon     *Value
	Title    *Value
	In       *Value
}

type Junction struct {
	Keyword source.Span
	ID      Value
	In      *Value
}

type Edge struct {
	LhsID    Value
	LhsGroup *source.Span
	LhsDir   Value
	LhsInto  *source.Span
	Title    *Value
	RhsInto  *source.Span
	RhsDir   Value
	RhsID    Value
	RhsGroup *source.Span
}

type Alignment struct {
	Keyword   source.Span
	Direction Value
	Members   []Value
}

type MetadataItem struct {
	Field string
	Value string
	Span  source.Span
}

type TitleAndAccessibilities struct {
	Items []MetadataItem
}

func (*Group) statementKind()                   {}
func (*Service) statementKind()                 {}
func (*Junction) statementKind()                {}
func (*Edge) statementKind()                    {}
func (*Alignment) statementKind()               {}
func (*TitleAndAccessibilities) statementKind() {}
