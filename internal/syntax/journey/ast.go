package journey

import "github.com/gosuda/elegant-mermaid/internal/source"

type Value struct {
	Text string
	Span source.Span
}

type Field struct {
	Raw     Value
	Trimmed Value
}

type Token struct {
	Kind   string
	Text   string
	Span   source.Span
	Value  Value
	Fields []Field
	end    int
}

type Start struct {
	Span     source.Span
	Header   Token
	Document Document
}

type Document struct {
	Span  source.Span
	Lines []Line
}

type Line struct {
	Span      source.Span
	Statement *Statement
}

type Statement struct {
	Span source.Span
	Kind StatementKind
}

type StatementKind interface {
	statementKind()
}

type Title struct {
	Text Value
}

type AccTitle struct {
	Keyword source.Span
	Value   Value
}

type AccDescr struct {
	Keyword source.Span
	Value   Value
}

type AccDescrMultiline struct {
	Open  source.Span
	Close *source.Span
	Value Value
}

type Section struct {
	Text Value
}

type Task struct {
	Name   Value
	Data   Value
	Fields []Field
}

func (*Title) statementKind()             {}
func (*AccTitle) statementKind()          {}
func (*AccDescr) statementKind()          {}
func (*AccDescrMultiline) statementKind() {}
func (*Section) statementKind()           {}
func (*Task) statementKind()              {}
