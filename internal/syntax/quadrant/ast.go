package quadrant

import "github.com/gosuda/elegant-mermaid/internal/source"

type Token struct {
	Kind    string
	Text    string
	Span    source.Span
	Content source.Span
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
	Statement Statement
	Eol       Token
}

type Statement struct {
	Span source.Span
	Kind StatementKind
}

type StatementKind interface {
	statementKind()
}

type Text struct {
	Span     source.Span
	Content  source.Span
	Value    string
	Markdown bool
}

type Title struct {
	Span  source.Span
	Value Token
}

type Accessibility struct {
	Span      source.Span
	Title     bool
	Multiline bool
	Value     Token
}

type AxisDetails struct {
	Span      source.Span
	Y         bool
	First     Text
	Delimiter *Token
	Second    *Text
}

type QuadrantDetails struct {
	Span   source.Span
	Number int
	Text   Text
}

type Style struct {
	Span source.Span
	Text string
}

type StylesOpt struct {
	Span   source.Span
	Styles []Style
}

type IdString struct {
	Span source.Span
	Text string
}

type ClassDefStatement struct {
	Span   source.Span
	Name   IdString
	Styles StylesOpt
}

type Points struct {
	Span   source.Span
	Text   Text
	Class  *Token
	PointX Token
	PointY Token
	Styles *StylesOpt
}

func (*Title) statementKind()             {}
func (*Accessibility) statementKind()     {}
func (*AxisDetails) statementKind()       {}
func (*QuadrantDetails) statementKind()   {}
func (*ClassDefStatement) statementKind() {}
func (*Points) statementKind()            {}
