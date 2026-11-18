package xychart

import "github.com/gosuda/elegant-mermaid/internal/source"

type Token struct {
	Kind string
	Text string
	Span source.Span
}

type Start struct {
	Span     source.Span
	Headers  []Header
	Document Document
}

type Header struct {
	Span        source.Span
	Keyword     Token
	Orientation *Token
}

type Document struct {
	Span       source.Span
	Statements []Statement
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
	Value    string
	Markdown bool
}

type Number struct {
	Span source.Span
	Text string
}

type Title struct {
	Span source.Span
	Text Text
}

type Range struct {
	Span source.Span
	Min  Number
	Max  Number
}

type BandData struct {
	Span       source.Span
	Categories []Text
}

type AxisStatement struct {
	Span  source.Span
	Y     bool
	Title *Text
	Band  *BandData
	Range *Range
}

type DataPoint struct {
	Span   source.Span
	Number Number
	Label  *Text
}

type PlotData struct {
	Span   source.Span
	Points []DataPoint
}

type PlotStatement struct {
	Span  source.Span
	Line  bool
	Title *Text
	Data  PlotData
}

type Accessibility struct {
	Span      source.Span
	Title     bool
	Multiline bool
	Value     Token
}

func (*Title) statementKind()         {}
func (*AxisStatement) statementKind() {}
func (*PlotStatement) statementKind() {}
func (*Accessibility) statementKind() {}
