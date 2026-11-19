package treemap

import "github.com/gosuda/elegant-mermaid/internal/source"

type Token struct {
	Kind string
	Text string
	Span source.Span
}

type Treemap struct {
	Span   source.Span
	Header Token
	Rows   []Statement
}

type Statement interface {
	statement()
}

type TitleAndAccessibilities struct {
	Span   source.Span
	Tokens []Token
}

type TreemapRow struct {
	Span     source.Span
	Indent   *Indentation
	Item     Item
	ClassDef *ClassDef
}

type Indentation struct {
	Span  source.Span
	Width int
}

type Item interface {
	item()
}

type Name struct {
	Span  source.Span
	Value string
}

type ClassSelector struct {
	Span source.Span
	Name string
}

type Section struct {
	Span          source.Span
	Name          Name
	ClassSelector *ClassSelector
}

type MyNumber struct {
	Span    source.Span
	Raw     string
	Literal string
	Valid   bool
}

type Leaf struct {
	Span          source.Span
	Name          Name
	Value         MyNumber
	ClassSelector *ClassSelector
}

type ClassDef struct {
	Span     source.Span
	Name     string
	Style    string
	HasStyle bool
}

func (*TitleAndAccessibilities) statement() {}
func (*TreemapRow) statement()              {}
func (*Section) item()                      {}
func (*Leaf) item()                         {}
