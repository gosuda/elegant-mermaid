package radar

import "github.com/gosuda/elegant-mermaid/internal/source"

type Token struct {
	Kind string
	Text string
	Span source.Span
}

type Start struct {
	Span     source.Span
	Header   Token
	Axes     []Axis
	Curves   []Curve
	Options  []Option
	Title    *Text
	AccTitle *Text
	AccDescr *Text
}

type Text struct {
	Value string
	Span  source.Span
}

type Label struct {
	Span  source.Span
	Value Token
}

type Axis struct {
	Span  source.Span
	Name  Token
	Label *Label
}

type Curve struct {
	Span    source.Span
	Name    Token
	Label   *Label
	Entries []Entry
}

type Number struct {
	Span source.Span
	Text string
}

type Entry interface {
	Number() Number
	Reference() (Token, bool)
}

type DetailedEntry struct {
	Span  source.Span
	Axis  Token
	Value Number
}

type NumberEntry struct {
	Value Number
}

type Option struct {
	Span  source.Span
	Name  Token
	Value Token
}

func (e DetailedEntry) Number() Number           { return e.Value }
func (e DetailedEntry) Reference() (Token, bool) { return e.Axis, true }
func (e NumberEntry) Number() Number             { return e.Value }
func (NumberEntry) Reference() (Token, bool)     { return Token{}, false }
