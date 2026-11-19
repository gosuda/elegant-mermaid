package state

import "github.com/gosuda/elegant-mermaid/internal/source"

type Token struct {
	Kind string
	Text string
	Span source.Span
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
	Node StatementNode
}

type StatementNode interface{ statementNode() }

type IDStatement struct {
	Span     source.Span
	ID       Token
	CSSClass *Token
}

type IDDeclaration struct {
	ID          IDStatement
	Description *Token
}

type Transition struct {
	From        IDStatement
	Arrow       Token
	To          IDStatement
	Description *Token
}

type Delimiters struct{ Open, Close source.Span }

type Composite struct {
	ID          Token
	Description *Token
	Body        *Document
	Delimiters  *Delimiters
}

type StereotypeKind uint8

const (
	StereotypeFork StereotypeKind = iota
	StereotypeJoin
	StereotypeChoice
)

type Stereotype struct {
	ID   Token
	Kind StereotypeKind
}

type Concurrent struct{}

type NotePosition struct {
	Span  source.Span
	Value string
}

type Note struct {
	Position NotePosition
	Target   Token
	Text     Token
}

type FloatingNote struct {
	Text Token
	ID   Token
}

type ClassDefStatement struct {
	Span   source.Span
	ID     Token
	Styles Token
}

type StyleStatement struct {
	Span    source.Span
	Targets Token
	Styles  Token
}

type CSSClassStatement struct {
	Span    source.Span
	Targets Token
	Class   Token
}

type Direction struct {
	Span  source.Span
	Value string
}

type Click struct {
	Target  IDStatement
	URL     Token
	Tooltip *Token
}

type Accessibility struct {
	Title bool
	Value Token
}

type Scale struct{ Value Token }

type HideEmpty struct{}

func (*IDDeclaration) statementNode()     {}
func (*Transition) statementNode()        {}
func (*Composite) statementNode()         {}
func (*Stereotype) statementNode()        {}
func (*Concurrent) statementNode()        {}
func (*Note) statementNode()              {}
func (*FloatingNote) statementNode()      {}
func (*ClassDefStatement) statementNode() {}
func (*StyleStatement) statementNode()    {}
func (*CSSClassStatement) statementNode() {}
func (*Direction) statementNode()         {}
func (*Click) statementNode()             {}
func (*Accessibility) statementNode()     {}
func (*Scale) statementNode()             {}
func (*HideEmpty) statementNode()         {}
