package block

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

type NodeStatement struct {
	Span  source.Span
	First Node
	Size  *Token
	Links []LinkedNode
}

type LinkedNode struct {
	Link Link
	Node Node
}

type Link struct {
	Span  source.Span
	Start *Token
	Label *Token
	End   Token
}

type Node struct {
	Span  source.Span
	ID    Token
	Shape *NodeShapeNLabel
}

type NodeShapeNLabel struct {
	Span  source.Span
	Open  Token
	Label Token
	Close Token
	Dirs  []Token
}

type ColumnsStatement struct {
	Span  source.Span
	Token Token
}

type SpaceStatement struct {
	Span  source.Span
	Token Token
}

type BlockStatement struct {
	Span    source.Span
	Keyword Token
	Header  *NodeStatement
	Body    Document
	End     Token
}

type ClassDefStatement struct {
	Span    source.Span
	Keyword Token
	ID      Token
	Style   Token
}

type CssClassStatement struct {
	Span    source.Span
	Keyword Token
	IDs     Token
	Class   Token
}

type StyleStatement struct {
	Span    source.Span
	Keyword Token
	IDs     Token
	Style   Token
}

func (*NodeStatement) statementKind()     {}
func (*ColumnsStatement) statementKind()  {}
func (*SpaceStatement) statementKind()    {}
func (*BlockStatement) statementKind()    {}
func (*ClassDefStatement) statementKind() {}
func (*CssClassStatement) statementKind() {}
func (*StyleStatement) statementKind()    {}
