package treeview

import "github.com/gosuda/elegant-mermaid/internal/source"

type Token struct {
	Kind  string
	Text  string
	Value string
	Span  source.Span
	from  int
	to    int
}

type TreeView struct {
	Span     source.Span
	Header   Token
	Title    *Token
	AccTitle *Token
	AccDescr *Token
	Nodes    []TreeNode
}

type TreeNode struct {
	Span   source.Span
	Indent *Token
	Name   Token
	Class  *Token
	Icon   *Token
	Desc   *Token
}
