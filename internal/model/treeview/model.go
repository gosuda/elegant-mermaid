package treeview

import "github.com/gosuda/elegant-mermaid/internal/source"

const (
	NoParent  = -1
	RootLevel = -1
	RootName  = "/"
	IconNone  = "none"
)

type Node struct {
	Index       int
	Parent      int
	Level       int
	Depth       int
	Children    []int
	Name        string
	Directory   bool
	Icon        string
	Class       string
	Description string
	Span        source.Span
}

type Length struct {
	Thousandths int32
	Set         bool
}

type Config struct {
	RowIndent     Length
	PaddingX      Length
	PaddingY      Length
	LineThickness Length
}

type Model struct {
	Nodes              []Node
	Config             Config
	Title              string
	AccTitle, AccDescr string
}
