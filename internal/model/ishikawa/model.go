package ishikawa

import "github.com/gosuda/elegant-mermaid/internal/source"

const NoParent = -1

const MaxDepth = 64

type Node struct {
	Index    int
	Parent   int
	Depth    int
	Children []int
	Label    string
	Span     source.Span
}

type Model struct {
	Nodes              []Node
	AccTitle, AccDescr string
}
