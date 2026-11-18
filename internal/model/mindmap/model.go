package mindmap

import "github.com/gosuda/elegant-mermaid/internal/source"

type Shape uint8

const (
	ShapeDefault Shape = iota
	ShapeSquare
	ShapeRounded
	ShapeCircle
	ShapeCloud
	ShapeBang
	ShapeHexagon
)

func (s Shape) String() string {
	switch s {
	case ShapeSquare:
		return "rect"
	case ShapeRounded:
		return "rounded"
	case ShapeCircle:
		return "mindmapCircle"
	case ShapeCloud:
		return "cloud"
	case ShapeBang:
		return "bang"
	case ShapeHexagon:
		return "hexagon"
	}
	return "defaultMindmapNode"
}

const NoParent = -1

type Node struct {
	Index       int
	Parent      int
	Level       int
	Children    []int
	SourceID    string
	Description string
	Label       string
	Markdown    bool
	Shape       Shape
	Icon        string
	Class       string
	Span        source.Span
}

type Config struct {
	Padding         int64
	PaddingSet      bool
	MaxNodeWidth    int64
	MaxNodeWidthSet bool
}

type Model struct {
	Nodes              []Node
	Config             Config
	AccTitle, AccDescr string
}
