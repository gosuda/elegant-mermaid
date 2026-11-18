package kanban

import "github.com/gosuda/elegant-mermaid/internal/source"

type NodeType uint8

const (
	TypeDefault NodeType = iota
	TypeRoundedRect
	TypeRect
	TypeCircle
	TypeCloud
	TypeBang
	TypeHexagon
)

const NoParent = -1

type Node struct {
	Index       int
	ID          string
	Level       int
	Label       string
	Width       int64
	Padding     int64
	Type        NodeType
	Parent      int
	ParentID    string
	Ticket      string
	Assigned    string
	Icon        string
	Class       string
	Priority    string
	HasPriority bool
	Anchor      source.Span
	Span        source.Span
}

func (n Node) IsSection() bool { return n.Parent == NoParent }

type Config struct {
	SectionWidth    int64
	SectionWidthSet bool
	Padding         int64
	PaddingSet      bool
	NodePadding     int64
	NodeMaxWidth    int64
}

type Model struct {
	Nodes    []Node
	Sections []int
	Config   Config
}

type Column struct {
	Section int
	Cards   []int
}

func (m *Model) Columns() []Column {
	columns := make([]Column, 0, len(m.Sections))
	for _, s := range m.Sections {
		column := Column{Section: s}
		for i := range m.Nodes {
			if m.Nodes[i].Parent != NoParent && m.Nodes[i].ParentID == m.Nodes[s].ID {
				column.Cards = append(column.Cards, i)
			}
		}
		columns = append(columns, column)
	}
	return columns
}
