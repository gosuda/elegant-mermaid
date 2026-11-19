package wardley

import "github.com/gosuda/elegant-mermaid/internal/source"

type Strategy uint8

const (
	StrategyNone Strategy = iota
	StrategyBuild
	StrategyBuy
	StrategyOutsource
	StrategyMarket
)

func (s Strategy) String() string {
	switch s {
	case StrategyBuild:
		return "build"
	case StrategyBuy:
		return "buy"
	case StrategyOutsource:
		return "outsource"
	case StrategyMarket:
		return "market"
	}
	return ""
}

type Flow uint8

const (
	FlowNone Flow = iota
	FlowForward
	FlowBackward
	FlowBidirectional
)

type Node struct {
	ID             string
	Name           string
	Label          string
	X, Y           int64
	Anchor         bool
	HasOffset      bool
	OffsetX        int64
	OffsetY        int64
	Inertia        bool
	Strategy       Strategy
	PipelineParent bool
	Span           source.Span
}

type Link struct {
	Source string
	Target string
	Dashed bool
	Label  string
	Flow   Flow
	Span   source.Span
}

type Trend struct {
	Node             string
	TargetX, TargetY int64
}

type Pipeline struct {
	Node       string
	Components []string
}

type Annotation struct {
	Number int64
	X, Y   int64
	Text   string
}

type Note struct {
	Text string
	X, Y int64
}

type Force struct {
	Name string
	X, Y int64
}

type Point struct{ X, Y int64 }

type ConfigEntry struct {
	Key   string
	Value int64
}

type Declaration struct {
	Node  int
	Span  source.Span
	Scale uint8
}

type Reference struct {
	Node int
	Name string
	Span source.Span
}

type Model struct {
	Header         source.Span
	Declarations   []Declaration
	References     []Reference
	PipelineUses   []Reference
	AccTitle       string
	AccDescr       string
	Title          string
	Stages         []string
	Boundaries     []int64
	Nodes          []Node
	Links          []Link
	Trends         []Trend
	Pipelines      []Pipeline
	Annotations    []Annotation
	Notes          []Note
	Accelerators   []Force
	Deaccelerators []Force
	Box            *Point
	Config         []ConfigEntry
}

func (m *Model) ReferenceName(r Reference) string {
	if r.Node >= 0 {
		return m.Nodes[r.Node].ID
	}
	return r.Name
}

func (m *Model) NodeIndex(id string) int {
	for i := range m.Nodes {
		if m.Nodes[i].ID == id {
			return i
		}
	}
	return -1
}

func (m *Model) Integer(key string) (int64, bool) {
	for _, e := range m.Config {
		if e.Key == key {
			return e.Value, true
		}
	}
	return 0, false
}
