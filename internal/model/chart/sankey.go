package chart

const KindSankey Kind = "sankey"

type ValueKind uint8

const (
	ValueFinite ValueKind = iota
	ValueNonFinite
	ValueOverflow
)

type SankeyNode struct {
	ID    string
	Label string
}

type SankeyLink struct {
	Source int
	Target int
	Kind   ValueKind
	Value  Number
}

type Sankey struct {
	Nodes []SankeyNode
	Links []SankeyLink
}
