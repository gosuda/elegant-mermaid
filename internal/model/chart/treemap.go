package chart

const KindTreemap Kind = "treemap"

type TreemapNode struct {
	Name      string
	ValueText string
	Value     Number
	Index     int
	Children  []*TreemapNode
}

type Treemap struct {
	Roots []*TreemapNode
}
