package chart

const KindVenn Kind = "venn"

type Venn struct {
	Sets     []VennSet
	Overlaps []VennOverlap
	Regions  []VennRegion
}

type VennSet struct {
	Label string
	Size  Number
	Texts []string
}

type VennOverlap struct {
	A, B  int
	Value Number
}

type VennRegion struct {
	Sets  []int
	Label string
	Texts []string
}
