package chart

const KindPie Kind = "pie"

type PieSection struct {
	Label string
	Value Number
	Index int
}

type Pie struct {
	ShowData bool
	Sections []PieSection
}
