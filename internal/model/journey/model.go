package journey

import "github.com/gosuda/elegant-mermaid/internal/source"

type Section struct {
	Name  string
	Label string
	Span  source.Span
}

type Task struct {
	Section      string
	SectionLabel string
	SectionSpan  source.Span
	Name         string
	Label        string
	Score        int
	People       []string
	Span         source.Span
	NameSpan     source.Span
	ScoreSpan    source.Span
	ActorSpan    source.Span
	WithoutActor bool
}

type Config struct {
	Width, Height, MarginX          int64
	WidthSet, HeightSet, MarginXSet bool
}

type Model struct {
	HeaderSpan source.Span
	AccTitle   string
	AccDescr   string
	Title      string
	TitleLabel string
	TitleSpan  source.Span
	Sections   []Section
	Tasks      []Task
	Actors     []string
	Config     Config
}
