package timeline

import "github.com/gosuda/elegant-mermaid/internal/source"

const NoSection = -1

type Event struct {
	Text  string
	Label string
	Span  source.Span
}

type Period struct {
	Text        string
	Label       string
	Section     int
	SectionName string
	Events      []Event
	Span        source.Span
}

type Section struct {
	Name  string
	Label string
	Span  source.Span
}

type Model struct {
	AccTitle   string
	AccDescr   string
	Title      string
	TitleLabel string
	Direction  string
	Sections   []Section
	Periods    []Period
}

func (m *Model) Vertical() bool { return m.Direction == "TD" }
