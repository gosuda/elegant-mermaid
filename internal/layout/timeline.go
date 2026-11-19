package layout

import (
	"strconv"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	timelinemodel "github.com/gosuda/elegant-mermaid/internal/model/timeline"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const (
	timelineKind  = "timeline"
	timelineTitle = "title"
	shapeTitle    = "title"
	shapeSection  = "section"
	shapePeriod   = "period"
	shapeEvent    = "event"
	linkStroke    = "dotted"
)

func FromTimeline(m *timelinemodel.Model, profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic) {
	options = resolveOptions(options)
	options.Config = nil
	options.Profile = profile
	in := Input{Kind: timelineKind, Profile: profile, Direction: scene.DirectionLR, Options: options}
	if m.Vertical() {
		in.Direction = scene.DirectionTB
	}
	if m.TitleLabel != "" {
		in.Boxes = append(in.Boxes, timelineBox(timelineTitle, shapeTitle, m.TitleLabel))
	}
	for s, section := range m.Sections {
		in.Boxes = append(in.Boxes, timelineBox("s"+strconv.Itoa(s), shapeSection, section.Label))
	}
	links := 0
	for i, period := range m.Periods {
		head := timelineBox("p"+strconv.Itoa(i), periodShape(period.Section), period.Label)
		in.Boxes = append(in.Boxes, head)
		previous := head.ID
		for k, event := range period.Events {
			next := timelineBox(head.ID+".e"+strconv.Itoa(k), shapeEvent, event.Label)
			in.Boxes = append(in.Boxes, next)
			in.Routes = append(in.Routes, Route{ID: "e" + strconv.Itoa(links), From: previous, To: next.ID, Orthogonal: true, Line: linkStroke})
			links++
			if !m.Vertical() {
				previous = next.ID
			}
		}
	}
	return in, nil
}

func timelineBox(id, shape, text string) Box {
	if id == text {
		id += "~"
	}
	return Box{ID: id, Role: scene.RoleNode, Shape: shape, Exclusive: true, Text: text}
}

func periodShape(section int) string {
	if section == timelinemodel.NoSection {
		return shapePeriod
	}
	return shapePeriod + ":" + strconv.Itoa(section)
}
