package layout

import (
	"errors"
	"fmt"
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/layout/lanes"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	timelinemodel "github.com/gosuda/elegant-mermaid/internal/model/timeline"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const unitsPerPx = 64

var errTimelineInput = errors.New("timeline layout: malformed input")

func layoutTimeline(in Input) (scene.Scene, []diag.Diagnostic, error) {
	graph, err := decodeTimeline(in)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	res, err := lanes.Timeline(graph, lanes.Params{Profile: in.Profile})
	if err != nil {
		return scene.Scene{}, nil, err
	}
	dump, err := timelineDump(in, res)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	return scene.Scene{Dump: dump, Groups: res.Groups}, nil, nil
}

type timelineMeter struct {
	profile                           scene.Profile
	fontFamily                        string
	cardWidth, columnGap, cardPadding int32
}

func newTimelineMeter(profile scene.Profile) (timelineMeter, error) {
	m := timelineMeter{profile: profile}
	for _, row := range []struct {
		name string
		into *int32
	}{{"timeline.card_width", &m.cardWidth}, {"timeline.column_gap", &m.columnGap}, {"timeline.card_padding", &m.cardPadding}} {
		value, ok := layoutConstant(profile, row.name)
		if !ok {
			return timelineMeter{}, lanes.ErrConstants
		}
		*row.into = value
	}
	return m, nil
}

func (m timelineMeter) cardTarget(slots int32) int32 {
	return slots*m.cardWidth + (slots-1)*m.columnGap - 2*m.cardPadding
}

func (m timelineMeter) text(text string, role scene.TextRole, target int32) (lanes.Text, error) {
	metric, lineHeight := measure.CellMetric(), int32(1)
	if m.profile == scene.ProfileVector {
		measured := timelineRole(role)
		metric, lineHeight = measure.ForRole(measured), measured.LineHeightPx()*unitsPerPx
	}
	lines, err := measure.StyledLines(text, target, metric.WithFontFamily(m.fontFamily))
	if err != nil {
		return lanes.Text{}, geom.ErrOverflow
	}
	var widest int32
	for _, line := range lines {
		widest = max(widest, line.Width)
	}
	return lanes.Text{Lines: lines, W: widest, H: max(int32(len(lines)), 1) * lineHeight, Role: role}, nil
}

func timelineRole(role scene.TextRole) measure.Role {
	switch role {
	case scene.TextRoleTitle:
		return measure.RoleTitle
	case scene.TextRoleBody:
		return measure.RoleBody
	}
	return measure.RoleLabel
}

func timelineShapeKind(shape string) string {
	kind, _, _ := strings.Cut(shape, ":")
	if kind == "" {
		return shapePeriod
	}
	return kind
}

func timelineSectionOf(shape string) (int, error) {
	_, suffix, has := strings.Cut(shape, ":")
	if !has {
		return timelinemodel.NoSection, nil
	}
	section, err := strconv.Atoi(suffix)
	if err != nil || section < 0 {
		return 0, fmt.Errorf("box shape %q: %w", shape, errTimelineInput)
	}
	return section, nil
}

type timelineDecoder struct {
	meter    timelineMeter
	graph    lanes.TimelineInput
	links    map[string]string
	sections []string
	counts   []int
}

func decodeTimeline(in Input) (lanes.TimelineInput, error) {
	meter, err := newTimelineMeter(in.Profile)
	if err != nil {
		return lanes.TimelineInput{}, err
	}
	meter.fontFamily = in.Options.FontFamily
	d := &timelineDecoder{meter: meter, graph: lanes.TimelineInput{Direction: in.Direction}, links: make(map[string]string, len(in.Routes))}
	for _, route := range in.Routes {
		d.links[route.To] = route.ID
	}
	for _, box := range in.Boxes {
		if err := d.box(box); err != nil {
			return lanes.TimelineInput{}, err
		}
	}
	return d.graph, d.sectionLabels()
}

func (d *timelineDecoder) box(box Box) error {
	switch timelineShapeKind(box.Shape) {
	case shapeTitle:
		label, err := d.meter.text(box.Text, scene.TextRoleTitle, geom.I32Max)
		d.graph.Title = &lanes.TimelineTitle{ID: box.ID, Label: label}
		return err
	case shapeSection:
		d.sections = append(d.sections, box.Text)
		d.counts = append(d.counts, 0)
		d.graph.Sections = append(d.graph.Sections, lanes.TimelineSection{ID: box.ID})
		return nil
	case shapePeriod:
		return d.period(box)
	case shapeEvent:
		return d.event(box)
	}
	return fmt.Errorf("box %q has shape %q: %w", box.ID, box.Shape, errTimelineInput)
}

func (d *timelineDecoder) period(box Box) error {
	section, err := timelineSectionOf(box.Shape)
	if err != nil {
		return err
	}
	if section != timelinemodel.NoSection {
		if section < 0 || section >= len(d.counts) {
			return fmt.Errorf("box %q: %w", box.ID, errTimelineInput)
		}
		d.counts[section]++
	}
	label, err := d.meter.text(box.Text, scene.TextRoleLabel, d.meter.cardTarget(1))
	d.graph.Periods = append(d.graph.Periods, lanes.TimelinePeriod{ID: box.ID, Section: section, Label: label})
	return err
}

func (d *timelineDecoder) event(box Box) error {
	link, linked := d.links[box.ID]
	if len(d.graph.Periods) == 0 || !linked {
		return fmt.Errorf("event %q: %w", box.ID, errTimelineInput)
	}
	label, err := d.meter.text(box.Text, scene.TextRoleBody, d.meter.cardTarget(1))
	last := &d.graph.Periods[len(d.graph.Periods)-1]
	last.Events = append(last.Events, lanes.TimelineEvent{ID: box.ID, Link: link, Label: label})
	return err
}

func (d *timelineDecoder) sectionLabels() error {
	for s, text := range d.sections {
		slots := int32(1)
		if d.graph.Direction == scene.DirectionLR {
			slots = int32(max(d.counts[s], 1))
		}
		label, err := d.meter.text(text, scene.TextRoleLabel, d.meter.cardTarget(slots))
		if err != nil {
			return err
		}
		d.graph.Sections[s].Label = label
	}
	return nil
}

func timelineDump(in Input, res lanes.TimelineResult) (scene.Dump, error) {
	options := in.Options
	options.Profile, options.Direction = in.Profile, in.Direction
	dump := scene.Dump{Stage: scene.StageLayout, Kind: timelineKind, Options: options, Canvas: res.Canvas}
	section, period, event := 0, -1, 0
	for _, box := range in.Boxes {
		var rect geom.Rect
		switch timelineShapeKind(box.Shape) {
		case shapeTitle:
			rect = res.Title
		case shapeSection:
			rect, section = res.Sections[section], section+1
		case shapePeriod:
			period, event = period+1, 0
			rect = res.Periods[period]
		default:
			rect, event = res.Events[period][event], event+1
		}
		dump.Boxes = append(dump.Boxes, scene.Box{ID: box.ID, Role: box.Role, Rect: rect, Parent: box.Parent, Exclusive: box.Exclusive, Shape: box.Shape, Text: box.Text})
	}
	return dump, appendTimelineRoutes(&dump, in, res)
}

func appendTimelineRoutes(dump *scene.Dump, in Input, res lanes.TimelineResult) error {
	at := 0
	for _, routes := range res.Routes {
		for _, points := range routes {
			if at >= len(in.Routes) {
				return errTimelineInput
			}
			route := in.Routes[at]
			dump.Routes = append(dump.Routes, scene.Route{ID: route.ID, From: route.From, To: route.To, Orthogonal: route.Orthogonal, Points: points, Stroke: route.Line})
			at++
		}
	}
	if at != len(in.Routes) {
		return errTimelineInput
	}
	return nil
}
