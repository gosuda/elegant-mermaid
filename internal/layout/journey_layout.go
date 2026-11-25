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
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const journeyUnitsPerPx = 64

var errJourneyInput = errors.New("journey layout: malformed input")

func layoutJourney(in Input) (scene.Scene, []diag.Diagnostic, error) {
	graph, err := decodeJourney(in)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	res, err := lanes.Journey(graph, lanes.Params{Profile: in.Profile})
	if err != nil {
		return scene.Scene{}, nil, err
	}
	dump, err := journeyDump(in, res)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	return scene.Scene{Dump: dump, Groups: res.Groups}, nil, nil
}

type journeyMeter struct {
	profile                       scene.Profile
	fontFamily                    string
	taskWidth, columnGap, padding int64
	scoreMin                      int
}

func newJourneyMeter(in Input, graph *lanes.JourneyInput) (journeyMeter, error) {
	var v [5]int64
	for i, name := range [...]string{"journey.task_width", "journey.column_gap", "node_pad_x", "node_border", "journey.score_min"} {
		value, ok := layoutConstant(in.Profile, name)
		if !ok {
			return journeyMeter{}, lanes.ErrConstants
		}
		v[i] = int64(value)
	}
	m := journeyMeter{profile: in.Profile, fontFamily: in.Options.FontFamily, taskWidth: v[0], columnGap: v[1], padding: v[2] + v[3], scoreMin: int(v[4])}
	if in.Profile == scene.ProfileVector {
		if err := m.applyConfig(in.Options.Config, graph); err != nil {
			return journeyMeter{}, err
		}
	}
	return m, nil
}

func (m *journeyMeter) applyConfig(entries []scene.Config, graph *lanes.JourneyInput) error {
	for _, entry := range entries {
		px, err := strconv.ParseInt(entry.Value, 10, 64)
		if err != nil || px < 0 || px*journeyUnitsPerPx > int64(geom.CoordLimit) {
			return geom.ErrOverflow
		}
		units := px * journeyUnitsPerPx
		switch entry.Key {
		case journeyWidthKey:
			graph.TaskWidth = units
		case journeyHeightKey:
			graph.TaskHeight, graph.BandHeight = units, units
		case journeyMarginKey:
			graph.ColumnGap = units
		}
	}
	if graph.TaskWidth > 0 {
		m.taskWidth = graph.TaskWidth
	}
	if graph.ColumnGap > 0 {
		m.columnGap = graph.ColumnGap
	}
	return nil
}

func (m journeyMeter) target(slots int) int32 {
	n := int64(max(slots, 1))
	return int32(max(n*m.taskWidth+(n-1)*m.columnGap-2*m.padding, 1))
}

func (m journeyMeter) text(text string, role scene.TextRole, target int32) (lanes.Text, error) {
	metric, lineHeight := measure.CellMetric(), int32(1)
	if m.profile == scene.ProfileVector {
		measured := journeyRole(role)
		metric, lineHeight = measure.ForRole(measured), measured.LineHeightPx()*journeyUnitsPerPx
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

func journeyRole(role scene.TextRole) measure.Role {
	switch role {
	case scene.TextRoleTitle:
		return measure.RoleTitle
	case scene.TextRoleBody:
		return measure.RoleBody
	}
	return measure.RoleLabel
}

func journeyShapeKind(shape string) string {
	kind, _, _ := strings.Cut(shape, ":")
	if kind == "" {
		return journeyShapeTask
	}
	return kind
}

func journeyScore(shape string, lowest int) (int, error) {
	if shape == "" {
		return lowest, nil
	}
	_, suffix, has := strings.Cut(shape, ":")
	score, err := strconv.Atoi(suffix)
	if !has || err != nil {
		return 0, fmt.Errorf("task shape %q: %w", shape, errJourneyInput)
	}
	return score, nil
}

type journeyDecoder struct {
	meter    journeyMeter
	graph    lanes.JourneyInput
	bandAt   map[string]int
	sections []string
	counts   []int
}

func decodeJourney(in Input) (lanes.JourneyInput, error) {
	graph := lanes.JourneyInput{}
	meter, err := newJourneyMeter(in, &graph)
	if err != nil {
		return lanes.JourneyInput{}, err
	}
	d := &journeyDecoder{meter: meter, graph: graph, bandAt: map[string]int{}}
	for _, box := range in.Boxes {
		if err := d.box(box); err != nil {
			return lanes.JourneyInput{}, err
		}
	}
	return d.graph, d.sectionLabels()
}

func (d *journeyDecoder) box(box Box) error {
	switch journeyShapeKind(box.Shape) {
	case journeyShapeTitle:
		label, err := d.meter.text(box.Text, scene.TextRoleTitle, geom.I32Max)
		d.graph.Title = &lanes.JourneyTitle{ID: box.ID, Label: label}
		return err
	case journeyShapeSection:
		d.bandAt[box.ID] = len(d.sections)
		d.sections = append(d.sections, box.Text)
		d.counts = append(d.counts, 0)
		d.graph.Sections = append(d.graph.Sections, lanes.JourneySection{ID: box.ID})
		return nil
	case journeyShapeTask:
		return d.task(box)
	case journeyShapePeople:
		return d.people(box)
	}
	return fmt.Errorf("box %q has shape %q: %w", box.ID, box.Shape, errJourneyInput)
}

func (d *journeyDecoder) task(box Box) error {
	score, err := journeyScore(box.Shape, d.meter.scoreMin)
	if err != nil {
		return err
	}
	band := lanes.NoBand
	if box.Parent != "" {
		at, known := d.bandAt[box.Parent]
		if !known {
			return fmt.Errorf("task %q: %w", box.ID, errJourneyInput)
		}
		band = at
		d.counts[at]++
	}
	label, err := d.meter.text(box.Text, scene.TextRoleLabel, d.meter.target(1))
	d.graph.Tasks = append(d.graph.Tasks, lanes.JourneyTask{ID: box.ID, Band: band, Score: score, Label: label})
	return err
}

func (d *journeyDecoder) people(box Box) error {
	last := len(d.graph.Tasks) - 1
	if last < 0 || d.graph.Tasks[last].ID != box.Parent {
		return fmt.Errorf("people %q: %w", box.ID, errJourneyInput)
	}
	label, err := d.meter.text(box.Text, scene.TextRoleBody, d.meter.target(1))
	d.graph.Tasks[last].People = &label
	return err
}

func (d *journeyDecoder) sectionLabels() error {
	for s, text := range d.sections {
		label, err := d.meter.text(text, scene.TextRoleLabel, d.meter.target(d.counts[s]))
		if err != nil {
			return err
		}
		d.graph.Sections[s].Label = label
	}
	return nil
}

func journeyDump(in Input, res lanes.JourneyResult) (scene.Dump, error) {
	options := in.Options
	options.Profile, options.Direction = in.Profile, in.Direction
	dump := scene.Dump{Stage: scene.StageLayout, Kind: journeyKind, Options: options, Canvas: res.Canvas}
	section, task := 0, -1
	for _, box := range in.Boxes {
		var rect geom.Rect
		switch journeyShapeKind(box.Shape) {
		case journeyShapeTitle:
			rect = res.Title
		case journeyShapeSection:
			rect, section = res.Frames[section], section+1
		case journeyShapeTask:
			task++
			rect = res.Tasks[task]
		default:
			rect = res.People[task]
		}
		dump.Boxes = append(dump.Boxes, scene.Box{ID: box.ID, Role: box.Role, Rect: rect, Parent: box.Parent, Exclusive: box.Exclusive, Shape: box.Shape, Text: box.Text})
	}
	return dump, nil
}
