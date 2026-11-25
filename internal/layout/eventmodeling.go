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
	model "github.com/gosuda/elegant-mermaid/internal/model/eventmodeling"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const (
	eventmodelingKind = "eventmodeling"
	eventLanePrefix   = "lane"
	eventLaneShape    = "lane:"
	eventDataBreak    = "\n\n"
)

var errEventmodelingInput = errors.New("eventmodeling layout: endpoint is not a frame")

func FromEventmodeling(m *model.Model, profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic) {
	options = resolveOptions(options)
	options.Config = nil
	options.Profile = profile
	in := Input{Kind: eventmodelingKind, Profile: profile, Direction: scene.DirectionLR, Options: options}
	for _, lane := range m.Lanes {
		id := eventLaneID(lane.Index)
		in.Boxes = append(in.Boxes, Box{ID: id, Role: scene.RoleGroup, Shape: eventLaneShape + strconv.Itoa(lane.Index), Text: lane.Label})
		in.Labels = append(in.Labels, Label{ID: id + ".label", Owner: id, Role: scene.TextRoleLabel, Text: lane.Label})
	}
	for _, frame := range m.Frames {
		in.Boxes = append(in.Boxes, Box{ID: frame.Name, Role: scene.RoleNode, Shape: frame.Category.String(), Parent: eventLaneID(frame.Lane), Exclusive: true, Text: eventFrameText(frame)})
	}
	for k, relation := range m.Relations {
		in.Routes = append(in.Routes, Route{ID: "e" + strconv.Itoa(k), From: m.Frames[relation.Source].Name, To: m.Frames[relation.Target].Name, MarkerEnd: "point", Line: "normal"})
	}
	return in, nil
}

func eventLaneID(index int) string { return eventLanePrefix + strconv.Itoa(index) }

func eventFrameText(frame model.Frame) string {
	data := strings.TrimRight(frame.Data, "\n")
	if data == "" {
		return frame.Display
	}
	return frame.Display + eventDataBreak + data
}

type decodedEvents struct {
	graph   lanes.EventModelingInput
	laneAt  map[string]int
	frameAt map[string]int
}

func layoutEventmodeling(in Input) (scene.Scene, []diag.Diagnostic, error) {
	decoded, err := decodeEventmodeling(in)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	res, err := lanes.EventModeling(decoded.graph, lanes.Params{Profile: in.Profile})
	if err != nil {
		return scene.Scene{}, nil, err
	}
	return scene.Scene{Dump: decoded.dump(in, res), Groups: res.Groups}, nil, nil
}

func eventLaneIndex(shape string) int {
	text, found := strings.CutPrefix(shape, eventLaneShape)
	if !found {
		return 0
	}
	index, err := strconv.Atoi(text)
	if err != nil {
		return 0
	}
	return index
}

func decodeEventmodeling(in Input) (decodedEvents, error) {
	wraps, err := lanes.EventModelingWraps(in.Profile)
	if err != nil {
		return decodedEvents{}, err
	}
	d := decodedEvents{laneAt: map[string]int{}, frameAt: map[string]int{}}
	for _, box := range in.Boxes {
		if box.Role == scene.RoleGroup {
			d.laneAt[box.ID] = len(d.graph.Lanes)
			d.graph.Lanes = append(d.graph.Lanes, lanes.EventLane{ID: box.ID, Index: eventLaneIndex(box.Shape)})
			continue
		}
		frame, err := d.frame(in.Profile, box, wraps, in.Options.FontFamily)
		if err != nil {
			return decodedEvents{}, err
		}
		d.frameAt[box.ID] = len(d.graph.Frames)
		d.graph.Frames = append(d.graph.Frames, frame)
	}
	for _, route := range in.Routes {
		from, fromKnown := d.frameAt[route.From]
		to, toKnown := d.frameAt[route.To]
		if !fromKnown || !toKnown {
			return decodedEvents{}, fmt.Errorf("route %q: %w", route.ID, errEventmodelingInput)
		}
		d.graph.Relations = append(d.graph.Relations, lanes.EventRelation{ID: route.ID, From: from, To: to})
	}
	return d, d.labels(in, wraps)
}

func (d *decodedEvents) frame(profile scene.Profile, box Box, wraps lanes.EventWraps, fontFamily string) (lanes.EventFrame, error) {
	lane, known := d.laneAt[box.Parent]
	if !known {
		lane = len(d.graph.Lanes)
		d.laneAt[box.Parent] = lane
		d.graph.Lanes = append(d.graph.Lanes, lanes.EventLane{Index: lane})
	}
	name, data, hasData := strings.Cut(box.Text, eventDataBreak)
	frame := lanes.EventFrame{ID: box.ID, Lane: lane, Category: box.Shape}
	var err error
	if frame.Name, err = measureEventText(profile, name, wraps.Frame, scene.TextRoleLabel, fontFamily); err != nil || !hasData {
		return frame, err
	}
	text, err := measureEventText(profile, strings.ReplaceAll(data, "\n", "<br>"), wraps.Frame, scene.TextRoleBody, fontFamily)
	frame.Data = &text
	return frame, err
}

func (d *decodedEvents) labels(in Input, wraps lanes.EventWraps) error {
	for _, label := range in.Labels {
		lane, known := d.laneAt[label.Owner]
		if !known {
			return fmt.Errorf("label %q: %w", label.ID, errEventmodelingInput)
		}
		text, err := measureEventText(in.Profile, label.Text, wraps.Lane, label.Role, in.Options.FontFamily)
		if err != nil {
			return err
		}
		d.graph.Lanes[lane].Label = &text
	}
	return nil
}

func eventMetric(profile scene.Profile, role scene.TextRole) measure.Metric {
	if profile == scene.ProfileCell {
		return measure.CellMetric()
	}
	if role == scene.TextRoleBody {
		return measure.ForRole(measure.RoleBody)
	}
	return measure.ForRole(measure.RoleLabel)
}

func measureEventText(profile scene.Profile, text string, target int32, role scene.TextRole, fontFamily string) (lanes.Text, error) {
	lineHeight, ok := layoutConstant(profile, "line_h")
	if !ok {
		return lanes.Text{}, lanes.ErrConstants
	}
	lines, err := measure.StyledLines(text, target, eventMetric(profile, role).WithFontFamily(fontFamily))
	if err != nil {
		return lanes.Text{}, geom.ErrOverflow
	}
	var widest int32
	for _, line := range lines {
		widest = max(widest, line.Width)
	}
	return lanes.Text{Lines: lines, W: widest, H: int32(len(lines)) * lineHeight, Role: role}, nil
}

func (d decodedEvents) rect(box Box, res lanes.EventModelingResult) geom.Rect {
	if box.Role == scene.RoleGroup {
		return res.Lanes[d.laneAt[box.ID]]
	}
	return res.Frames[d.frameAt[box.ID]]
}

func (d decodedEvents) dump(in Input, res lanes.EventModelingResult) scene.Dump {
	options := in.Options
	options.Profile, options.Direction = in.Profile, in.Direction
	dump := scene.Dump{Stage: scene.StageLayout, Kind: eventmodelingKind, Options: options, Canvas: res.Canvas}
	for _, box := range in.Boxes {
		dump.Boxes = append(dump.Boxes, scene.Box{ID: box.ID, Role: box.Role, Rect: d.rect(box, res), Parent: box.Parent, Exclusive: box.Exclusive, Shape: box.Shape, Text: box.Text})
	}
	for i, route := range in.Routes {
		dump.Routes = append(dump.Routes, scene.Route{ID: route.ID, From: route.From, To: route.To, Orthogonal: route.Orthogonal, Points: res.Routes[i], MarkerEnd: route.MarkerEnd, Stroke: route.Line})
	}
	for _, label := range in.Labels {
		lane := d.laneAt[label.Owner]
		text := d.graph.Lanes[lane].Label
		lines := make([]string, len(text.Lines))
		for k, line := range text.Lines {
			lines[k] = line.Text
		}
		dump.Labels = append(dump.Labels, scene.Label{ID: label.ID, Owner: label.Owner, Text: label.Text, Rect: res.LaneLabels[lane], Lines: lines})
	}
	return dump
}
