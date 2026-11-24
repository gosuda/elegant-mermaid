package layout

import (
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	swimlanemodel "github.com/gosuda/elegant-mermaid/internal/model/swimlane"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

// FromSwimlane builds the layered-family input of a swimlane model: the flowchart
// input with kind swimlane and the parent of each group.
func FromSwimlane(m *swimlanemodel.Model, profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic) {
	in, diagnostics := FromFlowchart(m.Flowchart, profile, options)
	in.Kind = "swimlane"
	for i := range in.Groups {
		in.Groups[i].Parent = m.Flowchart.Groups[i].Parent
	}
	return in, diagnostics
}

func layoutSwimlane(in Input) (scene.Scene, []diag.Diagnostic, error) {
	s, budget, _, err := layoutLayered(in)
	var ds []diag.Diagnostic
	if budget {
		ds = append(ds, diag.Diagnostic{Code: "layout/budget-exhausted", Severity: diag.SeverityInfo, Message: "layout stopped at its iteration cap"})
	}
	if err == nil {
		err = pinBands(in, &s)
	}
	return s, ds, err
}

type laneSpacing struct {
	title int64
	clear int64
	slot  int64
	bend  int64
}

func newLaneSpacing(profile scene.Profile) (laneSpacing, error) {
	title, err := laneConstant(profile, "line_h")
	if err != nil {
		return laneSpacing{}, err
	}
	padding, err := laneConstant(profile, "cluster_pad")
	if err != nil {
		return laneSpacing{}, err
	}
	slot, err := laneConstant(profile, "slot")
	if err != nil {
		return laneSpacing{}, err
	}
	bend, err := laneConstant(profile, "rank_gap")
	if err != nil {
		return laneSpacing{}, err
	}
	clear, err := laneAdd(padding, slot)
	if err != nil {
		return laneSpacing{}, err
	}
	return laneSpacing{title: title, clear: clear, slot: slot, bend: bend}, nil
}

func laneConstant(profile scene.Profile, name string) (int64, error) {
	key := profile.String() + "." + name
	for i := range gen.LayoutConst {
		if gen.LayoutConst[i].Name == key {
			return int64(gen.LayoutConst[i].Value), nil
		}
	}
	return 0, geom.ErrDomain
}

func laneNarrow(value int64) (int32, error) {
	if value < int64(geom.I32Min) || value > int64(geom.I32Max) {
		return 0, geom.ErrOverflow
	}
	return int32(value), nil
}

func laneAdd(a, b int64) (int64, error) {
	sum := a + b
	if (b > 0 && sum < a) || (b < 0 && sum > a) {
		return 0, geom.ErrOverflow
	}
	return sum, nil
}

type laneBand struct {
	id        string
	members   []string
	shift     int64
	start     int64
	thickness int64
}

type laneExtent struct {
	lo, hi int64
	any    bool
}

func (e *laneExtent) extend(value int64) {
	if !e.any {
		e.lo, e.hi, e.any = value, value, true
		return
	}
	e.lo, e.hi = min(e.lo, value), max(e.hi, value)
}

func topLevelLanes(in Input) []string {
	var lanes []string
	for i := range in.Groups {
		if in.Groups[i].Parent == "" {
			lanes = append(lanes, in.Groups[i].ID)
		}
	}
	return lanes
}

func laneOf(in Input, id string) (string, bool) {
	current := id
	for range len(in.Boxes) + 1 {
		index := boxIndex(in, current)
		if index < 0 {
			return "", false
		}
		if in.Boxes[index].Parent == "" {
			return current, in.Boxes[index].Role == scene.RoleGroup
		}
		current = in.Boxes[index].Parent
	}
	return "", false
}

func boxIndex(in Input, id string) int {
	for i := range in.Boxes {
		if in.Boxes[i].ID == id {
			return i
		}
	}
	return -1
}

func inLane(in Input, id, lane string) bool {
	found, ok := laneOf(in, id)
	return ok && found == lane
}

func pinBands(in Input, s *scene.Scene) error {
	lanes := topLevelLanes(in)
	if len(lanes) == 0 {
		return nil
	}
	spacing, err := newLaneSpacing(in.Profile)
	if err != nil {
		return err
	}
	axis := crossAxis(in.Direction)
	bands, err := layBands(in, s, axis, spacing, lanes)
	if err != nil {
		return err
	}
	frames := laneFrames(axis, bands, s)
	canvas := s.Canvas
	pin := buildLanePin(axis, bands, s)
	original := originalPoints(s)
	detachGeometry(s)
	if err = applyLanePin(s, &pin, bands); err != nil {
		return err
	}
	if err = routeBetweenBands(s, axis, spacing, bands, original); err != nil {
		return err
	}
	if err = restoreOrigin(s, axis); err != nil {
		return err
	}
	if err = relocateLabels(s, axis, spacing.slot); err != nil {
		return err
	}
	if err = growCanvas(s, canvas, axis); err != nil {
		return err
	}
	return attachLaneEnds(s, axis, frames)
}

func layBands(in Input, s *scene.Scene, axis laneAxis, spacing laneSpacing, lanes []string) ([]laneBand, error) {
	start := firstLaneStart(s, lanes, axis)
	bands := make([]laneBand, 0, len(lanes)+1)
	for _, lane := range lanes {
		band, err := layLane(in, s, axis, spacing, lane, start)
		if err != nil {
			return nil, err
		}
		start += band.thickness
		bands = append(bands, band)
	}
	loose := laneLooseNodes(in)
	if len(loose) == 0 {
		return bands, nil
	}
	band, err := layLooseNodes(in, s, axis, spacing, loose, start)
	if err != nil {
		return nil, err
	}
	return append(bands, band), nil
}

func firstLaneStart(s *scene.Scene, lanes []string, axis laneAxis) int64 {
	var origin laneExtent
	for _, lane := range lanes {
		if index := sceneBoxIndex(s, lane); index >= 0 {
			origin.extend(int64(*axis.start(&s.Boxes[index].Rect)))
		}
	}
	return origin.lo
}

func sceneBoxIndex(s *scene.Scene, id string) int {
	for i := range s.Boxes {
		if s.Boxes[i].ID == id {
			return i
		}
	}
	return -1
}

func layLane(in Input, s *scene.Scene, axis laneAxis, spacing laneSpacing, lane string, start int64) (laneBand, error) {
	band := laneBand{id: lane, start: start}
	for i := range in.Boxes {
		if inLane(in, in.Boxes[i].ID, lane) {
			band.members = append(band.members, in.Boxes[i].ID)
		}
	}
	extent := contentExtent(in, s, &band, axis)
	if !extent.any {
		extent.lo, extent.hi = start, start
	}
	thickness, err := laneAdd(spacing.title, 2*spacing.clear)
	if err != nil {
		return laneBand{}, err
	}
	if band.thickness, err = laneAdd(thickness, extent.hi-extent.lo); err != nil {
		return laneBand{}, err
	}
	shift, err := laneAdd(start, spacing.title)
	if err != nil {
		return laneBand{}, err
	}
	if shift, err = laneAdd(shift, spacing.clear); err != nil {
		return laneBand{}, err
	}
	band.shift = shift - extent.lo
	if _, err = laneAdd(start, band.thickness); err != nil {
		return laneBand{}, err
	}
	return band, nil
}

func laneLooseNodes(in Input) []string {
	var loose []string
	for i := range in.Boxes {
		if in.Boxes[i].Parent == "" && in.Boxes[i].Role == scene.RoleNode {
			loose = append(loose, in.Boxes[i].ID)
		}
	}
	return loose
}

func layLooseNodes(in Input, s *scene.Scene, axis laneAxis, spacing laneSpacing, loose []string, start int64) (laneBand, error) {
	band := laneBand{members: loose, start: start}
	extent := contentExtent(in, s, &band, axis)
	if !extent.any {
		return band, nil
	}
	band.thickness = extent.hi - extent.lo
	shift, err := laneAdd(start, spacing.clear)
	if err != nil {
		return laneBand{}, err
	}
	band.shift = shift - extent.lo
	return band, nil
}

func contentExtent(in Input, s *scene.Scene, band *laneBand, axis laneAxis) laneExtent {
	var extent laneExtent
	for _, member := range band.members {
		if index := sceneBoxIndex(s, member); index >= 0 {
			rect := s.Boxes[index].Rect
			extent.extend(int64(*axis.start(&rect)))
			extent.extend(int64(*axis.start(&rect)) + int64(*axis.length(&rect)))
		}
	}
	for i := range s.Routes {
		route := &s.Routes[i]
		var withinBand bool
		if band.id == "" {
			withinBand = slices.Contains(band.members, route.From) && slices.Contains(band.members, route.To)
		} else {
			withinBand = inLane(in, route.From, band.id) && inLane(in, route.To, band.id)
		}
		if !withinBand {
			continue
		}
		for j := range route.Points {
			extent.extend(int64(*axis.point(&route.Points[j])))
		}
	}
	return extent
}

func restoreOrigin(s *scene.Scene, axis laneAxis) error {
	var lowest laneExtent
	walkGeometry(s, axis, originSink(&lowest))
	if !lowest.any || lowest.lo >= 0 {
		return nil
	}
	return shiftCrossAxis(s, axis, -lowest.lo)
}

func growCanvas(s *scene.Scene, canvas geom.Size, axis laneAxis) error {
	grown, err := laneNarrow(geometryMax(s, axis))
	if err != nil {
		return err
	}
	*axis.size(&canvas) = max(*axis.size(&canvas), grown)
	s.Canvas = canvas
	return nil
}
