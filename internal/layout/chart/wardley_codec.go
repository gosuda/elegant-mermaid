package chart

import (
	"fmt"
	"slices"
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const (
	tagMap = iota
	tagNode
	tagPipeline
	tagTrend
	tagAccelerator
	tagDeaccelerator
	tagAnnotation
	tagBox
	tagNote
)

const (
	flagAnchor = 1 << iota
	flagInertia
	flagPipelineParent
	flagOffset
)

const (
	nodeFields      = 7
	pipelineHeader  = 3
	trendFields     = 4
	forceFields     = 3
	annotationField = 4
	mapHeader       = 3
)

func zigzag(v int64) int {
	if v < 0 {
		return int(-2*v - 1)
	}
	return int(2 * v)
}

func unzigzag(n int) int64 {
	if n%2 == 1 {
		return -(int64(n) + 1) / 2
	}
	return int64(n) / 2
}

func (w *Wardley) Regions() [][]int {
	sets := [][]int{w.mapRegion()}
	for _, n := range w.Nodes {
		sets = append(sets, nodeRegion(n))
	}
	for _, p := range w.Pipelines {
		set := []int{tagPipeline, p.Parent, len(p.Children)}
		sets = append(sets, append(set, p.Children...))
	}
	for _, t := range w.Trends {
		sets = append(sets, []int{tagTrend, t.Node, int(t.TargetX), int(t.TargetY)})
	}
	for _, f := range w.Accelerators {
		sets = append(sets, []int{tagAccelerator, int(f.X), int(f.Y)})
	}
	for _, f := range w.Deaccelerators {
		sets = append(sets, []int{tagDeaccelerator, int(f.X), int(f.Y)})
	}
	for _, a := range w.Annotations {
		sets = append(sets, []int{tagAnnotation, int(a.Number), int(a.X), int(a.Y)})
	}
	if w.Box != nil {
		sets = append(sets, []int{tagBox, int(w.Box.X), int(w.Box.Y)})
	}
	for _, n := range w.Notes {
		sets = append(sets, []int{tagNote, int(n.X), int(n.Y)})
	}
	return sets
}

func (w *Wardley) mapRegion() []int {
	set := []int{tagMap, len(w.Stages), len(w.Boundaries)}
	for _, b := range w.Boundaries {
		set = append(set, int(b))
	}
	return set
}

func nodeRegion(n WardleyNode) []int {
	flags := 0
	for _, f := range []struct {
		on  bool
		bit int
	}{{n.Anchor, flagAnchor}, {n.Inertia, flagInertia}, {n.PipelineParent, flagPipelineParent}, {n.HasOffset, flagOffset}} {
		if f.on {
			flags |= f.bit
		}
	}
	return []int{tagNode, flags, int(n.Strategy), int(n.X), int(n.Y), zigzag(n.OffsetX), zigzag(n.OffsetY)}
}

type WardleyDump struct {
	Routes  []scene.Route
	Labels  []scene.Label
	Regions [][]int
}

func DecodeWardley(d WardleyDump) (*Wardley, error) {
	w := &Wardley{}
	labels := make(map[string]string, len(d.Labels))
	for _, l := range d.Labels {
		labels[l.ID] = l.Text
	}
	w.Title = labels[wardleyTitleID]
	for _, set := range d.Regions {
		if err := w.decodeRegion(set, labels); err != nil {
			return nil, err
		}
	}
	for _, r := range d.Routes {
		if err := w.decodeRoute(r, labels); err != nil {
			return nil, err
		}
	}
	return w, w.validate()
}

func (w *Wardley) decodeRegion(set []int, labels map[string]string) error {
	if len(set) == 0 {
		return nil
	}
	switch set[0] {
	case tagMap:
		return w.decodeMap(set, labels)
	case tagNode:
		return w.decodeNode(set, labels)
	case tagPipeline:
		return w.decodePipeline(set)
	case tagTrend:
		return w.decodeTrend(set)
	case tagAccelerator, tagDeaccelerator:
		return w.decodeForce(set, labels)
	case tagAnnotation:
		return w.decodeAnnotation(set, labels)
	case tagBox:
		return w.decodeBox(set)
	case tagNote:
		return w.decodeNote(set, labels)
	}
	return fmt.Errorf("wardley region tag %d: %w", set[0], errDomain)
}

func shortRegion(set []int, fields int) error {
	if len(set) < fields {
		return fmt.Errorf("wardley region %d has %d fields, want %d: %w", set[0], len(set), fields, errDomain)
	}
	return nil
}

func (w *Wardley) decodeMap(set []int, labels map[string]string) error {
	if err := shortRegion(set, mapHeader); err != nil {
		return err
	}
	if len(set) != mapHeader+set[2] {
		return fmt.Errorf("wardley map region has %d fields: %w", len(set), errDomain)
	}
	for k := range set[1] {
		w.Stages = append(w.Stages, labels[wardleyID("st", k)])
	}
	for _, b := range set[mapHeader:] {
		w.Boundaries = append(w.Boundaries, int64(b))
	}
	return nil
}

func (w *Wardley) decodeNode(set []int, labels map[string]string) error {
	if err := shortRegion(set, nodeFields); err != nil {
		return err
	}
	if set[2] > int(WardleyMarket) {
		return fmt.Errorf("wardley strategy code %d: %w", set[2], errDomain)
	}
	flags := set[1]
	node := WardleyNode{
		Label: labels[wardleyNodeID(len(w.Nodes))+".label"], X: int64(set[3]), Y: int64(set[4]), Strategy: WardleyStrategy(set[2]),
		Anchor: flags&flagAnchor != 0, Inertia: flags&flagInertia != 0, PipelineParent: flags&flagPipelineParent != 0, HasOffset: flags&flagOffset != 0,
		OffsetX: unzigzag(set[5]), OffsetY: unzigzag(set[6]),
	}
	w.Nodes = append(w.Nodes, node)
	return nil
}

func (w *Wardley) decodePipeline(set []int) error {
	if err := shortRegion(set, pipelineHeader); err != nil {
		return err
	}
	if len(set) != pipelineHeader+set[2] {
		return fmt.Errorf("wardley pipeline region has %d fields: %w", len(set), errDomain)
	}
	w.Pipelines = append(w.Pipelines, WardleyPipeline{Parent: set[1], Children: slices.Clone(set[pipelineHeader:])})
	return nil
}

func (w *Wardley) decodeTrend(set []int) error {
	if err := shortRegion(set, trendFields); err != nil {
		return err
	}
	w.Trends = append(w.Trends, WardleyTrend{Node: set[1], TargetX: int64(set[2]), TargetY: int64(set[3])})
	return nil
}

func (w *Wardley) decodeForce(set []int, labels map[string]string) error {
	if err := shortRegion(set, forceFields); err != nil {
		return err
	}
	if set[0] == tagAccelerator {
		name := labels[wardleyAcceleratorID(len(w.Accelerators))+".label"]
		w.Accelerators = append(w.Accelerators, WardleyForce{Name: name, X: int64(set[1]), Y: int64(set[2])})
		return nil
	}
	name := labels[wardleyDeacceleratorID(len(w.Deaccelerators))+".label"]
	w.Deaccelerators = append(w.Deaccelerators, WardleyForce{Name: name, X: int64(set[1]), Y: int64(set[2])})
	return nil
}

func (w *Wardley) decodeAnnotation(set []int, labels map[string]string) error {
	if err := shortRegion(set, annotationField); err != nil {
		return err
	}
	number := int64(set[1])
	text := strings.TrimPrefix(labels[wardleyAnnotationID(len(w.Annotations))+".text"], annotationPrefix(number))
	w.Annotations = append(w.Annotations, WardleyAnnotation{Number: number, X: int64(set[2]), Y: int64(set[3]), Text: text})
	return nil
}

func (w *Wardley) decodeBox(set []int) error {
	if err := shortRegion(set, forceFields); err != nil {
		return err
	}
	w.Box = &WardleyPoint{X: int64(set[1]), Y: int64(set[2])}
	return nil
}

func (w *Wardley) decodeNote(set []int, labels map[string]string) error {
	if err := shortRegion(set, forceFields); err != nil {
		return err
	}
	text := labels[wardleyID("note", len(w.Notes))]
	w.Notes = append(w.Notes, WardleyNote{Text: text, X: int64(set[1]), Y: int64(set[2])})
	return nil
}

func (w *Wardley) decodeRoute(r scene.Route, labels map[string]string) error {
	rest, ok := strings.CutPrefix(r.ID, "l")
	if !ok {
		return nil
	}
	index, err := strconv.Atoi(rest)
	if err != nil || index != len(w.Links) {
		return fmt.Errorf("wardley route %q is out of order: %w", r.ID, errDomain)
	}
	from, fromOK := nodeIndex(r.From)
	to, toOK := nodeIndex(r.To)
	if !fromOK || !toOK {
		return fmt.Errorf("wardley route %q has endpoints %q and %q: %w", r.ID, r.From, r.To, errDomain)
	}
	link := WardleyLink{From: from, To: to, Dashed: r.Stroke == strokeDashed, Label: labels[r.ID+".label"], Flow: flowOfMarkers(r)}
	w.Links = append(w.Links, link)
	return nil
}

func nodeIndex(id string) (int, bool) {
	rest, ok := strings.CutPrefix(id, "n")
	if !ok {
		return 0, false
	}
	k, err := strconv.Atoi(rest)
	return k, err == nil && k >= 0
}

func flowOfMarkers(r scene.Route) WardleyFlow {
	start, end := r.MarkerStart == markerPoint, r.MarkerEnd == markerPoint
	switch {
	case start && end:
		return WardleyBidirectional
	case start:
		return WardleyBackward
	case end:
		return WardleyForward
	}
	return WardleyNoFlow
}

func (w *Wardley) validate() error {
	count := len(w.Nodes)
	for _, l := range w.Links {
		if l.From >= count || l.To >= count {
			return fmt.Errorf("wardley link endpoint outside %d nodes: %w", count, errDomain)
		}
	}
	for _, t := range w.Trends {
		if t.Node >= count {
			return fmt.Errorf("wardley trend node %d: %w", t.Node, errDomain)
		}
	}
	return w.validatePipelines(count)
}

func (w *Wardley) validatePipelines(count int) error {
	for _, p := range w.Pipelines {
		if p.Parent >= count || len(p.Children) == 0 {
			return fmt.Errorf("wardley pipeline parent %d: %w", p.Parent, errDomain)
		}
		if slices.ContainsFunc(p.Children, func(c int) bool { return c >= count }) {
			return fmt.Errorf("wardley pipeline children outside %d nodes: %w", count, errDomain)
		}
	}
	return nil
}
