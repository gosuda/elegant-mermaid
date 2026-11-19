package chart

import (
	"slices"
	"strconv"

	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const (
	wardleyPlotID    = "plot"
	wardleyBoxID     = "ab"
	wardleyAxisX     = "Evolution"
	wardleyAxisY     = "Visibility"
	wardleyTitleID   = "title"
	wardleyAxisXID   = "x.title"
	wardleyAxisYID   = "y.title"
	markerPoint      = "point"
	markerNone       = "none"
	strokeDashed     = "dashed"
	strokeDotted     = "dotted"
	wardleyFullScale = 100000
)

type WardleyStrategy uint8

const (
	WardleyNoStrategy WardleyStrategy = iota
	WardleyBuild
	WardleyBuy
	WardleyOutsource
	WardleyMarket
)

type WardleyFlow uint8

const (
	WardleyNoFlow WardleyFlow = iota
	WardleyForward
	WardleyBackward
	WardleyBidirectional
)

type WardleyNode struct {
	Label          string
	X, Y           int64
	Anchor         bool
	Inertia        bool
	PipelineParent bool
	HasOffset      bool
	OffsetX        int64
	OffsetY        int64
	Strategy       WardleyStrategy
}

type WardleyLink struct {
	From, To int
	Dashed   bool
	Label    string
	Flow     WardleyFlow
}

type WardleyPipeline struct {
	Parent   int
	Children []int
}

type WardleyTrend struct {
	Node             int
	TargetX, TargetY int64
}

type WardleyNote struct {
	Text string
	X, Y int64
}

type WardleyForce struct {
	Name string
	X, Y int64
}

type WardleyAnnotation struct {
	Number int64
	X, Y   int64
	Text   string
}

type WardleyPoint struct{ X, Y int64 }

type Wardley struct {
	Title          string
	Stages         []string
	Boundaries     []int64
	Nodes          []WardleyNode
	Pipelines      []WardleyPipeline
	Links          []WardleyLink
	Trends         []WardleyTrend
	Notes          []WardleyNote
	Accelerators   []WardleyForce
	Deaccelerators []WardleyForce
	Annotations    []WardleyAnnotation
	Box            *WardleyPoint
}

type WardleySkeleton struct {
	Boxes  []scene.Box
	Routes []scene.Route
	Labels []scene.Label
}

func wardleyID(prefix string, index int) string { return prefix + strconv.Itoa(index) }

func wardleyNodeID(k int) string { return wardleyID("n", k) }

func wardleyPipelineID(k int) string { return wardleyID("pl", k) }

func wardleyGhostID(k int) string { return wardleyID("tg", k) }

func wardleyAcceleratorID(k int) string { return wardleyID("ac", k) }

func wardleyDeacceleratorID(k int) string { return wardleyID("de", k) }

func wardleyAnnotationID(k int) string { return wardleyID("an", k) }

func (w *Wardley) boxLines() []int {
	var shown []int
	for i, a := range w.Annotations {
		if a.Text != "" {
			shown = append(shown, i)
		}
	}
	slices.SortStableFunc(shown, func(a, b int) int {
		return compareInt64(w.Annotations[a].Number, w.Annotations[b].Number)
	})
	return shown
}

func compareInt64(a, b int64) int {
	switch {
	case a < b:
		return -1
	case a > b:
		return 1
	}
	return 0
}

func (w *Wardley) showsBox() bool { return w.Box != nil && len(w.boxLines()) > 0 }

func (w *Wardley) pipelineOf(node int) (int, bool) {
	if w.Nodes[node].PipelineParent {
		return 0, false
	}
	for k, p := range w.Pipelines {
		if slices.Contains(p.Children, node) {
			return k, true
		}
	}
	return 0, false
}

func (w *Wardley) pipelineLinks(k int) [][2]int {
	children := slices.Clone(w.Pipelines[k].Children)
	slices.SortStableFunc(children, func(a, b int) int { return compareInt64(w.Nodes[a].X, w.Nodes[b].X) })
	links := make([][2]int, 0, len(children))
	for i := 0; i+1 < len(children); i++ {
		links = append(links, [2]int{children[i], children[i+1]})
	}
	return links
}

func (w *Wardley) Skeleton() WardleySkeleton {
	return WardleySkeleton{Boxes: w.skeletonBoxes(), Routes: w.skeletonRoutes(), Labels: w.skeletonLabels()}
}

func (w *Wardley) skeletonBoxes() []scene.Box {
	boxes := []scene.Box{{ID: wardleyPlotID, Role: scene.RoleNode}}
	for k := range w.Pipelines {
		boxes = append(boxes, w.plotChild(wardleyPipelineID(k)))
	}
	for k := range w.Nodes {
		parent := wardleyPlotID
		if p, ok := w.pipelineOf(k); ok {
			parent = wardleyPipelineID(p)
		}
		boxes = append(boxes, scene.Box{ID: wardleyNodeID(k), Role: scene.RoleNode, Parent: parent})
	}
	for k := range w.Trends {
		boxes = append(boxes, w.plotChild(wardleyGhostID(k)))
	}
	for k := range w.Accelerators {
		boxes = append(boxes, scene.Box{ID: wardleyAcceleratorID(k), Role: scene.RoleNode})
	}
	for k := range w.Deaccelerators {
		boxes = append(boxes, scene.Box{ID: wardleyDeacceleratorID(k), Role: scene.RoleNode})
	}
	for k := range w.Annotations {
		boxes = append(boxes, w.plotChild(wardleyAnnotationID(k)))
	}
	if w.showsBox() {
		boxes = append(boxes, scene.Box{ID: wardleyBoxID, Role: scene.RoleNode})
	}
	return boxes
}

func (w *Wardley) plotChild(id string) scene.Box {
	return scene.Box{ID: id, Role: scene.RoleNode, Parent: wardleyPlotID}
}

func (w *Wardley) skeletonRoutes() []scene.Route {
	var routes []scene.Route
	for k := range w.Pipelines {
		for j, pair := range w.pipelineLinks(k) {
			routes = append(routes, scene.Route{
				ID: wardleyPipelineID(k) + ".l" + strconv.Itoa(j), From: wardleyNodeID(pair[0]), To: wardleyNodeID(pair[1]),
				MarkerStart: markerNone, MarkerEnd: markerNone, Stroke: strokeDotted,
			})
		}
	}
	for k, l := range w.Links {
		route := scene.Route{ID: wardleyID("l", k), From: wardleyNodeID(l.From), To: wardleyNodeID(l.To), MarkerStart: markerNone, MarkerEnd: markerNone}
		if l.Dashed {
			route.Stroke = strokeDashed
		}
		if l.Flow == WardleyBackward || l.Flow == WardleyBidirectional {
			route.MarkerStart = markerPoint
		}
		if l.Flow == WardleyForward || l.Flow == WardleyBidirectional {
			route.MarkerEnd = markerPoint
		}
		routes = append(routes, route)
	}
	for k, t := range w.Trends {
		routes = append(routes, scene.Route{ID: wardleyID("tr", k), From: wardleyNodeID(t.Node), To: wardleyGhostID(k), MarkerStart: markerNone, MarkerEnd: markerPoint, Stroke: strokeDotted})
	}
	return routes
}

type wardleyKind uint8

const (
	kindTitle wardleyKind = iota
	kindAxisX
	kindAxisY
	kindStage
	kindNode
	kindLink
	kindNote
	kindNumber
	kindAnnotation
	kindAccelerator
	kindDeaccelerator
)

type wardleySpec struct {
	id, owner, text string
	kind            wardleyKind
	index           int
}

func (w *Wardley) skeletonLabels() []scene.Label {
	specs := w.specs()
	labels := make([]scene.Label, len(specs))
	for i, s := range specs {
		labels[i] = scene.Label{ID: s.id, Owner: s.owner, Text: s.text}
	}
	return labels
}

func (w *Wardley) specs() []wardleySpec {
	var specs []wardleySpec
	add := func(kind wardleyKind, index int, id, owner, text string) {
		specs = append(specs, wardleySpec{id: id, owner: owner, text: text, kind: kind, index: index})
	}
	if w.Title != "" {
		add(kindTitle, 0, wardleyTitleID, wardleyPlotID, w.Title)
	}
	add(kindAxisX, 0, wardleyAxisXID, wardleyPlotID, wardleyAxisX)
	add(kindAxisY, 0, wardleyAxisYID, wardleyPlotID, wardleyAxisY)
	for k, s := range w.Stages {
		add(kindStage, k, wardleyID("st", k), wardleyPlotID, s)
	}
	for k, n := range w.Nodes {
		add(kindNode, k, wardleyNodeID(k)+".label", wardleyNodeID(k), n.Label)
	}
	for k, l := range w.Links {
		if l.Label != "" {
			add(kindLink, k, wardleyID("l", k)+".label", wardleyID("l", k), l.Label)
		}
	}
	for k, n := range w.Notes {
		add(kindNote, k, wardleyID("note", k), wardleyPlotID, n.Text)
	}
	for k, a := range w.Annotations {
		add(kindNumber, k, wardleyAnnotationID(k)+".label", wardleyAnnotationID(k), strconv.FormatInt(a.Number, 10))
		add(kindAnnotation, k, wardleyAnnotationID(k)+".text", w.annotationTextOwner(k), annotationDisplay(a))
	}
	for k, f := range w.Accelerators {
		add(kindAccelerator, k, wardleyAcceleratorID(k)+".label", wardleyAcceleratorID(k), f.Name)
	}
	for k, f := range w.Deaccelerators {
		add(kindDeaccelerator, k, wardleyDeacceleratorID(k)+".label", wardleyDeacceleratorID(k), f.Name)
	}
	return specs
}

func (w *Wardley) annotationTextOwner(k int) string {
	if w.showsBox() {
		return wardleyBoxID
	}
	return wardleyAnnotationID(k)
}

func annotationPrefix(number int64) string { return strconv.FormatInt(number, 10) + ". " }

func annotationDisplay(a WardleyAnnotation) string {
	if a.Text == "" {
		return ""
	}
	return annotationPrefix(a.Number) + a.Text
}
