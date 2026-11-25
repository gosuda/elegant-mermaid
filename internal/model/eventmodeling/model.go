package eventmodeling

import (
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/eventmodeling"
)

type Category uint8

const (
	CategoryUI Category = iota
	CategoryCommand
	CategoryReadModel
	CategoryEvent
	CategoryProcessor
)

var categoryNames = [...]string{"ui", "command", "readmodel", "event", "processor"}

func (c Category) String() string { return categoryNames[c] }

var categoryOf = map[string]Category{
	"ui": CategoryUI, "cmd": CategoryCommand, "command": CategoryCommand,
	"rmo": CategoryReadModel, "readmodel": CategoryReadModel,
	"evt": CategoryEvent, "event": CategoryEvent,
	"pcr": CategoryProcessor, "processor": CategoryProcessor,
}

type Lane struct {
	Index int
	Label string
}

type Frame struct {
	Name          string
	Reset         bool
	Type          string
	Category      Category
	Identifier    string
	Display       string
	Namespace     string
	Lane          int
	HasData       bool
	Data          string
	DataType      string
	Span          source.Span
	StatementSpan source.Span
	Sources       []Reference
}

type Relation struct {
	Source int
	Target int
}

type Reference struct {
	Source int
	Span   source.Span
}

type Model struct {
	Frames    []Frame
	Lanes     []Lane
	Relations []Relation
}

type laneBand struct {
	first, limit int
	fallback     string
	prefix       string
}

var bands = map[Category]laneBand{
	CategoryUI:        {0, 100, "UI/Automation", "UI/A: "},
	CategoryProcessor: {0, 100, "UI/Automation", "UI/A: "},
	CategoryCommand:   {100, 200, "Command/Read Model", "C/RM: "},
	CategoryReadModel: {100, 200, "Command/Read Model", "C/RM: "},
	CategoryEvent:     {200, 300, "Events", "Stream: "},
}

func Resolve(document *syn.EventModel) (*Model, []diag.Diagnostic) {
	r := &resolver{document: document, model: &Model{}}
	r.frames()
	r.relations()
	slices.SortFunc(r.model.Lanes, func(a, b Lane) int { return a.Index - b.Index })
	return r.model, r.diagnostics
}

type resolver struct {
	document    *syn.EventModel
	model       *Model
	diagnostics []diag.Diagnostic
}

func (r *resolver) frames() {
	first := make(map[string]source.Span, len(r.document.Frames))
	for _, node := range r.document.Frames {
		fields := node.Fields()
		if span, exists := first[fields.Name.Text]; exists {
			d := syn.Diagnostic("eventmodeling/duplicate-frame-id", "frame "+fields.Name.Text+" already exists", fields.Name.Span)
			d.Related = []diag.Related{{Span: span, Message: "first declared here"}}
			r.diagnostics = append(r.diagnostics, d)
		} else {
			first[fields.Name.Text] = fields.Name.Span
		}
		_, reset := node.(*syn.EmResetFrame)
		r.model.Frames = append(r.model.Frames, r.frame(fields, reset))
	}
}

func (r *resolver) frame(fields *syn.FrameFields, reset bool) Frame {
	category := categoryOf[fields.ModelEntityType.Text]
	namespace, display := splitIdentifier(fields.EntityIdentifier.Text)
	frame := Frame{
		Name: fields.Name.Text, Reset: reset, Type: fields.ModelEntityType.Text, Category: category,
		Identifier: fields.EntityIdentifier.Text, Display: display, Namespace: namespace,
		Lane: r.lane(category, namespace), Span: fields.Name.Span, StatementSpan: fields.Span,
	}
	frame.HasData, frame.Data = r.payload(fields)
	if fields.DataType != nil {
		frame.DataType = fields.DataType.Text
	}
	return frame
}

func splitIdentifier(identifier string) (namespace, display string) {
	parts := strings.Split(identifier, ".")
	if len(parts) == 2 {
		return parts[0], parts[1]
	}
	return "", identifier
}

func (r *resolver) lane(category Category, namespace string) int {
	band := bands[category]
	index, label := band.first, band.fallback
	if namespace != "" {
		index, label = r.nextIndex(band)+1, band.prefix+namespace
	}
	if !slices.ContainsFunc(r.model.Lanes, func(l Lane) bool { return l.Index == index }) {
		r.model.Lanes = append(r.model.Lanes, Lane{Index: index, Label: label})
	}
	return index
}

func (r *resolver) nextIndex(band laneBand) int {
	next := band.first
	for _, lane := range r.model.Lanes {
		if lane.Index > band.first && lane.Index < band.limit {
			next = max(next, lane.Index)
		}
	}
	return next
}

func (r *resolver) payload(fields *syn.FrameFields) (bool, string) {
	has, text := false, ""
	if fields.DataInlineValue != nil {
		has, text = true, unwrapPayload(fields.DataInlineValue.Text, "{")
	}
	if fields.DataReference == nil {
		return has, text
	}
	for _, entity := range r.document.DataEntities {
		if entity.Name.Text == fields.DataReference.Text {
			return true, unwrapPayload(normalizeLines(entity.DataBlockValue.Text), "{\n") + "\n"
		}
	}
	return has, text
}

func normalizeLines(text string) string {
	return strings.ReplaceAll(strings.ReplaceAll(text, "\r\n", "\n"), "\r", "\n")
}

func (r *resolver) relations() {
	for target, node := range r.document.Frames {
		sources := node.Fields().SourceFrames
		for _, ref := range sources {
			from := slices.IndexFunc(r.model.Frames, func(frame Frame) bool { return frame.Name == ref.Text })
			r.model.Frames[target].Sources = append(r.model.Frames[target].Sources, Reference{Source: from, Span: ref.Span})
		}
		if len(sources) > 0 {
			r.explicit(target, sources)
			continue
		}
		r.inferred(target)
	}
}

func (r *resolver) explicit(target int, sources []syn.Value) {
	for from, frame := range r.model.Frames {
		named := slices.ContainsFunc(sources, func(v syn.Value) bool { return v.Text == frame.Name })
		if named && from <= target {
			r.model.Relations = append(r.model.Relations, Relation{Source: from, Target: target})
		}
	}
}

func (r *resolver) inferred(target int) {
	frame := r.model.Frames[target]
	if frame.Reset {
		return
	}
	for from := target - 1; from >= 0; from-- {
		if r.model.Frames[from].Lane != frame.Lane {
			r.model.Relations = append(r.model.Relations, Relation{Source: from, Target: target})
			return
		}
	}
}
