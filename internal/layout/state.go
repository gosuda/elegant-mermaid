package layout

import (
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	statemodel "github.com/gosuda/elegant-mermaid/internal/model/state"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

type stateNames struct{ used map[string]struct{} }

func newStateNames(m *statemodel.Model) *stateNames {
	names := &stateNames{used: make(map[string]struct{}, len(m.States))}
	for _, s := range m.States {
		names.used[s.ID] = struct{}{}
	}
	return names
}

func (n *stateNames) claim(preferred string) string {
	candidate := preferred
	for suffix := 1; ; suffix++ {
		if _, taken := n.used[candidate]; !taken {
			n.used[candidate] = struct{}{}
			return candidate
		}
		candidate = preferred + "." + strconv.Itoa(suffix)
	}
}

type stateBuilder struct {
	model   *statemodel.Model
	in      *Input
	regions []string
	names   *stateNames
}

func FromState(m *statemodel.Model, profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic) {
	direction, _ := scene.ParseDirection(m.Scopes[0].Direction)
	in := Input{Kind: "state", Profile: profile, Direction: direction, Options: resolveOptions(options)}
	b := &stateBuilder{model: m, in: &in, names: newStateNames(m)}
	for _, region := range m.Regions {
		b.regions = append(b.regions, b.names.claim(region.ID))
	}
	stateGroups := make([]int, len(m.States))
	for i := range m.States {
		if err := b.appendState(&m.States[i]); err != nil {
			return Input{}, []diag.Diagnostic{{Code: "layout/state-domain", Severity: diag.SeverityError, Message: err.Error()}}
		}
		stateGroups[i] = -1
		if m.States[i].Composite != statemodel.None {
			stateGroups[i] = len(in.Groups) - 1
		}
	}
	regionGroups := b.appendRegions()
	for _, c := range m.Composites {
		if len(c.Regions) == 0 {
			continue
		}
		set := layered.RegionSet{Parent: stateGroups[c.State]}
		for _, r := range c.Regions {
			set.Regions = append(set.Regions, regionGroups[r])
		}
		in.RegionSets = append(in.RegionSets, set)
	}
	b.appendNotes()
	b.appendTransitions()
	return in, nil
}

func (b *stateBuilder) parentID(parent statemodel.Parent) string {
	switch parent.Kind {
	case statemodel.ParentState:
		return b.model.States[parent.Index].ID
	case statemodel.ParentRegion:
		return b.regions[parent.Index]
	}
	return ""
}

func (b *stateBuilder) stateScope(state *statemodel.State) (*statemodel.Composite, statemodel.Scope) {
	if state.Composite == statemodel.None {
		return nil, b.model.Scopes[state.Scope]
	}
	composite := &b.model.Composites[state.Composite]
	return composite, b.model.Scopes[composite.Scope]
}

func stateBoxText(state *statemodel.State, composite *statemodel.Composite, shape stateShapeRule) string {
	switch {
	case composite != nil && len(state.Descriptions) > 0:
		return state.Descriptions[0].Value
	case composite != nil:
		return state.ID
	case shape.name == "roundedRect":
		return stateText(state)
	}
	return ""
}

func (b *stateBuilder) appendState(state *statemodel.State) error {
	in := b.in
	composite, scope := b.stateScope(state)
	direction := ""
	if scope.DirectionSpan != nil {
		direction = scope.Direction
	}
	shape, size, err := stateShape(state, in.Profile, scope.Direction)
	if err != nil {
		return err
	}
	box := Box{ID: state.ID, Role: scene.RoleNode, Shape: shape.name, Parent: b.parentID(state.Parent), Exclusive: composite == nil, Text: stateBoxText(state, composite, shape), Direction: direction}
	exact := shape.exact
	if composite != nil {
		box.Role, box.Shape, exact, size = scene.RoleGroup, "", false, geom.Size{}
	}
	in.Boxes = append(in.Boxes, box)
	in.Sizes = append(in.Sizes, size)
	in.Exact = append(in.Exact, exact)
	if composite != nil {
		span := source.Span{}
		if scope.DirectionSpan != nil {
			span = *scope.DirectionSpan
		}
		in.Groups = append(in.Groups, Group{ID: state.ID, DirectionSpan: span})
	}
	return nil
}

func stateText(state *statemodel.State) string {
	if len(state.Descriptions) == 0 {
		return state.ID
	}
	rows := make([]string, len(state.Descriptions))
	for i, row := range state.Descriptions {
		rows[i] = row.Value
	}
	return strings.Join(rows, "\n")
}

type stateShapeRule struct {
	name  string
	exact bool
}

func stateShape(state *statemodel.State, profile scene.Profile, direction string) (stateShapeRule, geom.Size, error) {
	switch state.Kind {
	case statemodel.KindFork, statemodel.KindJoin:
		return forkShape(profile, direction)
	case statemodel.KindChoice:
		return squareShape(profile, "choice", "choice_size")
	}
	if len(state.Occurrences) > 0 {
		switch state.Occurrences[len(state.Occurrences)-1].Role {
		case statemodel.RoleStart:
			return squareShape(profile, "sm-circ", "start_size")
		case statemodel.RoleEnd:
			return squareShape(profile, "fr-circ", "end_size")
		}
	}
	return stateShapeRule{name: "roundedRect"}, geom.Size{}, nil
}

func forkShape(profile scene.Profile, direction string) (stateShapeRule, geom.Size, error) {
	length, ok := layoutConstant(profile, "state.fork_length")
	if !ok {
		return stateShapeRule{}, geom.Size{}, errStateDomain
	}
	thickness, ok := layoutConstant(profile, "state.fork_thickness")
	if !ok {
		return stateShapeRule{}, geom.Size{}, errStateDomain
	}
	d, _ := scene.ParseDirection(direction)
	size := geom.Size{W: length, H: thickness}
	if d == scene.DirectionLR || d == scene.DirectionRL {
		size = geom.Size{W: thickness, H: length}
	}
	return stateShapeRule{name: "fork", exact: true}, size, nil
}

func squareShape(profile scene.Profile, name, constant string) (stateShapeRule, geom.Size, error) {
	side, ok := layoutConstant(profile, "state."+constant)
	if !ok {
		return stateShapeRule{}, geom.Size{}, errStateDomain
	}
	return stateShapeRule{name: name, exact: true}, geom.Size{W: side, H: side}, nil
}

func (b *stateBuilder) appendRegions() []int {
	groups := make([]int, 0, len(b.model.Regions))
	for i, region := range b.model.Regions {
		parent := b.model.States[b.model.Composites[region.Parent].State].ID
		id := b.regions[i]
		b.in.Boxes = append(b.in.Boxes, Box{ID: id, Role: scene.RoleGroup, Parent: parent})
		b.in.Sizes = append(b.in.Sizes, geom.Size{})
		b.in.Exact = append(b.in.Exact, false)
		groups = append(groups, len(b.in.Groups))
		b.in.Groups = append(b.in.Groups, Group{ID: id})
	}
	return groups
}

func (b *stateBuilder) appendNotes() {
	m, in := b.model, b.in
	for target := range m.States {
		state := &m.States[target]
		if state.Note == statemodel.None {
			continue
		}
		note := m.Notes[state.Note]
		id := b.names.claim(state.ID + ".note")
		noteIndex := len(in.Boxes)
		side, direction := layered.AttachLeft, "left"
		if note.Position == "right of" {
			side, direction = layered.AttachRight, "right"
		}
		in.Boxes = append(in.Boxes, Box{ID: id, Role: scene.RoleNode, Shape: "note", Parent: in.Boxes[target].Parent, Exclusive: true, Text: note.Text.Value, Direction: direction})
		in.Sizes = append(in.Sizes, geom.Size{})
		in.Exact = append(in.Exact, false)
		in.Attachments = append(in.Attachments, layered.Attachment{Target: target, Note: noteIndex, Side: side})
	}
}

func (b *stateBuilder) appendTransitions() {
	m, in := b.model, b.in
	for i, t := range m.Transitions {
		id := b.names.claim("e" + strconv.Itoa(i))
		length := 1
		if t.Label != nil && t.Label.Value != "" {
			in.Labels = append(in.Labels, Label{ID: b.names.claim(id + ".label"), Owner: id, Role: scene.TextRoleLabel, Text: t.Label.Value})
			length = 2
		}
		in.Routes = append(in.Routes, Route{ID: id, From: m.States[t.From.State].ID, To: m.States[t.To.State].ID, Orthogonal: true, MarkerStart: "none", MarkerEnd: "point", Line: "normal", MinLength: length})
	}
}
