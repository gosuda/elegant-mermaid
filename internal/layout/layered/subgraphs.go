package layered

import (
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func fixedGroup(groups []FixedGroup, id string) *FixedGroup {
	for i := range groups {
		if groups[i].ID == id {
			return &groups[i]
		}
	}
	return nil
}

func inputParent(in Input, id string) string {
	for _, b := range in.Boxes {
		if b.ID == id {
			return b.Parent
		}
	}
	return ""
}

func inputInside(in Input, id, group string) bool {
	for fuel := len(in.Boxes) + 1; id != "" && fuel > 0; fuel-- {
		if id == group {
			return true
		}
		id = inputParent(in, id)
	}
	return false
}

func crossingGroup(in Input, id string) bool {
	for _, r := range in.Routes {
		if properEndpoint(in, r.From, id) != properEndpoint(in, r.To, id) {
			return true
		}
	}
	return false
}

func properEndpoint(in Input, id, group string) bool {
	return id != group && inputInside(in, id, group)
}

func prepareSubgraphs(in Input, opts Options) (Input, error) {
	if err := validateRegionSets(in); err != nil {
		return Input{}, err
	}
	prepared := in
	prepared.Boxes = slices.Clone(in.Boxes)
	prepared.Text = slices.Clone(in.Text)
	prepared.Labels = slices.Clone(in.Labels)
	prepared.Routes = slices.Clone(in.Routes)
	prepared.Edges = slices.Clone(in.Edges)
	for _, box := range in.Boxes {
		g := GroupOptions{ID: box.ID, Direction: box.Direction}
		if !directedGroup(in, prepared, box) {
			continue
		}
		if crossingGroup(in, g.ID) {
			recordIgnoredDirection(opts, g.ID)
			continue
		}
		folded, err := foldSubgraph(in, prepared, g, opts)
		if err != nil {
			return Input{}, err
		}
		prepared = folded
	}
	return prepared, nil
}

func directedGroup(in, prepared Input, box scene.Box) bool {
	return box.Role == scene.RoleGroup && box.Direction != "" && hasInputBox(prepared, box.ID) && !regionMember(in, box.ID)
}

func recordIgnoredDirection(opts Options, id string) {
	if opts.IgnoredDirections != nil {
		*opts.IgnoredDirections = append(*opts.IgnoredDirections, id)
	}
}

func foldSubgraph(in, prepared Input, g GroupOptions, opts Options) (Input, error) {
	fixed, err := layoutSubgraph(in, g, opts)
	if err != nil {
		return Input{}, err
	}
	collapsed := collapseSubgraph(prepared, g.ID)
	if collapsed.Attachments, err = projectAttachments(prepared, retainedBoxes(prepared, collapsed)); err != nil {
		return Input{}, err
	}
	if collapsed.RegionSets, err = collapsedRegionSets(prepared, g.ID, collapsed); err != nil {
		return Input{}, err
	}
	collapsed.Fixed = append(collapsed.Fixed, fixed)
	return collapsed, nil
}

func hasInputBox(in Input, id string) bool {
	for _, b := range in.Boxes {
		if b.ID == id {
			return true
		}
	}
	return false
}

func layoutSubgraph(in Input, g GroupOptions, opts Options) (FixedGroup, error) {
	sub := subgraphInput(in, g.ID)
	attachments, err := projectAttachments(in, retainedBoxes(in, sub))
	if err != nil {
		return FixedGroup{}, err
	}
	sub.Attachments = attachments
	if sub.RegionSets, err = subgraphRegionSets(in, sub); err != nil {
		return FixedGroup{}, err
	}
	opts.Scene.Direction, _ = scene.ParseDirection(g.Direction)
	var packing packingReservations
	opts.capturePacking = &packing
	s, err := LayoutFamily(sub, opts)
	if err != nil {
		return FixedGroup{}, err
	}
	stripRegionRoot(&s, g.ID)
	margin := constant(opts.Scene.Profile, "canvas_margin")
	if err := shiftScene(&s, -int64(margin), -int64(margin)); err != nil {
		return FixedGroup{}, err
	}
	s.Canvas.W -= 2 * margin
	s.Canvas.H -= 2 * margin
	return frameSubgraph(in, g.ID, fixedContents{scene: s, packing: packing}, opts.Scene)
}

func subOwner(in Input, id string) bool {
	for _, r := range in.Routes {
		if r.ID == id {
			return true
		}
	}
	return false
}

func collapseSubgraph(in Input, id string) Input {
	out := Input{Kind: in.Kind, Fixed: in.Fixed}
	for i, b := range in.Boxes {
		if b.ID != id && inputInside(in, b.ID, id) {
			continue
		}
		out.Boxes = append(out.Boxes, b)
		out.Text = append(out.Text, inputBoxText(in, i))
		appendBoxSizes(&out, in, i)
	}
	for i, r := range in.Routes {
		if properEndpoint(in, r.From, id) && properEndpoint(in, r.To, id) {
			continue
		}
		appendInputRoute(&out, in, i)
	}
	for _, l := range in.Labels {
		if labelOwnerPresent(out, l.Owner) {
			out.Labels = append(out.Labels, l)
		}
	}
	return out
}

func shiftScene(s *scene.Scene, dx, dy int64) error {
	for i := range s.Boxes {
		b := Box{Rect: s.Boxes[i].Rect}
		if err := translateBox(&b, dx, dy); err != nil {
			return err
		}
		s.Boxes[i].Rect = b.Rect
	}
	for i := range s.Labels {
		b := Box{Rect: s.Labels[i].Rect}
		if err := translateBox(&b, dx, dy); err != nil {
			return err
		}
		s.Labels[i].Rect = b.Rect
	}
	for i := range s.Routes {
		part := Layout{Routes: []EdgeRoute{{Points: s.Routes[i].Points}}}
		if err := translateLayout(&part, dx, dy); err != nil {
			return err
		}
	}
	return nil
}

func inputBoxText(in Input, index int) string {
	for _, label := range in.Labels {
		if label.Owner == in.Boxes[index].ID {
			return label.Text
		}
	}
	if index < len(in.Text) {
		return in.Text[index]
	}
	return in.Boxes[index].ID
}

func appendInputRoute(out *Input, in Input, index int) {
	out.Routes = append(out.Routes, in.Routes[index])
	option := EdgeOptions{}
	if index < len(in.Edges) {
		option = in.Edges[index]
	}
	out.Edges = append(out.Edges, option)
}

func subgraphInput(in Input, id string) Input {
	owns := ownsRegions(in, id)
	sub := Input{Kind: in.Kind}
	for i, b := range in.Boxes {
		member, ok := subgraphMember(in, b, id, owns)
		if !ok {
			continue
		}
		sub.Boxes = append(sub.Boxes, member)
		sub.Text = append(sub.Text, inputBoxText(in, i))
		appendBoxSizes(&sub, in, i)
	}
	subgraphRoutes(&sub, in, id)
	for _, l := range in.Labels {
		if l.Owner != id && labelOwnerPresent(sub, l.Owner) {
			sub.Labels = append(sub.Labels, l)
		}
	}
	return sub
}

func subgraphMember(in Input, b scene.Box, id string, owns bool) (scene.Box, bool) {
	if !inputInside(in, b.ID, id) || b.ID == id && !owns {
		return b, false
	}
	switch {
	case b.ID == id:
		b.Parent, b.Direction = "", ""
	case b.Parent == id && !owns:
		b.Parent = ""
	}
	return b, true
}

func subgraphRoutes(out *Input, in Input, id string) {
	for i, r := range in.Routes {
		if properEndpoint(in, r.From, id) && properEndpoint(in, r.To, id) {
			appendInputRoute(out, in, i)
		}
	}
}

func labelOwnerPresent(in Input, id string) bool { return hasInputBox(in, id) || subOwner(in, id) }
