package layered

import (
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func validateAttachments(in Input) error {
	if len(in.Attachments) == 0 {
		return nil
	}
	ids := make(map[string]int, len(in.Boxes))
	for i, b := range in.Boxes {
		ids[b.ID] = i
	}
	if len(ids) != len(in.Boxes) {
		return ErrGraph
	}
	parents, err := attachmentParents(in, ids)
	if err != nil {
		return err
	}
	if err := validateParentChains(parents); err != nil {
		return err
	}
	return validateAttachmentPairs(in)
}

func attachmentParents(in Input, ids map[string]int) ([]int, error) {
	parents := make([]int, len(in.Boxes))
	for i, b := range in.Boxes {
		parents[i] = -1
		if b.Parent == "" {
			continue
		}
		index, ok := ids[b.Parent]
		if !ok || in.Boxes[index].Role != scene.RoleGroup {
			return nil, ErrGraph
		}
		parents[i] = index
	}
	return parents, nil
}

func validateParentChains(parents []int) error {
	for start := range parents {
		depth := 0
		for cursor := start; cursor >= 0; cursor = parents[cursor] {
			depth++
			if depth > 65 {
				return ErrGraph
			}
		}
	}
	return nil
}

func attachmentInRange(a Attachment, n int) bool {
	return a.Target >= 0 && a.Target < n && a.Note >= 0 && a.Note < n
}

func validAttachmentPair(in Input, a Attachment, targets, notes []bool) bool {
	target, note := in.Boxes[a.Target], in.Boxes[a.Note]
	return a.Target != a.Note && !notes[a.Target] && !notes[a.Note] && !targets[a.Note] && target.Parent == note.Parent && note.Role == scene.RoleNode
}

func validateAttachmentPairs(in Input) error {
	targets := make([]bool, len(in.Boxes))
	notes := make([]bool, len(in.Boxes))
	for _, a := range in.Attachments {
		if !attachmentInRange(a, len(in.Boxes)) || !validAttachmentPair(in, a, targets, notes) {
			return ErrGraph
		}
		targets[a.Target] = true
		notes[a.Note] = true
	}
	return nil
}

func retainedMapping(retained []bool) []int {
	mapping := make([]int, len(retained))
	next := 0
	for i, keep := range retained {
		mapping[i] = -1
		if keep {
			mapping[i] = next
			next++
		}
	}
	return mapping
}

func projectAttachments(in Input, retained []bool) ([]Attachment, error) {
	if len(retained) != len(in.Boxes) {
		return nil, ErrGraph
	}
	mapping := retainedMapping(retained)
	var out []Attachment
	for _, a := range in.Attachments {
		if !attachmentInRange(a, len(mapping)) {
			return nil, ErrGraph
		}
		target, note := mapping[a.Target], mapping[a.Note]
		switch {
		case target >= 0 && note >= 0:
			out = append(out, Attachment{Target: target, Note: note, Side: a.Side})
		case target >= 0 || note >= 0:
			return nil, ErrGraph
		}
	}
	return out, nil
}

func retainedBoxes(in, out Input) []bool {
	present := make(map[string]bool, len(out.Boxes))
	for _, b := range out.Boxes {
		present[b.ID] = true
	}
	retained := make([]bool, len(in.Boxes))
	for i, b := range in.Boxes {
		retained[i] = present[b.ID]
	}
	return retained
}

func connectAttachments(g *Graph, in Input) error {
	g.Attachments = slices.Clone(in.Attachments)
	g.semantic = in.Boxes
	for _, a := range in.Attachments {
		tail := attachmentAnchor(g, int32(a.Target))
		head := attachmentAnchor(g, int32(a.Note))
		if tail < 0 || head < 0 {
			return ErrGraph
		}
		appendBorderEdge(g, tail, head)
	}
	return nil
}

func attachmentAnchor(g *Graph, decl int32) int32 {
	for i, n := range g.Nodes {
		if n.Border == BorderNone && n.Decl == decl {
			return int32(i)
		}
	}
	for _, c := range g.Clusters {
		if c.Decl == decl {
			return c.Top
		}
	}
	return -1
}

func semanticAncestors(boxes []scene.Box, id string) []int {
	parent := ""
	for _, b := range boxes {
		if b.ID == id {
			parent = b.Parent
			break
		}
	}
	var out []int
	for range 64 {
		index := slices.IndexFunc(boxes, func(b scene.Box) bool { return b.ID == parent })
		if index < 0 {
			break
		}
		out = append(out, index)
		parent = boxes[index].Parent
	}
	slices.Reverse(out)
	return out
}

func semanticInside(boxes []scene.Box, id, root string) bool {
	for _, index := range semanticAncestors(boxes, id) {
		if boxes[index].ID == root {
			return true
		}
	}
	return false
}
