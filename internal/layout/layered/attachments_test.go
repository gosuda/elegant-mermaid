package layered

import (
	"fmt"
	"slices"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/stretchr/testify/require"
)

func TestAttachmentFootprintSides(t *testing.T) {
	notes := []attachmentNoteSize{{size: geom.Size{W: 4, H: 8}, side: AttachLeft}, {size: geom.Size{W: 5, H: 2}, side: AttachRight}}
	tb, err := attachmentFootprintOf(footprintInput{target: geom.Size{W: 10, H: 6}, notes: notes, direction: scene.DirectionTB, gap: 3})
	require.NoError(t, err)
	require.Equal(t, geom.Size{W: 31, H: 14}, tb.size)
	require.Equal(t, geom.Rect{X: 10, Y: 4, W: 10, H: 6}, tb.target)
	require.Equal(t, []geom.Rect{{X: 3, Y: 3, W: 4, H: 8}, {X: 23, Y: 6, W: 5, H: 2}}, tb.notes)
	lr, err := attachmentFootprintOf(footprintInput{target: geom.Size{W: 10, H: 6}, notes: notes, direction: scene.DirectionLR, gap: 3})
	require.NoError(t, err)
	require.Equal(t, geom.Size{W: 16, H: 28}, lr.size)
	require.Equal(t, geom.Rect{X: 3, Y: 14, W: 10, H: 6}, lr.target)
}

type attachmentFixture struct{ in Input }

func (f *attachmentFixture) node(id, parent string) int {
	f.in.Boxes = append(f.in.Boxes, scene.Box{ID: id, Role: scene.RoleNode, Parent: parent, Exclusive: true})
	f.in.Text = append(f.in.Text, id)
	f.in.Sizes = append(f.in.Sizes, geom.Size{})
	f.in.Exact = append(f.in.Exact, false)
	return len(f.in.Boxes) - 1
}

func (f *attachmentFixture) group(id, parent string) int {
	index := f.node(id, parent)
	f.in.Boxes[index].Role = scene.RoleGroup
	f.in.Boxes[index].Exclusive = false
	return index
}

func (f *attachmentFixture) edge(from, to, label string) {
	id := fmt.Sprintf("e%d", len(f.in.Routes))
	if label != "" {
		f.in.Labels = append(f.in.Labels, scene.Label{ID: id + ".label", Owner: id, Text: label})
	}
	f.in.Routes = append(f.in.Routes, scene.Route{ID: id, From: from, To: to, Orthogonal: true})
	f.in.Edges = append(f.in.Edges, EdgeOptions{MinLength: 1})
}

func (f *attachmentFixture) attach(target, note int, side AttachmentSide) {
	f.in.Attachments = append(f.in.Attachments, Attachment{Target: target, Note: note, Side: side})
	f.edge(f.in.Boxes[note].ID, f.in.Boxes[target].ID, "")
}

func (f *attachmentFixture) render(t *testing.T, profile scene.Profile, direction scene.Direction) scene.Scene {
	t.Helper()
	f.in.Kind = "state"
	s, err := LayoutFamily(f.in, Options{Scene: scene.Options{Profile: profile, Direction: direction, Thoroughness: 1}})
	require.NoError(t, err)
	require.Len(t, s.Boxes, len(f.in.Boxes))
	require.Len(t, s.Routes, len(f.in.Routes))
	for _, a := range f.in.Attachments {
		target, note := s.Boxes[a.Target].Rect, s.Boxes[a.Note].Rect
		if a.Side == AttachLeft {
			require.LessOrEqual(t, int64(note.X)+int64(note.W), int64(target.X), "left note %v target %v", note, target)
		} else {
			require.LessOrEqual(t, int64(target.X)+int64(target.W), int64(note.X), "right note %v target %v", note, target)
		}
	}
	for _, r := range s.Routes {
		require.GreaterOrEqual(t, len(r.Points), 2, "route %s", r.ID)
	}
	return s
}

var attachmentDirections = []scene.Direction{scene.DirectionTB, scene.DirectionBT, scene.DirectionLR, scene.DirectionRL}

func TestAttachmentsPreserveScreenSidesAndExactLoopTargets(t *testing.T) {
	for _, profile := range []scene.Profile{scene.ProfileCell, scene.ProfileVector} {
		for _, direction := range attachmentDirections {
			f := &attachmentFixture{}
			f.node("unrelated", "")
			f.node("source", "")
			target := f.node("target", "")
			side := int32(896)
			if profile == scene.ProfileCell {
				side = 1
			}
			f.in.Text[target] = ""
			f.in.Sizes[target], f.in.Exact[target] = geom.Size{W: side, H: side}, true
			f.node("exit", "")
			left, right, again := f.node("left", ""), f.node("right", ""), f.node("left_again", "")
			f.attach(target, left, AttachLeft)
			f.attach(target, right, AttachRight)
			f.attach(target, again, AttachLeft)
			f.edge("source", "target", "incoming")
			f.edge("target", "exit", "outgoing")
			f.edge("exit", "target", "back")
			f.edge("target", "target", "first loop")
			f.edge("target", "target", "second loop")
			s := f.render(t, profile, direction)
			rect := s.Boxes[target].Rect
			require.Equal(t, [2]int32{side, side}, [2]int32{rect.W, rect.H})
		}
	}
}

func TestAttachmentsFollowNestedCompositeFrames(t *testing.T) {
	for _, profile := range []scene.Profile{scene.ProfileCell, scene.ProfileVector} {
		for _, direction := range attachmentDirections {
			f := &attachmentFixture{}
			f.node("unrelated", "")
			f.node("outside", "")
			f.group("outer", "")
			target := f.group("composite", "outer")
			f.group("nested", "composite")
			f.in.Boxes[target].Direction = "BT"
			inner := f.node("a", "nested")
			f.node("b", "nested")
			left, right := f.node("left", "outer"), f.node("right", "outer")
			f.attach(target, left, AttachLeft)
			f.attach(target, right, AttachRight)
			f.edge("a", "b", "internal label wider than a title")
			f.edge("b", "b", "internal loop")
			f.edge("outside", "a", "enter")
			f.edge("b", "outside", "leave")
			f.attach(inner, f.node("inner_note", "nested"), AttachRight)
			f.edge("outside", "left", "note entry")
			f.edge("right", "outside", "note exit")
			s := f.render(t, profile, direction)
			require.Positive(t, s.Boxes[target].Rect.W)
		}
	}
}

func TestAttachmentsProjectThroughLocalDirectionIsolation(t *testing.T) {
	f := &attachmentFixture{}
	f.node("unrelated", "")
	local := f.group("local", "")
	f.in.Boxes[local].Direction = "RL"
	f.node("preceding", "local")
	target := f.node("target", "local")
	note := f.node("note", "local")
	f.attach(target, note, AttachLeft)
	f.in.Routes, f.in.Edges = nil, nil
	f.edge("preceding", "target", "")
	f.render(t, scene.ProfileCell, scene.DirectionTB)
}

func TestMalformedAttachmentsAreRejected(t *testing.T) {
	f := &attachmentFixture{}
	target := f.node("target", "")
	note := f.node("note", "")
	f.attach(target, note, AttachLeft)
	f.in.Attachments[0].Note = 99
	require.ErrorIs(t, validateAttachments(f.in), ErrGraph)
	f.in.Attachments[0].Note = note
	f.in.Boxes[note].Parent = "missing"
	require.ErrorIs(t, validateAttachments(f.in), ErrGraph)
	f.in.Boxes[note].Parent = ""
	f.in.Attachments = append(f.in.Attachments, f.in.Attachments[0])
	require.ErrorIs(t, validateAttachments(f.in), ErrGraph)
}

func (f *attachmentFixture) groupIndex(t *testing.T, id string) int {
	t.Helper()
	index := 0
	for _, b := range f.in.Boxes {
		if b.ID == id {
			return index
		}
		if b.Role == scene.RoleGroup {
			index++
		}
	}
	t.Fatalf("missing group %s", id)
	return -1
}

func (f *attachmentFixture) regions(t *testing.T, parent string, regions ...string) {
	set := RegionSet{Parent: f.groupIndex(t, parent)}
	for _, id := range regions {
		set.Regions = append(set.Regions, f.groupIndex(t, id))
	}
	f.in.RegionSets = append(f.in.RegionSets, set)
}

func regionalAttachments(t *testing.T, target string) *attachmentFixture {
	f := &attachmentFixture{}
	for _, pair := range [][2]string{{"prefix", ""}, {"prefix-empty", "prefix"}, {"prefix-live", "prefix"}, {"outer", ""}, {"first", "outer"}, {"second", "outer"}, {"second-empty", "second"}, {"second-live", "second"}, {"last", "outer"}} {
		f.group(pair[0], pair[1])
	}
	for _, pair := range [][2]string{{"prefix-node", "prefix-live"}, {"state", "first"}, {"other", "second-live"}, {"tall", "second-live"}, {"outside", ""}} {
		f.node(pair[0], pair[1])
	}
	f.regions(t, "prefix", "prefix-empty", "prefix-live")
	f.node("internal", "first")
	f.regions(t, "outer", "first", "second", "last")
	f.regions(t, "second", "second-empty", "second-live")
	f.attach(0, f.node("prefix-note", ""), AttachLeft)
	index := slices.IndexFunc(f.in.Boxes, func(b scene.Box) bool { return b.ID == target })
	parent := f.in.Boxes[index].Parent
	f.attach(index, f.node("left", parent), AttachLeft)
	f.attach(index, f.node("right", parent), AttachRight)
	for _, e := range [][3]string{{"prefix-node", "outside", "prefix exit"}, {"outside", "state", "entry"}, {"state", "other", "cross-region"}, {"state", "internal", "internal forward label"}, {"internal", "state", "internal return label"}, {"other", "tall", "unequal sibling content"}, {"tall", "outside", "exit"}, {target, target, "target loop"}} {
		f.edge(e[0], e[1], e[2])
	}
	return f
}

func TestAttachmentsPreserveConcurrentRegions(t *testing.T) {
	for _, profile := range []scene.Profile{scene.ProfileCell, scene.ProfileVector} {
		for _, direction := range attachmentDirections {
			for _, target := range []string{"state"} {
				f := regionalAttachments(t, target)
				s := f.render(t, profile, direction)
				for i, b := range s.Boxes {
					require.Equal(t, [2]string{f.in.Boxes[i].ID, f.in.Boxes[i].Parent}, [2]string{b.ID, b.Parent})
				}
				for _, set := range f.in.RegionSets {
					assertRegionFrames(t, f, s, set)
				}
			}
		}
	}
}

func assertRegionFrames(t *testing.T, f *attachmentFixture, s scene.Scene, set RegionSet) {
	t.Helper()
	groups := groupBoxIDs(f.in)
	var previous *geom.Rect
	for _, region := range set.Regions {
		rect := findSceneBox(s, groups[region])
		require.True(t, rect.W > 0 && rect.H > 0, "region %s frame %v", groups[region], rect)
		if previous != nil {
			vertical := s.Options.Direction == scene.DirectionLR || s.Options.Direction == scene.DirectionRL
			before, after := int64(previous.X)+int64(previous.W), int64(rect.X)
			if vertical {
				before, after = int64(previous.Y)+int64(previous.H), int64(rect.Y)
			}
			require.LessOrEqual(t, before, after, "regions out of order %v %v", *previous, rect)
		}
		previous = &rect
	}
}

func findSceneBox(s scene.Scene, id string) geom.Rect {
	for _, b := range s.Boxes {
		if b.ID == id {
			return b.Rect
		}
	}
	return geom.Rect{}
}
