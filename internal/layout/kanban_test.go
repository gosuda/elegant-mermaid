package layout

import (
	"errors"
	"os"
	"path/filepath"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const kanbanDemo = "kanban\n  todo[To Do]\n    a[Task A]@{ ticket: T1, assigned: me, priority: High }\n    b[Task B]\n  done[Done]\n"

func kanbanLayoutOf(t *testing.T, src string, profile scene.Profile) scene.Scene {
	t.Helper()
	d := ParseDiagram([]byte(src))
	require.Empty(t, d.Diagnostics)
	in, err := d.Input(profile, scene.Options{})
	require.NoError(t, err)
	s, _, err := Layout(in)
	require.NoError(t, err)
	clause, failed, err := s.Validate()
	require.NoError(t, err)
	require.False(t, failed, clause)
	return s
}

func kanbanTexts(s scene.Scene) []*scene.Text {
	var out []*scene.Text
	for _, group := range s.Groups {
		for _, item := range group.Items {
			if text, ok := item.(*scene.Text); ok {
				out = append(out, text)
			}
		}
	}
	return out
}

func runsOf(text *scene.Text) []string {
	var lines []string
	for _, line := range text.Lines {
		joined := ""
		for _, run := range line {
			joined += run.Text
		}
		lines = append(lines, joined)
	}
	return lines
}

func TestKanbanCellGeometry(t *testing.T) {
	s := kanbanLayoutOf(t, kanbanDemo, scene.ProfileCell)
	require.Equal(t, geom.Size{W: 53, H: 16}, s.Canvas)
	require.Equal(t, []geom.Rect{{X: 1, Y: 1, W: 25, H: 14}, {X: 1, Y: 3, W: 24, H: 6}, {X: 1, Y: 10, W: 24, H: 3}, {X: 27, Y: 1, W: 25, H: 5}}, rects(s))
	require.Equal(t, []string{"s0", "s0.c0", "s0.c1", "s1"}, []string{s.Boxes[0].ID, s.Boxes[1].ID, s.Boxes[2].ID, s.Boxes[3].ID})
	require.Equal(t, "s0", s.Boxes[1].Parent)
	require.True(t, s.Boxes[1].Exclusive)
	require.False(t, s.Boxes[0].Exclusive)
	require.Equal(t, scene.RoleGroup, s.Boxes[0].Role)
}

func TestKanbanCellScene(t *testing.T) {
	s := kanbanLayoutOf(t, kanbanDemo, scene.ProfileCell)
	require.Len(t, s.Groups, 4)
	require.Equal(t, []scene.GroupRole{scene.GroupRoleGroup, scene.GroupRoleGroup, scene.GroupRoleNode, scene.GroupRoleNode}, []scene.GroupRole{s.Groups[0].Role, s.Groups[1].Role, s.Groups[2].Role, s.Groups[3].Role})
	require.Equal(t, []string{"s0", "s1", "s0.c0", "s0.c1"}, []string{s.Groups[0].Owner, s.Groups[1].Owner, s.Groups[2].Owner, s.Groups[3].Owner})
	card := s.Groups[2].Items
	frame, ok := card[0].(*scene.RoundRect)
	require.True(t, ok)
	require.Equal(t, "node", frame.Style)
	text, ok := card[1].(*scene.Text)
	require.True(t, ok)
	require.Equal(t, scene.AlignStart, text.Align)
	require.Equal(t, geom.Rect{X: 4, Y: 4, W: 18, H: 4}, text.Rect)
	require.Equal(t, []string{"Task A", "ticket: T1", "assigned: me", "priority: High"}, runsOf(text))
	title, ok := s.Groups[0].Items[1].(*scene.Text)
	require.True(t, ok)
	require.Equal(t, scene.AlignMiddle, title.Align)
	require.Equal(t, geom.Rect{X: 1, Y: 2, W: 25, H: 1}, title.Rect)
	require.Equal(t, []string{"To Do"}, runsOf(title))
}

func TestKanbanVectorGeometry(t *testing.T) {
	s := kanbanLayoutOf(t, "kanban\n  todo[To Do]\n    a[Task A]\n    b[Task B]\n", scene.ProfileVector)
	require.Equal(t, geom.Size{W: 13824, H: 8704}, s.Canvas)
	require.Equal(t, geom.Rect{X: 512, Y: 512, W: 12800, H: 7680}, s.Boxes[0].Rect)
	require.Equal(t, geom.Rect{X: 992, Y: 2112, W: 11840, H: 2560 - 0}, s.Boxes[1].Rect)
	require.Equal(t, geom.Rect{X: 992, Y: 2112 + 2560 + 320, W: 11840, H: 2560}, s.Boxes[2].Rect)
	require.Equal(t, geom.Rect{X: 512, Y: 672, W: 12800, H: 1280}, kanbanTexts(s)[0].Rect)
	text := kanbanTexts(s)[1]
	require.Equal(t, geom.Rect{X: 992 + 1280, Y: 2112 + 640, W: 11840 - 2560, H: 1280}, text.Rect)
}

func TestKanbanHeaderBandFollowsTallestTitle(t *testing.T) {
	s := kanbanLayoutOf(t, "kanban\n  a[One]\n  b[A title that must wrap onto several lines of the narrow column]\n    c[Card]\n", scene.ProfileCell)
	texts := kanbanTexts(s)
	long := texts[1]
	require.Greater(t, len(long.Lines), 2)
	require.Equal(t, int32(len(long.Lines)), long.Rect.H)
	require.Equal(t, int32(len(long.Lines)+1), s.Boxes[2].Rect.Y-s.Boxes[1].Rect.Y)
	require.Greater(t, texts[0].Rect.Y, long.Rect.Y)
}

func TestKanbanRepeatedSectionIDsRepeatCardsWithDistinctBoxIDs(t *testing.T) {
	s := kanbanLayoutOf(t, "kanban\n  s[One]\n    a[A]\n  s[Two]\n    b[B]\n", scene.ProfileCell)
	ids := make([]string, len(s.Boxes))
	for i, box := range s.Boxes {
		ids[i] = box.ID
	}
	require.Equal(t, []string{"s0", "s0.c0", "s0.c1", "s1", "s1.c0", "s1.c1"}, ids)
}

func TestKanbanConfigScalesSectionAndMargin(t *testing.T) {
	src := "%%{init: {\"kanban\": {\"sectionWidth\": 100, \"padding\": 4}}}%%\nkanban\n  a[One]\n    b[Task]\n"
	vector := kanbanLayoutOf(t, src, scene.ProfileVector)
	require.Equal(t, int32(6400), vector.Boxes[0].Rect.W)
	require.Equal(t, int32(256), vector.Boxes[0].Rect.X)
	require.Equal(t, int32(6400-960), vector.Boxes[1].Rect.W)
	cell := kanbanLayoutOf(t, src, scene.ProfileCell)
	require.Equal(t, int32(13), cell.Boxes[0].Rect.W)
	require.Equal(t, int32(12), cell.Boxes[1].Rect.W)
	require.Equal(t, int32(1), cell.Boxes[0].Rect.X)
	require.Contains(t, diagramModelDump(t, src), `"padding":4,"sectionWidth":100`)
}

func TestKanbanModelDumpNamesSectionsAndCards(t *testing.T) {
	dump := diagramModelDump(t, kanbanDemo)
	require.Contains(t, dump, `{"id":"s0","role":"group","parent":"","exclusive":false,"direction":"","shape":"kanbanSection","text":"To Do"}`)
	require.Contains(t, dump, `{"id":"s0.c0","role":"node","parent":"s0","exclusive":true,"shape":"kanbanItem","text":"Task A<br>ticket: T1<br>assigned: me<br>priority: High"}`)
	require.Contains(t, dump, `"routes":[]`)
}

func TestKanbanLabelsAreTrimmed(t *testing.T) {
	s := kanbanLayoutOf(t, "kanban\n  s[  Todo  ]\n    c[ Card ]\n", scene.ProfileCell)
	require.Equal(t, []string{"Todo"}, runsOf(kanbanTexts(s)[0]))
	require.Equal(t, []string{"Card"}, runsOf(kanbanTexts(s)[1]))
}

func TestKanbanEmptyDiagramIsAMargin(t *testing.T) {
	for profile, want := range map[scene.Profile]geom.Size{scene.ProfileVector: {W: 1024, H: 1024}, scene.ProfileCell: {W: 2, H: 2}} {
		s := kanbanLayoutOf(t, "kanban\n\n", profile)
		require.Equal(t, want, s.Canvas)
		require.Empty(t, s.Boxes)
	}
}

func TestKanbanProfilesShareIdentities(t *testing.T) {
	vector := kanbanLayoutOf(t, kanbanDemo, scene.ProfileVector)
	cell := kanbanLayoutOf(t, kanbanDemo, scene.ProfileCell)
	require.Len(t, cell.Boxes, len(vector.Boxes))
	for i := range vector.Boxes {
		require.Equal(t, vector.Boxes[i].ID, cell.Boxes[i].ID)
		require.Equal(t, vector.Boxes[i].Parent, cell.Boxes[i].Parent)
	}
}

func TestKanbanCorpusValidatesInBothProfiles(t *testing.T) {
	paths, err := filepath.Glob(filepath.Join("..", "..", "corpus", "kanban", "*", "*.mmd"))
	require.NoError(t, err)
	require.NotEmpty(t, paths)
	for _, path := range paths {
		src, err := os.ReadFile(path)
		require.NoError(t, err)
		for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
			kanbanLayoutOf(t, string(src), profile)
		}
	}
}

func kanbanInput() Input {
	return Input{
		Kind:    kanbanKind,
		Options: scene.DefaultOptions(),
		Boxes:   []Box{{ID: "s", Role: scene.RoleGroup, Shape: kanbanSectionShape}, {ID: "c", Role: scene.RoleNode, Parent: "s", Exclusive: true, Text: "card"}},
	}
}

func TestKanbanRejectsInconsistentBoxes(t *testing.T) {
	missing := kanbanInput()
	missing.Boxes[1].Parent = "nowhere"
	_, _, err := Layout(missing)
	require.ErrorIs(t, err, errKanbanDomain)
	nested := kanbanInput()
	nested.Boxes = append(nested.Boxes, Box{ID: "inner", Role: scene.RoleGroup, Parent: "s"})
	_, _, err = Layout(nested)
	require.ErrorIs(t, err, errKanbanDomain)
	card := kanbanInput()
	card.Boxes = append(card.Boxes, Box{ID: "deep", Role: scene.RoleNode, Parent: "c", Exclusive: true})
	_, _, err = Layout(card)
	require.ErrorIs(t, err, errKanbanDomain)
}

func TestKanbanEnforcesLimits(t *testing.T) {
	for name, edit := range map[string]func(*Input){
		"nodes": func(in *Input) { in.Options.Limits.MaxNodes = 1 },
		"text":  func(in *Input) { in.Options.Limits.MaxTextBytes = 3 },
		"edges": func(in *Input) { in.Options.Limits.MaxEdges = 1; in.Routes = []Route{{ID: "e"}, {ID: "f"}} },
	} {
		in := kanbanInput()
		edit(&in)
		_, _, err := Layout(in)
		var limit *layered.LimitError
		require.True(t, errors.As(err, &limit), name)
	}
}

func TestKanbanRejectsOversizedConfig(t *testing.T) {
	in := kanbanInput()
	in.Options.Config = []scene.Config{{Key: "sectionWidth", Value: "99999999"}}
	_, _, err := Layout(in)
	require.ErrorIs(t, err, geom.ErrOverflow)
}
