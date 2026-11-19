package cells

import (
	"bytes"
	"encoding/json"
	"reflect"
	"slices"
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func TestRenderAttachmentProjection(t *testing.T) {
	cases := []struct {
		name     string
		box      geom.Rect
		points   []geom.Point
		row, col int
		join     rune
	}{
		{"vertical", geom.Rect{X: 1, Y: 7, W: 5, H: 3}, []geom.Point{{X: 3, Y: 4}, {X: 3, Y: 7}}, 3, 3, '┬'},
		{"horizontal", geom.Rect{X: 9, Y: 1, W: 5, H: 3}, []geom.Point{{X: 6, Y: 2}, {X: 9, Y: 2}}, 2, 5, '├'},
	}
	for _, tc := range cases {
		for _, direction := range []string{"forward", "reverse"} {
			t.Run(tc.name+"/"+direction, func(t *testing.T) {
				points := slices.Clone(tc.points)
				from, to := "a", "b"
				if direction == "reverse" {
					slices.Reverse(points)
					from, to = to, from
				}
				s := projectionScene(geom.Rect{X: 1, Y: 1, W: 5, H: 3}, tc.box, from, to, points)
				assertAttachmentJoin(t, s, geom.Point{X: int32(tc.col), Y: int32(tc.row)}, tc.join)
			})
		}
	}
}

func assertAttachmentJoin(t *testing.T, s scene.Scene, at geom.Point, join rune) {
	t.Helper()
	before := slices.Clone(s.Routes[0].Points)
	dumpBefore := s.AppendJSON(nil)
	scene.ProjectCellAttachments(&s)
	if !bytes.Equal(dumpBefore, s.AppendJSON(nil)) {
		t.Fatal("assembly projection changed canonical dump")
	}
	itemsBefore, err := json.Marshal(s.Groups)
	if err != nil {
		t.Fatal(err)
	}
	got, err := Render(s, Options{})
	itemsAfter, snapshotErr := json.Marshal(s.Groups)
	if snapshotErr != nil || !bytes.Equal(itemsBefore, itemsAfter) {
		t.Fatal("render changed assembled primitives")
	}
	if err != nil {
		t.Fatal(err)
	}
	rows := strings.Split(string(got.Text), "\n")
	if chars := []rune(rows[at.Y]); len(chars) <= int(at.X) || chars[at.X] != join {
		t.Fatalf("missing border join: %s", got.Text)
	}
	if !reflect.DeepEqual(s.Routes[0].Points, before) {
		t.Fatal("render changed canonical route")
	}
}

func projectionScene(a, b geom.Rect, from, to string, points []geom.Point) scene.Scene {
	return scene.Scene{
		Dump: scene.Dump{
			Options: scene.Options{Profile: scene.ProfileCell},
			Canvas:  geom.Size{W: 16, H: 12},
			Boxes:   []scene.Box{{ID: "a", Rect: a}, {ID: "b", Rect: b}},
			Routes:  []scene.Route{{ID: "e", From: from, To: to, Orthogonal: true, Points: points}},
		},
		Groups: []*scene.Group{
			{Role: scene.GroupRoleEdge, Owner: "e", Items: []scene.Primitive{&scene.Polyline{Shape: scene.Shape{Style: "edge"}, Points: points}}},
			{Items: []scene.Primitive{&scene.Rect{Shape: scene.Shape{Style: "node"}, Rect: a}, &scene.Rect{Shape: scene.Shape{Style: "node"}, Rect: b}}},
		},
	}
}

func TestRenderAttachmentMarkersAndSelfLoop(t *testing.T) {
	a := geom.Rect{X: 1, Y: 1, W: 5, H: 5}
	points := []geom.Point{{X: 6, Y: 2}, {X: 10, Y: 2}, {X: 10, Y: 4}, {X: 6, Y: 4}}
	s := projectionScene(a, geom.Rect{}, "a", "a", points)
	start := &scene.MarkerRef{Marker: "point", At: points[0]}
	end := &scene.MarkerRef{Marker: "point", At: points[3]}
	s.Groups[0].Items = append(s.Groups[0].Items, start, end)
	before := slices.Clone(points)
	got := renderProjectedScene(t, &s)
	rows := strings.Split(string(got.Text), "\n")
	for _, row := range []int{2, 4} {
		if chars := []rune(rows[row]); len(chars) <= 5 || chars[5] != '▶' || chars[6] == '▶' {
			t.Fatalf("marker did not join painted self-loop border: %s", got.Text)
		}
	}
	if !reflect.DeepEqual(points, before) || start.At != before[0] || end.At != before[3] {
		t.Fatal("render mutated self-loop or markers")
	}
}

func TestRenderAttachmentAdjacentBend(t *testing.T) {
	a := geom.Rect{X: 1, Y: 1, W: 5, H: 5}
	b := geom.Rect{X: 9, Y: 7, W: 5, H: 3}
	points := []geom.Point{{X: 6, Y: 2}, {X: 6, Y: 8}, {X: 9, Y: 8}}
	s := projectionScene(a, b, "a", "b", points)
	dumpBefore := s.AppendJSON(nil)
	scene.ProjectCellAttachments(&s)
	if !bytes.Equal(dumpBefore, s.AppendJSON(nil)) {
		t.Fatal("assembly projection changed canonical dump")
	}
	itemsBefore, err := json.Marshal(s.Groups)
	if err != nil {
		t.Fatal(err)
	}
	got, err := Render(s, Options{})
	itemsAfter, snapshotErr := json.Marshal(s.Groups)
	if snapshotErr != nil || !bytes.Equal(itemsBefore, itemsAfter) {
		t.Fatal("render changed assembled primitives")
	}
	if err != nil {
		t.Fatal(err)
	}
	if strings.ContainsRune(string(got.Text), '⣿') {
		t.Fatal("orthogonal attachment became a dotted diagonal")
	}
	rows := strings.Split(string(got.Text), "\n")
	if chars := []rune(rows[6]); len(chars) <= 5 || chars[5] != '│' {
		t.Fatalf("adjacent bend lost vertical continuity: %s", got.Text)
	}
}

func TestRenderCoincidentAttachments(t *testing.T) {
	points := []geom.Point{{X: 6, Y: 6}}
	s := projectionScene(geom.Rect{X: 1, Y: 1, W: 5, H: 5}, geom.Rect{X: 6, Y: 6, W: 5, H: 3}, "a", "b", points)
	s.Routes[0].MarkerStart = "point"
	s.Routes[0].MarkerEnd = "point"
	start := &scene.MarkerRef{Marker: "point", At: points[0]}
	end := &scene.MarkerRef{Marker: "point", At: points[0]}
	s.Groups[0].Items = append(s.Groups[0].Items, start, end)
	got := renderProjectedScene(t, &s)
	rows := strings.Split(string(got.Text), "\n")
	for _, at := range []geom.Point{{X: 5, Y: 5}, {X: 6, Y: 6}} {
		if chars := []rune(rows[at.Y]); len(chars) <= int(at.X) || chars[at.X] != '▶' {
			t.Fatalf("coincident markers lost endpoint attribution: %s", got.Text)
		}
	}
	if !reflect.DeepEqual(points, []geom.Point{{X: 6, Y: 6}}) || start.At != points[0] || end.At != points[0] {
		t.Fatal("render mutated coincident attachments")
	}
	if chars := []rune(rows[5]); len(chars) <= 6 || chars[6] != '┐' {
		t.Fatalf("coincident corner route did not use x-first bend: %s", got.Text)
	}
}

func renderProjectedScene(t *testing.T, s *scene.Scene) Result {
	t.Helper()
	dumpBefore := s.AppendJSON(nil)
	scene.ProjectCellAttachments(s)
	if !bytes.Equal(dumpBefore, s.AppendJSON(nil)) {
		t.Fatal("assembly projection changed canonical dump")
	}
	itemsBefore, err := json.Marshal(s.Groups)
	if err != nil {
		t.Fatal(err)
	}
	got, err := Render(*s, Options{})
	itemsAfter, snapshotErr := json.Marshal(s.Groups)
	if snapshotErr != nil || !bytes.Equal(itemsBefore, itemsAfter) {
		t.Fatal("render changed assembled primitives")
	}
	if err != nil {
		t.Fatal(err)
	}
	return got
}

func TestRenderCoincidentTargetMarkerMetadata(t *testing.T) {
	points := []geom.Point{{X: 6, Y: 2}}
	s := projectionScene(geom.Rect{X: 1, Y: 1, W: 5, H: 3}, geom.Rect{X: 6, Y: 1, W: 5, H: 3}, "a", "b", points)
	s.Routes[0].MarkerEnd = "point"
	s.Groups[0].Items = append(s.Groups[0].Items, &scene.MarkerRef{Marker: "point", At: points[0]})
	dumpBefore := s.AppendJSON(nil)
	scene.ProjectCellAttachments(&s)
	if !bytes.Equal(dumpBefore, s.AppendJSON(nil)) {
		t.Fatal("assembly projection changed canonical dump")
	}
	itemsBefore, err := json.Marshal(s.Groups)
	if err != nil {
		t.Fatal(err)
	}
	got, err := Render(s, Options{})
	itemsAfter, snapshotErr := json.Marshal(s.Groups)
	if snapshotErr != nil || !bytes.Equal(itemsBefore, itemsAfter) {
		t.Fatal("render changed assembled primitives")
	}
	if err != nil {
		t.Fatal(err)
	}
	rows := strings.Split(string(got.Text), "\n")
	if chars := []rune(rows[2]); len(chars) <= 6 || chars[6] != '▶' || chars[5] == '▶' {
		t.Fatalf("target-only marker attributed to source: %s", got.Text)
	}
}

func TestAssemblyProjectionPreservesTargetAxis(t *testing.T) {
	points := []geom.Point{{X: 3, Y: 4}, {X: 14, Y: 4}, {X: 14, Y: 10}}
	s := projectionScene(geom.Rect{X: 1, Y: 1, W: 5, H: 3}, geom.Rect{X: 9, Y: 7, W: 5, H: 3}, "a", "b", points)
	canonical := s.AppendJSON(nil)
	original := s.Groups[0].Items[0].(*scene.Polyline)
	scene.ProjectCellAttachments(&s)
	projected := s.Groups[0].Items[0].(*scene.Polyline)
	want := []geom.Point{{X: 3, Y: 3}, {X: 14, Y: 3}, {X: 14, Y: 4}, {X: 13, Y: 4}, {X: 13, Y: 9}}
	if !reflect.DeepEqual(projected.Points, want) || projected == original {
		t.Fatalf("attachment projection = %v, want %v in a replacement primitive", projected.Points, want)
	}
	if !bytes.Equal(canonical, s.AppendJSON(nil)) || !reflect.DeepEqual(original.Points, points) {
		t.Fatal("assembly changed canonical geometry")
	}
}
