package layout

import (
	"slices"
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func usecaseInput(t *testing.T, src string, profile scene.Profile) Input {
	t.Helper()
	d := ParseDiagram([]byte(src))
	for _, diagnostic := range d.Diagnostics {
		t.Fatalf("diagnostic: %+v", diagnostic)
	}
	in, err := d.Input(profile, scene.Options{})
	if err != nil {
		t.Fatal(err)
	}
	return in
}

func usecaseScene(t *testing.T, src string, profile scene.Profile) scene.Scene {
	t.Helper()
	s, _, err := Layout(usecaseInput(t, src, profile))
	if err != nil {
		t.Fatal(err)
	}
	return s
}

func usecaseSize(t *testing.T, src string, profile scene.Profile) (geom.Size, bool) {
	t.Helper()
	in := usecaseInput(t, src, profile)
	input, err := usecaseFamilyInput(in)
	if err != nil {
		t.Fatal(err)
	}
	return input.Sizes[0], input.Exact[0]
}

func usecaseShapes(in Input) []string {
	var shapes []string
	for _, b := range in.Boxes {
		shapes = append(shapes, b.Shape)
	}
	return shapes
}

func TestUsecaseEllipsesWrapAndTakeKindMinimum(t *testing.T) {
	for _, c := range []struct {
		profile scene.Profile
		minimum int32
	}{{scene.ProfileCell, 15}, {scene.ProfileVector, 7680}} {
		size, exact := usecaseSize(t, "usecase-beta\nU(short)\n", c.profile)
		if exact || size.W != c.minimum {
			t.Fatalf("%v: %v exact=%v", c.profile, size, exact)
		}
	}
	size, _ := usecaseSize(t, "usecase-beta\nU(abcdefghijklmno pqrstuvwxyz)\n", scene.ProfileCell)
	if size != (geom.Size{W: 19, H: 4}) {
		t.Fatalf("wrapped ellipse size %v", size)
	}
}

func TestUsecaseActorSizeHasNoEllipseMinimum(t *testing.T) {
	for _, c := range []struct {
		profile scene.Profile
		want    geom.Size
	}{{scene.ProfileVector, geom.Size{W: 4608, H: 7424}}, {scene.ProfileCell, geom.Size{W: 9, H: 9}}} {
		size, exact := usecaseSize(t, "usecase-beta\nactor A\n", c.profile)
		if !exact || size != c.want {
			t.Fatalf("%v: %v exact=%v", c.profile, size, exact)
		}
	}
}

func TestUsecaseActorsAndBoundariesSelectShapes(t *testing.T) {
	src := "usecase-beta\nactor A\nactor B@{type:hollow}\nactor C@{type:awesome}\nactor D@{icon:person}\nactor E@{business:true}\nsystemBoundary S@{type:package}\nU@{business:true}\nend\n"
	in := usecaseInput(t, src, scene.ProfileCell)
	want := []string{"usecaseActor", "usecaseActorHollow", "usecaseActorAwesome", "usecaseActorIcon:icon:person", "usecaseActor:business", "rect:package", "usecaseBusiness"}
	if got := usecaseShapes(in); !slices.Equal(got, want) {
		t.Fatalf("%v", got)
	}
	if in.Boxes[len(in.Boxes)-1].Parent != "S" || in.Boxes[5].Role != scene.RoleGroup {
		t.Fatalf("%+v", in.Boxes)
	}
}

func TestUsecaseRoutesKeepDirectionMarkersAndStereotypeStyle(t *testing.T) {
	in := usecaseInput(t, "usecase-beta\ne0\nA <-- B\nB --o C\nC --x D\nD ..>:include E\n", scene.ProfileCell)
	var ids, kinds []string
	for _, r := range in.Routes {
		ids = append(ids, r.ID)
		kinds = append(kinds, r.MarkerStart+"/"+r.MarkerEnd+"/"+r.Line)
	}
	if !slices.Equal(ids, []string{"e1", "e2", "e3", "e4"}) || !slices.Equal(kinds, []string{"point/none/normal", "none/circle/normal", "none/cross/normal", "none/point/dotted"}) {
		t.Fatalf("%v %v", ids, kinds)
	}
	if !slices.ContainsFunc(in.Labels, func(l Label) bool { return l.Owner == "e4" }) {
		t.Fatal("include relation lost its label")
	}
}

func TestUsecaseNotesMergeIntoBoxDeclarationOrder(t *testing.T) {
	in := usecaseInput(t, "usecase-beta\nA\nnote for A \"detail\"\nB\n", scene.ProfileCell)
	var ids []string
	for _, b := range in.Boxes {
		ids = append(ids, b.ID)
	}
	if !slices.Equal(ids, []string{"A", "note-0", "B"}) || in.Boxes[1].Shape != "note" || in.Routes[0].To != "A" {
		t.Fatalf("%v %+v", ids, in.Routes)
	}
}

func usecaseGroup(s scene.Scene, owner string) *scene.Group {
	for _, g := range s.Groups {
		if g.Owner == owner {
			return g
		}
	}
	return nil
}

func TestUsecaseSceneHasActorFigureAndEllipse(t *testing.T) {
	for _, profile := range []scene.Profile{scene.ProfileCell, scene.ProfileVector} {
		s := usecaseScene(t, "usecase-beta\nactor A(User)\nU(Task)\n", profile)
		var head, strokes bool
		for _, item := range usecaseGroup(s, "A").Items {
			switch item.(type) {
			case *scene.Ellipse:
				head = true
			case *scene.Polyline:
				strokes = true
			}
		}
		if !head || !strokes {
			t.Fatalf("%v: actor items %+v", profile, usecaseGroup(s, "A").Items)
		}
		if _, ok := usecaseGroup(s, "U").Items[0].(*scene.Ellipse); !ok {
			t.Fatalf("%v: use case starts with %T", profile, usecaseGroup(s, "U").Items[0])
		}
	}
}

func usecaseLines(s scene.Scene, owner string) []string {
	var lines []string
	for _, item := range usecaseGroup(s, owner).Items {
		if text, ok := item.(*scene.Text); ok {
			for _, line := range text.Lines {
				var b strings.Builder
				for _, run := range line {
					b.WriteString(run.Text)
				}
				lines = append(lines, b.String())
			}
		}
	}
	return lines
}

func TestUsecaseEmphasisAcrossWrapBoundaryStaysBold(t *testing.T) {
	label := "**abcdefghijklmnopqrstuvwxyz abcdefghijklmnopqrstuvwxyz**"
	src := "usecase-beta\nU(" + label + ")\n"
	if size, _ := usecaseSize(t, src, scene.ProfileCell); size != (geom.Size{W: 19, H: 6}) {
		t.Fatalf("size %v", size)
	}
	s := usecaseScene(t, src, scene.ProfileCell)
	want := []string{"abcdefghijklmno", "pqrstuvwxyz", "abcdefghijklmno", "pqrstuvwxyz"}
	if got := usecaseLines(s, "U"); !slices.Equal(got, want) {
		t.Fatalf("%q", got)
	}
	var bold bool
	for _, item := range usecaseGroup(s, "U").Items {
		if text, ok := item.(*scene.Text); ok {
			for _, line := range text.Lines {
				for _, run := range line {
					bold = bold || run.Bold
				}
			}
		}
	}
	if !bold {
		t.Fatal("emphasis lost its weight")
	}
}

func TestUsecaseForcedBreaksKeepEmptyRows(t *testing.T) {
	src := "usecase-beta\nU(x<br/><br/>y)\n"
	if size, _ := usecaseSize(t, src, scene.ProfileCell); size != (geom.Size{W: 15, H: 5}) {
		t.Fatalf("size %v", size)
	}
	if got := usecaseLines(usecaseScene(t, src, scene.ProfileCell), "U"); !slices.Equal(got, []string{"x", "", "y"}) {
		t.Fatalf("%q", got)
	}
}

func TestUsecaseLiteralMarkupStaysUnstyled(t *testing.T) {
	s := usecaseScene(t, "usecase-beta\nB(a * b _c_d)\nC($$x$$)\n", scene.ProfileCell)
	for owner, want := range map[string]string{"B": "a * b _c_d", "C": "$$x$$"} {
		if got := usecaseLines(s, owner); !slices.Equal(got, []string{want}) {
			t.Fatalf("%s: %q", owner, got)
		}
	}
}

func TestUsecaseMinimumLengthSpansRanks(t *testing.T) {
	short := usecaseScene(t, "usecase-beta\nactor A\nA --> B\n", scene.ProfileVector)
	long := usecaseScene(t, "usecase-beta\nactor A\nA ----> B\n", scene.ProfileVector)
	if long.Canvas.H <= short.Canvas.H {
		t.Fatalf("long arrow canvas %v is not taller than %v", long.Canvas, short.Canvas)
	}
}
