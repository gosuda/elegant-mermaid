package class_test

import (
	"testing"

	model "github.com/gosuda/elegant-mermaid/internal/model/class"
	"github.com/gosuda/elegant-mermaid/internal/source"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/class"
)

func TestGeneratedIDsSkipDeclarations(t *testing.T) {
	src := []byte("classDiagram\nnote \"first\"\nclass note0\nclass note1\nclass interface0\nA --() Port\nnote \"second\"\n")
	f, ds := parser.Parse(src, nil)
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	m, ds := model.Resolve(src, f)
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	if m.Notes[0].ID != "note2" || m.Notes[1].ID != "note3" {
		t.Fatal(m.Notes)
	}
	for _, c := range m.Classes {
		if c.Interface && c.ID != "interface1" {
			t.Fatal(c)
		}
	}
	if len(m.Classes) != 5 {
		t.Fatal(m.Classes)
	}
}

func TestResolution(t *testing.T) {
	src := []byte("classDiagram\nnamespace Outer.Inner {\nclass Box~T~[\"Container\"] {\n<<interface>>\n+String value\n+get(x)$ Result~T~\n}\n}\nBox <|-- Child : inherits\nnote for Box \"A note\"\n")
	f, ds := parser.Parse(src, nil)
	if len(ds) > 0 {
		t.Fatal(ds)
	}
	m, ds := model.Resolve(src, f)
	if len(ds) > 0 {
		t.Fatal(ds)
	}
	if len(m.Classes) != 2 || len(m.Namespaces) != 2 || len(m.Relations) != 1 || len(m.Notes) != 1 {
		t.Fatalf("%+v", m)
	}
	assertResolvedClass(t, m.Classes[0])
	assertResolvedRelation(t, m.Relations[0])
}

func assertResolvedClass(t *testing.T, c model.Class) {
	t.Helper()
	if c.ID != "Box" || c.Label != "Container" || c.Generic != "T" || c.Parent != "Outer.Inner" || len(c.Attributes) != 1 || len(c.Methods) != 1 || len(c.Annotations) != 1 {
		t.Fatalf("%+v", c)
	}
}

func assertResolvedRelation(t *testing.T, relation model.Relation) {
	t.Helper()
	if relation.MarkerStart != "extension" || relation.Label != "inherits" {
		t.Fatal(relation)
	}
}
func TestUnknownAnnotation(t *testing.T) {
	f, _ := parser.Parse([]byte("classDiagram\n<<interface>> Missing\n"), nil)
	_, ds := model.Resolve(nil, f)
	if len(ds) != 1 || ds[0].Code != "class/annotation-target-unknown" || ds[0].Span != (source.Span{Start: 27, End: 34}) {
		t.Fatal(ds)
	}
}
func TestMembers(t *testing.T) {
	for _, c := range []struct {
		input, text              string
		method, static, abstract bool
	}{{"+name: String", "+name: String", false, false, false}, {"+get(x) String$", "+get(x) : String", true, true, false}, {"#run()*", "#run()", true, false, true}} {
		m := model.ParseMember(c.input, source.Span{})
		if m.Text != c.text || m.Method != c.method || m.Static != c.static || m.Abstract != c.abstract {
			t.Fatalf("%s: %+v", c.input, m)
		}
	}
}
func TestBareNames(t *testing.T) {
	f, _ := parser.Parse([]byte("classDiagram\nUnused\nclass A\nclass A[\"new\"]\nnote for Missing \"text\"\n"), nil)
	m, ds := model.Resolve(nil, f)
	if len(ds) > 0 || len(m.Classes) != 1 || m.Classes[0].Label != "new" {
		t.Fatal(m, ds)
	}
}
