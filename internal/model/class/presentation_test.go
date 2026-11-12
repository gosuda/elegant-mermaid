package class_test

import (
	"testing"

	model "github.com/gosuda/elegant-mermaid/internal/model/class"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/class"
)

func TestPresentationResolution(t *testing.T) {
	src := []byte("classDiagram\nclass A[\"A #amp; B\"]\ncssClass \"A,Missing\" red\nclassDef red color:navy,fill:tan\nclick A call invoke(\"a,b\", c) \"tip\"\nnote for Missing \"ignored target\"\nclass Missing\n")
	file, ds := parser.Parse(src, nil)
	if len(ds) > 0 {
		t.Fatal(ds)
	}
	m, ds := model.Resolve(src, file)
	if len(ds) > 0 {
		t.Fatal(ds)
	}
	assertPresentationClass(t, m.Classes[0])
	assertPresentationClicks(t, m.Clicks)
	if m.Notes[0].Target != "" {
		t.Fatal(m.Notes)
	}
}

func assertPresentationClass(t *testing.T, c model.Class) {
	t.Helper()
	if c.Label != "A & B" || c.CSS != "default red" || len(c.Styles) != 1 {
		t.Fatal(c)
	}
	if len(c.TextStyles) != 1 || c.TextStyles[0] != "color:navy,bgFill:tan" {
		t.Fatal(c.TextStyles)
	}
}

func assertPresentationClicks(t *testing.T, clicks []model.Click) {
	t.Helper()
	if len(clicks) != 1 || clicks[0].Value != "invoke" || len(clicks[0].Args) != 2 || clicks[0].Args[0] != "a,b" || clicks[0].Args[1] != "c" {
		t.Fatal(clicks)
	}
}

func TestEmptyExplicitLabel(t *testing.T) {
	file, ds := parser.Parse([]byte("classDiagram\nclass A[\"\"]\n"), nil)
	if len(ds) > 0 {
		t.Fatal(ds)
	}
	m, ds := model.Resolve(nil, file)
	if len(ds) > 0 || m.Classes[0].Label != "" {
		t.Fatal(m, ds)
	}
}
