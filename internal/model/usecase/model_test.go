package usecase_test

import (
	"slices"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/usecase"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/usecase"
)

func resolved(t *testing.T, src string) (*model.Model, []diag.Diagnostic) {
	t.Helper()
	start, ds := parser.Parse([]byte(src), nil)
	if len(ds) != 0 {
		t.Fatalf("parse: %v", ds)
	}
	return model.Resolve([]byte(src), start)
}

func ids(m *model.Model) []string {
	var out []string
	for _, node := range m.Nodes {
		out = append(out, node.ID)
	}
	return out
}

func text(src string, d diag.Diagnostic) string { return src[d.Span.Start:d.Span.End] }

func TestForwardReferencesKeepFirstOccurrenceOrder(t *testing.T) {
	m, ds := resolved(t, "usecase-beta\nA --> B\nactor A(User)\nB(Task)\n")
	if len(ds) != 0 || !slices.Equal(ids(m), []string{"A", "B"}) {
		t.Fatalf("%v %v", ds, ids(m))
	}
	if m.Nodes[0].Kind != model.KindActor || m.Nodes[0].Label != "User" || m.Nodes[1].Label != "Task" || m.Relations[0].ID != "edge-0" {
		t.Fatalf("%+v %+v", m.Nodes, m.Relations)
	}
}

func TestMatchingDeclarationsMergeUniqueClasses(t *testing.T) {
	m, ds := resolved(t, "usecase-beta\nA(Task):::one\nA(Task):::two,one\n")
	if len(ds) != 0 || len(m.Nodes) != 1 || !slices.Equal(m.Nodes[0].Classes, []string{"one", "two"}) {
		t.Fatalf("%v %+v", ds, m.Nodes)
	}
}

func TestConflictsReportLaterAndRelatedFirstSpan(t *testing.T) {
	src := "usecase-beta\nA(First)\nA(Second)\n"
	_, ds := resolved(t, src)
	if len(ds) != 1 || ds[0].Code != "usecase/declaration-conflict" || ds[0].Message != "conflicting declaration of A: different label" {
		t.Fatalf("%+v", ds)
	}
	related := ds[0].Related[0]
	if text(src, ds[0]) != "A(Second)" || src[related.Span.Start:related.Span.End] != "A(First)" || related.Message != "first declared here" {
		t.Fatalf("%+v", ds[0])
	}
}

func TestQuotedNamesGenerateASCIIIDsAndRepeatConflicts(t *testing.T) {
	_, ds := resolved(t, "usecase-beta\n\"Some user\"\n\"Some user\"\n")
	if len(ds) != 1 || ds[0].Message != "conflicting declaration of Some_user: duplicate generated id" {
		t.Fatalf("%+v", ds)
	}
}

func TestBoundaryMembersAreOrderedUniqueAndDefaultToRect(t *testing.T) {
	m, ds := resolved(t, "usecase-beta\nsystemBoundary S(Title)\nactor A\nB\nB\nend\n")
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	group := m.Nodes[0]
	if group.Kind != model.KindBoundary || group.BoundaryType != "rect" || !slices.Equal(group.Members, []string{"A", "B"}) {
		t.Fatalf("%+v", group)
	}
	if m.Nodes[1].Parent != "S" || m.Nodes[2].Parent != "S" {
		t.Fatalf("%+v", m.Nodes)
	}
}

func TestMetadataUpdatesExistingSymbolsWithoutCreatingNodes(t *testing.T) {
	m, ds := resolved(t, "usecase-beta\nA@{business:true}\nA(Task)\nactor B\nB@{type:hollow}\nB@{business:true}\n")
	if len(ds) != 0 || len(m.Nodes) != 2 || !m.Nodes[0].Business {
		t.Fatalf("%v %+v", ds, m.Nodes)
	}
	if actor := m.Nodes[1]; actor.ActorType != "hollow" || !actor.Business {
		t.Fatalf("%+v", actor)
	}
}

func TestInvalidMetadataReportsPropertySpan(t *testing.T) {
	src := "usecase-beta\nA(Task)@{type:hollow}\n"
	_, ds := resolved(t, src)
	if len(ds) != 1 || ds[0].Code != "usecase/invalid-metadata" || ds[0].Message != "invalid metadata type for usecase A" || text(src, ds[0]) != "type:hollow" {
		t.Fatalf("%+v", ds)
	}
}

func TestIncompatibleActorGeometryReportsDeclaration(t *testing.T) {
	src := "usecase-beta\nactor A@{type:hollow,icon:person}\n"
	_, ds := resolved(t, src)
	if len(ds) != 1 || ds[0].Code != "usecase/invalid-actor" || ds[0].Message != "invalid actor A: icon cannot combine with hollow or awesome type" || text(src, ds[0]) != "A@{type:hollow,icon:person}" {
		t.Fatalf("%+v", ds)
	}
}

func TestRelationKindsAndMinimumLengths(t *testing.T) {
	m, ds := resolved(t, "usecase-beta\nA ---> B\nA -- yes ----> B\nA --o B\nA <-- C\nB ..> : Include C\nB --|> C\nA --- D\n")
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	want := []struct {
		kind, label, start, end string
		min                     int
	}{
		{"association", "", "none", "point", 2},
		{"association", "yes", "none", "point", 3},
		{"association", "", "none", "circle", 1},
		{"association", "", "point", "none", 1},
		{"include", "«include»", "none", "point", 1},
		{"generalization", "", "none", "extension", 1},
		{"association", "", "none", "none", 2},
	}
	for i, w := range want {
		r := m.Relations[i]
		if r.Kind != w.kind || r.Label != w.label || r.MarkerStart != w.start || r.MarkerEnd != w.end || r.MinLength != w.min {
			t.Fatalf("relation %d: %+v", i, r)
		}
	}
}

func TestRelationEndpointsAreValidated(t *testing.T) {
	cases := []struct{ src, message string }{
		{"usecase-beta\nactor A\nactor B\nA ..> : include B\n", "invalid include relationship: both endpoints must be use cases"},
		{"usecase-beta\nactor A\nB(Task)\nA --|> B\n", "invalid generalization relationship: both endpoints must be actors or both use cases"},
		{"usecase-beta\nsystemBoundary S\nend\nS --> A\n", "invalid association relationship: boundaries cannot be endpoints"},
		{"usecase-beta\njson J@{\"a\":1}\nactor A\nA --o J\n", "invalid association relationship: JSON endpoints require a solid point or markerless association"},
	}
	for _, c := range cases {
		_, ds := resolved(t, c.src)
		if len(ds) != 1 || ds[0].Code != "usecase/invalid-relationship" || ds[0].Message != c.message {
			t.Fatalf("%q: %+v", c.src, ds)
		}
	}
}

func TestNotesStylesAndClassesResolveTargets(t *testing.T) {
	m, ds := resolved(t, "usecase-beta\nactor A\nA --> B\nnote for A \"first\"\nnote for B \"second\"\nclassDef hot fill:#f00\nclass A,B hot\nstyle A stroke:#000\ne@{animate:true}\n")
	requireUnresolvedMetadataTarget(t, ds)
	requireNotes(t, m.Notes)
	requireDefinitions(t, m.Definitions)
	requireNodeAppearance(t, m.Nodes[0])
}

func requireUnresolvedMetadataTarget(t *testing.T, ds []diag.Diagnostic) {
	t.Helper()
	if len(ds) != 1 || ds[0].Code != "usecase/unresolved-target" || ds[0].Message != "unresolved metadata target e" {
		t.Fatalf("%+v", ds)
	}
}

func requireNotes(t *testing.T, notes []model.Note) {
	t.Helper()
	if len(notes) != 2 || notes[0].ID != "note-0" || notes[1].ID != "note-1" || notes[1].Target != "B" {
		t.Fatalf("%+v", notes)
	}
}

func requireDefinitions(t *testing.T, definitions []model.Definition) {
	t.Helper()
	if len(definitions) != 1 || definitions[0].Name != "hot" || definitions[0].Text != "fill:#f00" {
		t.Fatalf("%+v", definitions)
	}
}

func requireNodeAppearance(t *testing.T, node model.Node) {
	t.Helper()
	if !slices.Equal(node.Classes, []string{"hot"}) || !slices.Equal(node.Styles, []string{"stroke:#000"}) {
		t.Fatalf("%+v", node)
	}
}

func TestExplicitEdgeIDsAcceptAnimationMetadata(t *testing.T) {
	m, ds := resolved(t, "usecase-beta\nA e@--> B\ne@{animation:fast}\nA --> B\n")
	if len(ds) != 0 || len(m.Relations) != 2 {
		t.Fatalf("%v %+v", ds, m.Relations)
	}
	if first := m.Relations[0]; first.ID != "e" || !first.Explicit || !first.Animate || first.Animation != "fast" || m.Relations[1].ID != "edge-0" {
		t.Fatalf("%+v", m.Relations)
	}
}

func TestDirectionAndAccessibilityLastValueWins(t *testing.T) {
	m, ds := resolved(t, "usecase-beta\ndirection LR\ndirection TD\naccTitle: first\naccTitle:  second \naccDescr: d\n")
	if len(ds) != 0 || m.Direction != "TB" || m.AccTitle != "second" || m.AccDescr != "d" {
		t.Fatalf("%v %+v", ds, m)
	}
}

func TestBareClassSuffixEndpointIsRejected(t *testing.T) {
	_, ds := resolved(t, "usecase-beta\nactor A\nA --> B:::x\n")
	if len(ds) != 1 || ds[0].Code != "usecase/reference-class-suffix" || ds[0].Message != "endpoint B uses classes without a declaration" {
		t.Fatalf("%+v", ds)
	}
}
