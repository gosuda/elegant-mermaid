package layout

import (
	"errors"
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	"github.com/gosuda/elegant-mermaid/internal/layout/railroad"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const railroadSample = "railroad-beta\nr = sequence(terminal(\"a\"), optional(special(\"b c\"))) ;\nq = oneOrMore(nonterminal(\"r\")) ;\n"

const railroadSampleModelDump = `{"version":1,"stage":"model","kind":"railroad","profile":"vector","options":{"profile":"vector","thoroughness":3,"max_width":0,"direction":"TB","limits":{"max_nodes":2000,"max_edges":5000,"max_text_bytes":1048576}},
"boxes":[{"id":"r0","role":"group","parent":"","exclusive":false,"direction":"","shape":"rule"},
{"id":"r0.0","role":"group","parent":"r0","exclusive":false,"direction":"","shape":"sequence"},
{"id":"r0.1","role":"node","parent":"r0.0","exclusive":true,"shape":"terminal"},
{"id":"r0.2","role":"group","parent":"r0.0","exclusive":false,"direction":"","shape":"optional"},
{"id":"r0.3","role":"node","parent":"r0.2","exclusive":true,"shape":"special"},
{"id":"r1","role":"group","parent":"","exclusive":false,"direction":"","shape":"rule"},
{"id":"r1.0","role":"group","parent":"r1","exclusive":false,"direction":"","shape":"oneOrMore"},
{"id":"r1.1","role":"node","parent":"r1.0","exclusive":true,"shape":"nonterminal"}],
"routes":[{"id":"e0","from":"r0.1","to":"r0.2","orthogonal":true,"marker_end":"none"}],
"labels":[{"id":"r0.label","owner":"r0","text":"r =","lines":[]},
{"id":"r0.1.label","owner":"r0.1","text":"a","lines":[]},
{"id":"r0.3.label","owner":"r0.3","text":"? b c ?","lines":[]},
{"id":"r1.label","owner":"r1","text":"q =","lines":[]},
{"id":"r1.1.label","owner":"r1.1","text":"r","lines":[]}]}
`

func railroadDiagramInput(t *testing.T, src string, profile scene.Profile) Input {
	t.Helper()
	d := ParseDiagram([]byte(src))
	for _, diagnostic := range d.Diagnostics {
		if diagnostic.Severity == diag.SeverityError {
			t.Fatalf("diagnostic: %+v", diagnostic)
		}
	}
	in, err := d.Input(profile, scene.Options{})
	if err != nil {
		t.Fatal(err)
	}
	return in
}

func TestRailroadModelDumpGolden(t *testing.T) {
	if got := diagramModelDump(t, railroadSample); got != railroadSampleModelDump {
		t.Fatalf("got\n%s\nwant\n%s", got, railroadSampleModelDump)
	}
}

func TestRailroadInputRoundTripsThroughTheFamilyTree(t *testing.T) {
	in := railroadDiagramInput(t, railroadSample, scene.ProfileCell)
	rules, err := railroadRules(in)
	if err != nil {
		t.Fatal(err)
	}
	joins := railroad.Joins(rules)
	if len(joins) != len(in.Routes) {
		t.Fatalf("%d joins for %d routes", len(joins), len(in.Routes))
	}
	for i, join := range joins {
		if r := in.Routes[i]; r.ID != join.ID || r.From != join.From || r.To != join.To {
			t.Fatalf("route %d %+v differs from join %+v", i, r, join)
		}
	}
	if len(rules) != 2 || rules[0].Title != "r =" || rules[1].Root.Kind != railroad.KindOneOrMore {
		t.Fatalf("%+v", rules)
	}
}

func TestRailroadLayoutsSatisfyTheHardConstraints(t *testing.T) {
	sources := []string{
		railroadSample,
		"railroad-ebnf-beta\nr = a , ( b | c d )* - e , [ f ] , { g } , ? h ? , i+ ;\n",
		"railroad-abnf-beta\nr = 1*3a / 2[b c] / *(d / e) ;\n",
		"railroad-peg-beta\nr <- &a !(b / c)+ d? e* . ;\n",
		"railroad-beta\ntitle Empty\n",
	}
	for _, src := range sources {
		for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
			in := railroadDiagramInput(t, src, profile)
			s, _, err := Layout(in)
			if err != nil {
				t.Fatal(err)
			}
			clause, failed, err := s.Validate()
			if err != nil || failed {
				t.Fatalf("%q %v: %v %v", src, profile, clause, err)
			}
		}
	}
}

func TestRailroadLabelsAreOnlyRuleTitles(t *testing.T) {
	in := railroadDiagramInput(t, railroadSample, scene.ProfileCell)
	s, _, err := Layout(in)
	if err != nil {
		t.Fatal(err)
	}
	var owners []string
	for _, l := range s.Labels {
		owners = append(owners, l.Owner)
	}
	if strings.Join(owners, ",") != "r0,r1" {
		t.Fatalf("label owners %v", owners)
	}
}

func TestRailroadRejectsModelsOverTheLimits(t *testing.T) {
	in := railroadDiagramInput(t, railroadSample, scene.ProfileCell)
	in.Options.Limits.MaxNodes = 3
	_, _, err := Layout(in)
	limit, ok := errors.AsType[*layered.LimitError](err)
	if !ok || limit.Resource != "nodes" || limit.Actual != 8 {
		t.Fatalf("got %v", err)
	}
	in = railroadDiagramInput(t, railroadSample, scene.ProfileCell)
	in.Options.Limits.MaxTextBytes = 4
	if _, _, err := Layout(in); !errors.Is(err, layered.ErrTooLarge) {
		t.Fatalf("got %v", err)
	}
}

func TestRailroadRejectsAmbiguousOwners(t *testing.T) {
	in := railroadDiagramInput(t, railroadSample, scene.ProfileCell)
	in.Routes[0].ID = "r0.1"
	if _, _, err := Layout(in); !errors.Is(err, layered.ErrGraph) {
		t.Fatalf("got %v", err)
	}
}

func TestRailroadRejectsCyclicOrBranchingInput(t *testing.T) {
	loop := Input{Kind: railroadKind, Options: scene.DefaultOptions(), Boxes: []Box{{ID: "a", Shape: "optional"}, {ID: "a", Parent: "a", Shape: "optional"}}}
	if _, _, err := Layout(loop); !errors.Is(err, railroad.ErrArity) {
		t.Fatalf("got %v", err)
	}
	wide := Input{Kind: railroadKind, Options: scene.DefaultOptions(), Boxes: []Box{{ID: "r", Shape: ruleShape}, {ID: "x", Parent: "r"}, {ID: "y", Parent: "r"}}}
	if _, _, err := Layout(wide); !errors.Is(err, railroad.ErrArity) {
		t.Fatalf("got %v", err)
	}
}

func TestRailroadControlCharactersDisplayAsSpacesOrReplacement(t *testing.T) {
	d := ParseDiagram([]byte("railroad-beta\nr = terminal(\"a\\tb\\nc\") ;\n"))
	in, err := d.Input(scene.ProfileCell, scene.Options{})
	if err != nil {
		t.Fatal(err)
	}
	if got := in.Boxes[1].Text; got != "a b c" {
		t.Fatalf("%q", got)
	}
	if got := displayText("a\x01\u0085b"); got != "a\ufffd\ufffdb" {
		t.Fatalf("%q", got)
	}
}
