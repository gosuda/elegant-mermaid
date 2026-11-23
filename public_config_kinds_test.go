package mermaid_test

import (
	"encoding/json"
	"reflect"
	"slices"
	"testing"

	mermaid "github.com/gosuda/elegant-mermaid"
)

type configKindCase struct{ kind, source string }

func configNonedgeFixtures() []configKindCase {
	return []configKindCase{
		{"xychart", "xychart\nx-axis [Alpha, Beta]\nbar [1, 2]\n"},
		{"timeline", "timeline\ntitle History\n1 : First\n"},
		{"railroad", "railroad-beta\nr = terminal(\"Alpha\") ;\n"},
		{"radar", "radar-beta\naxis Alpha, Beta, Gamma\ncurve c{1, 2, 3}\n"},
		{"info", "info showInfo\n"},
		{"packet", "packet\ntitle Packet\n0-7: \"Alpha\"\n"},
		{"kanban", "kanban\n  todo[To Do]\n    a[Task Alpha]\n"},
		{"pie", "pie\ntitle Portions\n\"Alpha\" : 1\n\"Beta\" : 2\n"},
		{"quadrant", "quadrantChart\ntitle Priorities\nAlpha: [0.25, 0.75]\n"},
		{"journey", "journey\ntitle My day\nsection Go\n  Make tea: 5: Me\n"},
		{"gantt", "gantt\ndateFormat YYYY-MM-DD\nFirst :a, 2024-01-01, 1d\nSecond :b, after a, 1d\n"},
		{"venn", "venn-beta\ntitle Skills\nset A[\"Alpha\"]:10\nset B[\"Beta\"]:6\nunion A,B[\"Shared\"]:3\n"},
		{"treemap", "treemap-beta\n\"Root\"\n  \"Leaf\": 10\n"},
	}
}

func TestPublicConfigZeroEdgesAllowsNonedgeKinds(t *testing.T) {
	for _, tc := range configNonedgeFixtures() {
		t.Run(tc.kind, func(t *testing.T) {
			document := mermaid.Parse([]byte("---\nconfig:\n  maxEdges: 0\n---\n" + tc.source))
			assertConfigKind(t, document, tc.kind)
		})
	}
}

func TestPublicConfigFontSurvivesEveryKind(t *testing.T) {
	cases := configNonedgeFixtures()
	for _, tc := range configEdgeFixtures() {
		cases = append(cases, configKindCase{kind: tc.kind, source: tc.source})
	}
	seen := make(map[string]bool, len(cases))
	for _, tc := range cases {
		if seen[tc.kind] {
			t.Fatalf("duplicate kind %s", tc.kind)
		}
		seen[tc.kind] = true
		t.Run(tc.kind, func(t *testing.T) {
			document := mermaid.Parse([]byte(tc.source))
			assertConfigKind(t, document, tc.kind)
			assertKindFontProfile(t, document, tc.kind, mermaid.ProfileVector)
			assertKindFontProfile(t, document, tc.kind, mermaid.ProfileCell)
		})
	}
	if len(seen) != 33 {
		t.Fatalf("covered %d kinds, want 33", len(seen))
	}
}

func assertConfigKind(t *testing.T, document *mermaid.Document, want string) {
	t.Helper()
	kind, found := document.Kind()
	if !found || kind.String() != want || document.HasErrors() {
		t.Fatalf("invalid %s fixture: kind=%s found=%t diagnostics=%+v", want, kind, found, document.Diagnostics())
	}
}

type configKindDump struct {
	Profile string `json:"profile"`
	Options struct {
		FontFamily string `json:"fontFamily"`
	} `json:"options"`
	Canvas json.RawMessage `json:"canvas"`
	Boxes  json.RawMessage `json:"boxes"`
	Routes json.RawMessage `json:"routes"`
	Labels json.RawMessage `json:"labels"`
}

func configLayoutDump(t *testing.T, document *mermaid.Document, profile mermaid.Profile, config string) configKindDump {
	t.Helper()
	scene, err := mermaid.Layout(t.Context(), document, mermaid.LayoutOptions{Profile: profile, Config: []byte(config)})
	if err != nil {
		t.Fatal(err)
	}
	var dump configKindDump
	if err := json.Unmarshal(scene.Dump(), &dump); err != nil {
		t.Fatal(err)
	}
	return dump
}

func assertKindFontProfile(t *testing.T, document *mermaid.Document, kind string, profile mermaid.Profile) {
	t.Helper()
	before := configLayoutDump(t, document, profile, "")
	after := configLayoutDump(t, document, profile, "fontFamily: Example\n")
	if after.Options.FontFamily != "Example" || before.Profile != after.Profile {
		t.Fatalf("lost shared font or profile: before=%+v after=%+v", before.Options, after.Options)
	}
	if after.Profile == "cell" {
		after.Options.FontFamily = ""
		if !reflect.DeepEqual(before, after) {
			t.Fatalf("font changed cell geometry for %s", kind)
		}
	} else if profile == mermaid.ProfileCell && !slices.Contains([]string{"pie", "radar", "sankey", "venn"}, kind) {
		t.Fatalf("%s unexpectedly uses vector geometry for text", kind)
	}
}
