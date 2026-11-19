package layout

import (
	"encoding/json"
	"testing"
)

func TestModelDumpIconKeyFollowsTheIconName(t *testing.T) {
	for _, tc := range []struct {
		name   string
		source string
		icon   bool
	}{
		{"named-square", "flowchart TD\n A@{ icon: \"fa:user\", form: \"square\", label: \"named\" }\n", true},
		{"empty", "flowchart TD\n A@{ icon: \"\", form: \"square\", label: \"empty\" }\n", false},
		{"bare-shape", "flowchart TD\n A@{ shape: icon, label: \"bare\" }\n", false},
		{"plain", "flowchart TD\n A[plain]\n", false},
		{"without-form", "flowchart TD\n A@{ icon: \"x:y\" }\n", true},
		{"circle", "flowchart TD\n A@{ icon: \"fa:user\", form: \"circle\", label: \"named\" }\n", true},
		{"lr-subgraph", "flowchart TB\n subgraph S\n direction LR\n A@{ icon: \"fa:user\", form: \"circle\", label: \"named\" }\n B[plain]\n A --> B\n end\n", true},
	} {
		t.Run(tc.name, func(t *testing.T) {
			dump := diagramModelDump(t, tc.source)
			var box map[string]any
			if err := json.Unmarshal([]byte(dumpRecord(t, dump, "A")), &box); err != nil {
				t.Fatal(err)
			}
			value, present := box["icon"]
			if present != tc.icon {
				t.Fatalf("icon key present = %t, want %t", present, tc.icon)
			}
			if present && value != true {
				t.Fatalf("icon = %v, want true", value)
			}
		})
	}
}

func TestLayoutStageDumpCarriesNoIconKey(t *testing.T) {
	s := layoutStageScene(t, "flowchart TD\n A@{ icon: \"fa:user\", form: \"square\", label: \"named\" }\n")
	var parsed struct {
		Boxes []map[string]any `json:"boxes"`
	}
	if err := json.Unmarshal(s.AppendJSON(nil), &parsed); err != nil {
		t.Fatal(err)
	}
	requireNoKey(t, parsed.Boxes, "icon")
}
