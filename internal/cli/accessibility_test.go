package cli

import (
	"encoding/xml"
	"testing"
)

func TestRenderAccessibility(t *testing.T) {
	for _, tc := range []struct{ name, metadata, title, description string }{
		{"fallback", "", "Mermaid flowchart diagram", ""},
		{"inline", "accTitle: Build & deploy <pipeline>\naccDescr: Inputs & outputs <safe>\n", "Build & deploy <pipeline>", "Inputs & outputs <safe>"},
		{"block", "accTitle: Pipeline\naccDescr {first & second <stage>}\n", "Pipeline", "first & second <stage>"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			out, stderr, code := invoke(t, "flowchart LR\n"+tc.metadata+"A --> B\n", "render", "-e", "svg", "--color", "never")
			if code != 0 || stderr != "" {
				t.Fatalf("exit=%d stderr=%q", code, stderr)
			}
			assertSVGAccessibility(t, out, tc.title, tc.description)
		})
	}
}

func assertSVGAccessibility(t *testing.T, out, title, description string) {
	t.Helper()
	var svg struct {
		LabelledBy  string `xml:"aria-labelledby,attr"`
		DescribedBy string `xml:"aria-describedby,attr"`
		Title       struct {
			ID   string `xml:"id,attr"`
			Text string `xml:",chardata"`
		} `xml:"title"`
		Description struct {
			ID   string `xml:"id,attr"`
			Text string `xml:",chardata"`
		} `xml:"desc"`
	}
	if err := xml.Unmarshal([]byte(out), &svg); err != nil {
		t.Fatal(err)
	}
	if svg.Title.Text != title || svg.Title.ID == "" || svg.LabelledBy != svg.Title.ID {
		t.Fatalf("title: %+v", svg)
	}
	if svg.Description.Text != description || svg.DescribedBy != svg.Description.ID {
		t.Fatalf("description: %+v", svg)
	}
	if description != "" && svg.DescribedBy == "" {
		t.Fatal("description is not referenced")
	}
}
