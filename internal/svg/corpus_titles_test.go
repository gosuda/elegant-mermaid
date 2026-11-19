package svg_test

import (
	"context"
	"encoding/json"
	"encoding/xml"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"

	mermaid "github.com/gosuda/elegant-mermaid"
)

func readCorpusJSON(t *testing.T, root, name string, value any) {
	t.Helper()
	data, err := os.ReadFile(filepath.Join(root, "corpus", name))
	if err != nil {
		t.Fatal(err)
	}
	if err := json.Unmarshal(data, value); err != nil {
		t.Fatal(err)
	}
}

func corpusFixtures(t *testing.T, root string) []string {
	t.Helper()
	var verdicts map[string]json.RawMessage
	readCorpusJSON(t, root, "verdicts.json", &verdicts)
	var paths []string
	for path := range verdicts {
		paths = append(paths, path)
	}
	slices.Sort(paths)
	return paths
}

func assertTitleReferenced(t *testing.T, parsed *mermaid.Document) {
	t.Helper()
	output, err := mermaid.RenderSVG(context.Background(), parsed, mermaid.SVGOptions{})
	if err != nil {
		t.Fatal(err)
	}
	var document struct {
		XMLName    xml.Name `xml:"svg"`
		LabelledBy string   `xml:"aria-labelledby,attr"`
		Titles     []struct {
			ID   string `xml:"id,attr"`
			Text string `xml:",chardata"`
		} `xml:"title"`
	}
	if err := xml.Unmarshal(output, &document); err != nil {
		t.Fatal(err)
	}
	for _, title := range document.Titles {
		if title.ID != "" && title.ID == document.LabelledBy && strings.TrimSpace(title.Text) != "" {
			return
		}
	}
	t.Fatal("SVG has no non-empty title referenced by aria-labelledby")
}

func TestCorpusSVGTitles(t *testing.T) {
	root := filepath.Join("..", "..")
	paths := corpusFixtures(t, root)
	if len(paths) == 0 {
		t.Fatal("no accepted corpus fixtures")
	}
	accepted := 0
	for _, path := range paths {
		source, err := os.ReadFile(filepath.Join(root, path))
		if err != nil {
			t.Fatal(err)
		}
		parsed := mermaid.Parse(source)
		if parsed.HasErrors() {
			continue
		}
		accepted++
		t.Run(path, func(t *testing.T) { assertTitleReferenced(t, parsed) })
	}
	if accepted == 0 {
		t.Fatal("parser accepted no corpus fixtures")
	}
}
