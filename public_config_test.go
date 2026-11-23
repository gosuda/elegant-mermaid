package mermaid_test

import (
	"bytes"
	"encoding/json"
	"errors"
	"fmt"
	"reflect"
	"strings"
	"testing"

	mermaid "github.com/gosuda/elegant-mermaid"
)

func TestPublicConfigDefaultTextLimit(t *testing.T) {
	const prefix = "flowchart LR\n%% "
	for _, size := range []int{50000, 50001} {
		t.Run(fmt.Sprint(size), func(t *testing.T) {
			text := prefix + strings.Repeat("x", size-len(prefix))
			document := mermaid.Parse([]byte(text))
			if size == 50000 {
				if document.HasErrors() {
					t.Fatalf("source at limit rejected: %+v", document.Diagnostics())
				}
				return
			}
			diagnostic := requireConfigDiagnostic(t, document, "limit/max-text-size")
			if diagnostic.Span != (mermaid.Span{Start: 50000, End: size}) || diagnostic.Message != "source has 50001 bytes; the limit is 50000 bytes" {
				t.Fatalf("text limit diagnostic: %+v", diagnostic)
			}
		})
	}
}

func TestPublicConfigDefaultEdgeLimit(t *testing.T) {
	text := "flowchart LR\n" + strings.Repeat("A --> B\n", 501)
	document := mermaid.Parse([]byte(text))
	diagnostic := requireConfigDiagnostic(t, document, "limit/max-edges")
	start := strings.LastIndex(text, "A --> B")
	if diagnostic.Span != (mermaid.Span{Start: start, End: start + len("A --> B")}) || diagnostic.Message != "diagram has 501 edges; the limit is 500" {
		t.Fatalf("edge limit diagnostic: %+v", diagnostic)
	}
}

func TestPublicConfigEdgeLimitCountsChainAndLoop(t *testing.T) {
	text := "---\nconfig:\n  maxEdges: 2\n---\nflowchart LR\nA --> B --> C\nC --> C\n"
	document := mermaid.Parse([]byte(text))
	diagnostic := requireConfigDiagnostic(t, document, "limit/max-edges")
	start := strings.Index(text, "C --> C")
	if diagnostic.Span != (mermaid.Span{Start: start, End: start + len("C --> C")}) || diagnostic.Message != "diagram has 3 edges; the limit is 2" {
		t.Fatalf("resolved edge limit diagnostic: %+v", diagnostic)
	}
}

func TestPublicConfigOverridePreservesDocument(t *testing.T) {
	for _, tc := range []struct{ name, source, config, code string }{
		{"text", "flowchart LR\nA\n%% " + strings.Repeat("x", 50000), "maxTextSize: 60000\n", "limit/max-text-size"},
		{"edges", "---\nconfig:\n  maxEdges: 1\n---\nflowchart LR\nA --> B --> C\n", "maxEdges: 2\n", "limit/max-edges"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			document := mermaid.Parse([]byte(tc.source))
			requireConfigDiagnostic(t, document, tc.code)
			before := document.Diagnostics()
			if _, err := mermaid.RenderText(t.Context(), document, mermaid.TextOptions{LayoutOptions: mermaid.LayoutOptions{Config: []byte(tc.config)}}); err != nil {
				t.Fatalf("higher site limit must recover: %v", err)
			}
			if !reflect.DeepEqual(before, document.Diagnostics()) || string(document.Source()) != tc.source {
				t.Fatal("render mutated the document")
			}
			if _, err := mermaid.RenderText(t.Context(), document, mermaid.TextOptions{}); !errors.Is(err, mermaid.ErrInvalidDocument) {
				t.Fatalf("default render lost the original limit: %v", err)
			}
		})
	}
}

func TestPublicConfigSiteLimitCanLowerDefaults(t *testing.T) {
	document := mermaid.Parse([]byte("flowchart LR\nA --> B --> C\n"))
	for _, config := range []string{"maxEdges: 1\n", "maxTextSize: 10\n"} {
		_, err := mermaid.RenderText(t.Context(), document, mermaid.TextOptions{LayoutOptions: mermaid.LayoutOptions{Config: []byte(config)}})
		if !errors.Is(err, mermaid.ErrInvalidDocument) {
			t.Fatalf("%q: wanted invalid document, got %v", config, err)
		}
	}
}

func TestPublicConfigFontFamily(t *testing.T) {
	text := "---\nconfig:\n  fontFamily: serif\n---\nflowchart LR\nA[Alpha]\n"
	document := mermaid.Parse([]byte(text))
	diagnostic := requireConfigDiagnostic(t, document, "config/font-metrics-approximate")
	if diagnostic.Severity != mermaid.SeverityInfo || diagnostic.Message != "text width is measured with Inter; fontFamily is serif" {
		t.Fatalf("font diagnostic: %+v", diagnostic)
	}
	svg, err := mermaid.RenderSVG(t.Context(), document, mermaid.SVGOptions{})
	if err != nil || !bytes.Contains(svg, []byte("font-family='serif'")) {
		t.Fatalf("font family was not emitted: %v, %s", err, svg)
	}
	plain, err := mermaid.RenderTextSource(t.Context(), []byte("flowchart LR\nA[Alpha]\n"), mermaid.TextOptions{})
	if err != nil {
		t.Fatal(err)
	}
	configured, err := mermaid.RenderText(t.Context(), document, mermaid.TextOptions{})
	if err != nil || !bytes.Equal(plain, configured) {
		t.Fatalf("font family changed cell measurement: %v", err)
	}
}

func TestPublicConfigFontWidthFactor(t *testing.T) {
	document := mermaid.Parse([]byte("flowchart TB\nA -->|Alpha| B\n"))
	plain, err := mermaid.Layout(t.Context(), document, mermaid.LayoutOptions{})
	if err != nil {
		t.Fatal(err)
	}
	configured, err := mermaid.Layout(t.Context(), document, mermaid.LayoutOptions{Config: []byte("fontFamily: serif\n")})
	if err != nil {
		t.Fatal(err)
	}
	width := configLabelWidth(t, plain, "e0.label")
	if got, want := configLabelWidth(t, configured, "e0.label"), width*108/100; got != want {
		t.Fatalf("configured width = %d; want floor(%d * 108 / 100) = %d", got, width, want)
	}
}

func configLabelWidth(t *testing.T, scene *mermaid.Scene, id string) int {
	t.Helper()
	var dump struct {
		Labels []struct {
			ID string `json:"id"`
			W  int    `json:"w"`
		} `json:"labels"`
	}
	if err := json.Unmarshal(scene.Dump(), &dump); err != nil {
		t.Fatal(err)
	}
	for _, label := range dump.Labels {
		if label.ID == id {
			return label.W
		}
	}
	t.Fatalf("missing label %s: %s", id, scene.Dump())
	return 0
}

func requireConfigDiagnostic(t *testing.T, document *mermaid.Document, code string) mermaid.Diagnostic {
	t.Helper()
	for _, diagnostic := range document.Diagnostics() {
		if diagnostic.Code == code {
			return diagnostic
		}
	}
	t.Fatalf("missing %s: %+v", code, document.Diagnostics())
	return mermaid.Diagnostic{}
}
