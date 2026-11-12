package mermaid_test

import (
	"bytes"
	"context"
	"errors"
	"strings"
	"testing"

	mermaid "github.com/gosuda/elegant-mermaid"
)

func TestPublicSourceOwnershipAndPositions(t *testing.T) {
	src := []byte("flowchart TD\r\nA[é]\rB[x]\n")
	d := mermaid.Parse(src)
	if &d.Source()[0] != &src[0] {
		t.Fatal("valid source was copied")
	}
	at := bytes.Index(src, []byte("é"))
	if got := d.Position(at + 1); got != (mermaid.Position{Line: 2, Column: 3}) {
		t.Fatalf("interior scalar position: %+v", got)
	}
	if got := d.Position(-5); got != (mermaid.Position{Line: 1, Column: 1}) {
		t.Fatalf("negative clamp: %+v", got)
	}
	if got := d.Position(len(src) + 20); got != (mermaid.Position{Line: 4, Column: 1}) {
		t.Fatalf("end clamp: %+v", got)
	}
}

func TestPublicInvalidSourceOwnership(t *testing.T) {
	invalid := append([]byte("flowchart TD\nA["), 0xe2, 0x82)
	repaired := mermaid.Parse(invalid)
	if !bytes.HasSuffix(repaired.Source(), []byte("�")) {
		t.Fatalf("maximal-subpart repair: %q", repaired.Source())
	}
	invalid[0] = 'X'
	if repaired.Source()[0] != 'f' {
		t.Fatal("repaired source aliases caller")
	}
	found := false
	for _, diagnostic := range repaired.Diagnostics() {
		if diagnostic.Code == "source/invalid-utf8" {
			found = true
			if diagnostic.Span.End > len(repaired.Source()) {
				t.Fatal("invalid repaired span")
			}
		}
	}
	if !found {
		t.Fatal("missing encoding diagnostic")
	}
}

func TestPublicDiagnosticOwnership(t *testing.T) {
	d := mermaid.Parse([]byte("flowchart TD\nA -> B\n"))
	first := d.Diagnostics()
	if len(first) == 0 {
		t.Fatal("expected syntax diagnostic")
	}
	first[0].Message = "changed"
	mutateDiagnosticDetails(first)
	for _, v := range d.Diagnostics() {
		if v.Message == "changed" {
			t.Fatal("diagnostics alias document")
		}
		assertDiagnosticFixOwnership(t, v.Fixes)
	}
}

func mutateDiagnosticDetails(diagnostics []mermaid.Diagnostic) {
	for i := range diagnostics {
		for j := range diagnostics[i].Related {
			diagnostics[i].Related[j].Message = "changed"
		}
		for j := range diagnostics[i].Fixes {
			fix := &diagnostics[i].Fixes[j]
			fix.Title = "changed"
			for k := range fix.Edits {
				fix.Edits[k].NewText = "changed"
			}
		}
	}
}

func assertDiagnosticFixOwnership(t *testing.T, fixes []mermaid.Fix) {
	t.Helper()
	for _, f := range fixes {
		if f.Title == "changed" {
			t.Fatal("fix aliases document")
		}
		for _, e := range f.Edits {
			if e.NewText == "changed" {
				t.Fatal("edit aliases document")
			}
		}
	}
}

func TestPublicRenderBoundary(t *testing.T) {
	d := mermaid.Parse([]byte("flowchart LR\naccTitle: Public title\naccDescr: Public description\nA[Alpha] --> B[Beta]\n"))
	svg, err := mermaid.RenderSVG(t.Context(), d, mermaid.SVGOptions{LayoutOptions: mermaid.LayoutOptions{Profile: mermaid.ProfileCell}, IDPrefix: "test"})
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{"Public title", "Public description", "Alpha", "Beta", "aria-labelledby='testtitle'"} {
		if !bytes.Contains(svg, []byte(want)) {
			t.Fatalf("missing SVG content %q", want)
		}
	}
	text, err := mermaid.RenderText(t.Context(), d, mermaid.TextOptions{})
	if err != nil || !bytes.Contains(text, []byte("Alpha")) {
		t.Fatalf("text render: %q, %v", text, err)
	}
}

func TestPublicSceneDumpOwnership(t *testing.T) {
	d := mermaid.Parse([]byte("flowchart LR\nA[Alpha] --> B[Beta]\n"))
	s, err := mermaid.Layout(t.Context(), d, mermaid.LayoutOptions{})
	if err != nil {
		t.Fatal(err)
	}
	dump := s.Dump()
	dump[0] = 'X'
	if s.Dump()[0] != '{' {
		t.Fatal("dump aliases scene")
	}
}

func TestPublicRenderErrors(t *testing.T) {
	d := mermaid.Parse([]byte("flowchart LR\nA[Alpha] --> B[Beta]\n"))
	ctx, cancel := context.WithCancel(t.Context())
	cancel()
	if _, err := mermaid.RenderSVG(ctx, d, mermaid.SVGOptions{}); err != context.Canceled {
		t.Fatalf("cancel identity: %v", err)
	}
	for _, o := range []mermaid.LayoutOptions{{Thoroughness: -1}, {Thoroughness: 6}, {MaxWidth: -1}, {Limits: mermaid.Limits{MaxEdges: -1}}, {Theme: "missing"}, {Config: []byte("[1, 2]")}} {
		if _, err := mermaid.Layout(t.Context(), d, o); !errors.Is(err, mermaid.ErrBadConfig) {
			t.Fatalf("option boundary: %v", err)
		}
	}
	if _, err := mermaid.Layout(t.Context(), d, mermaid.LayoutOptions{Limits: mermaid.Limits{MaxNodes: 1}}); !errors.Is(err, mermaid.ErrTooLarge) {
		t.Fatalf("limit boundary: %v", err)
	}
	bad := mermaid.Parse([]byte("flowchart TD\nA["))
	if _, err := mermaid.RenderText(t.Context(), bad, mermaid.TextOptions{}); !errors.Is(err, mermaid.ErrInvalidDocument) {
		t.Fatalf("invalid document boundary: %v", err)
	}
}

func TestPublicConfigBoundary(t *testing.T) {
	d := mermaid.Parse([]byte("flowchart TD\nA[Alpha]\n"))
	for _, config := range []string{"", " \t\r\n ", "# empty mapping\n", "{}", "layout: elk\n", "flowchart:\n  nodeSpacing: 40\n", "themeVariables: {primaryColor: '#abc'}\n"} {
		t.Run(config, func(t *testing.T) {
			if _, err := mermaid.Layout(t.Context(), d, mermaid.LayoutOptions{Config: []byte(config)}); err != nil {
				t.Fatalf("valid config rejected: %v", err)
			}
		})
	}
	for _, config := range [][]byte{[]byte("null"), []byte("plain scalar"), []byte("[1, 2]"), []byte("theme: ["), {0xff}} {
		if _, err := mermaid.Layout(t.Context(), d, mermaid.LayoutOptions{Config: config}); !errors.Is(err, mermaid.ErrBadConfig) {
			t.Fatalf("invalid config %q: %v", config, err)
		}
	}
}

func TestPublicLayoutDefaults(t *testing.T) {
	d := mermaid.Parse([]byte("flowchart TD\nA\n"))
	s, err := mermaid.Layout(t.Context(), d, mermaid.LayoutOptions{Limits: mermaid.Limits{MaxNodes: 7}})
	if err != nil {
		t.Fatal(err)
	}
	want := `"options":{"profile":"vector","thoroughness":3,"max_width":0,"direction":"TB","limits":{"max_nodes":7,"max_edges":5000,"max_text_bytes":1048576}}`
	if !bytes.Contains(s.Dump(), []byte(want)) {
		t.Fatalf("field-wise defaults missing from dump: %s", s.Dump())
	}
}

func TestPublicErrorPrecedenceAndEnums(t *testing.T) {
	valid := mermaid.Parse([]byte("flowchart TD\nA\n"))
	invalid := mermaid.Parse([]byte("flowchart TD\nA["))
	calls := []struct {
		name   string
		render func(context.Context, *mermaid.Document) error
	}{
		{"layout", func(ctx context.Context, d *mermaid.Document) error {
			_, err := mermaid.Layout(ctx, d, mermaid.LayoutOptions{Profile: 255})
			return err
		}},
		{"svg", func(ctx context.Context, d *mermaid.Document) error {
			_, err := mermaid.RenderSVG(ctx, d, mermaid.SVGOptions{Text: 255})
			return err
		}},
		{"text charset", func(ctx context.Context, d *mermaid.Document) error {
			_, err := mermaid.RenderText(ctx, d, mermaid.TextOptions{Charset: 255})
			return err
		}},
		{"text color", func(ctx context.Context, d *mermaid.Document) error {
			_, err := mermaid.RenderText(ctx, d, mermaid.TextOptions{Color: 255})
			return err
		}},
	}
	for _, call := range calls {
		t.Run(call.name, func(t *testing.T) {
			if err := call.render(t.Context(), valid); !errors.Is(err, mermaid.ErrBadConfig) {
				t.Fatalf("invalid enum: %v", err)
			}
			if err := call.render(t.Context(), invalid); !errors.Is(err, mermaid.ErrInvalidDocument) {
				t.Fatalf("document must precede options: %v", err)
			}
			ctx, cancel := context.WithCancel(t.Context())
			cancel()
			if err := call.render(ctx, invalid); err != ctx.Err() {
				t.Fatalf("context identity and precedence: %v", err)
			}
		})
	}
}

func TestPublicMarkdownMapping(t *testing.T) {
	host := []byte("> ```mermaid\n> flowchart TD\n> A[Alpha]\n> ```\n")
	blocks := mermaid.MarkdownBlocks(host)
	if len(blocks) != 1 {
		t.Fatalf("blocks: %d", len(blocks))
	}
	b := blocks[0]
	at := strings.Index(string(b.Source), "Alpha")
	if b.HostOffset(at) != bytes.Index(host, []byte("Alpha")) {
		t.Fatal("container host mapping")
	}
	b.Source[0] = 'X'
	if host[bytes.Index(host, []byte("flowchart"))] != 'f' {
		t.Fatal("container block aliases host")
	}
	top := []byte("```mermaid\nflowchart TD\n```\n")
	plain := mermaid.MarkdownBlocks(top)
	if len(plain) != 1 || &plain[0].Source[0] != &top[len("```mermaid\n")] {
		t.Fatal("top-level block must borrow")
	}
}
