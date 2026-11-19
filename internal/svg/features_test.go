package svg_test

import (
	"bytes"
	"errors"
	"strings"
	"testing"

	mermaid "github.com/gosuda/elegant-mermaid"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/icon"
	"github.com/gosuda/elegant-mermaid/internal/layout"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/svg"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
)

const packJSON = `{"prefix":"p","icons":{"a":{"body":"<path fill=\"currentColor\" d=\"M0 0h24v24H0z\"/>","width":24,"height":24},"arc":{"body":"<path d=\"M0 0A1 1 0 0 1 2 2\"/>"}}}`

func iconScene(items []scene.Primitive) scene.Scene {
	return scene.Scene{Dump: scene.Dump{Canvas: geom.Size{W: 4096, H: 4096}}, Groups: []*scene.Group{{Role: scene.GroupRoleNode, Owner: "n", Items: items}}}
}

func renderIcon(t *testing.T, packs []*icon.Pack, name string) (string, icon.Drawing) {
	t.Helper()
	drawing := icon.Draw(packs, name, geom.Point{X: 640, Y: 640}, scene.ProfileVector)
	var out bytes.Buffer
	if err := svg.Write(&out, iconScene(drawing.Items), svg.Options{Kind: "flowchart"}); err != nil {
		t.Fatal(err)
	}
	return out.String(), drawing
}

func assertMissingIcon(t *testing.T, packs []*icon.Pack, unknown, name string) {
	t.Helper()
	got, drawing := renderIcon(t, packs, name)
	if !drawing.Missing {
		t.Errorf("%s: resolved", name)
	}
	if got != unknown {
		t.Errorf("%s: output differs from the unknown icon", name)
	}
	d := icon.MissingDiagnostic(name, source.Span{Start: 4, End: 9})
	if d.Code != "icon/pack-missing" || d.Severity.String() != "info" || !strings.Contains(d.Message, name) || d.Help == "" {
		t.Errorf("%s: %+v", name, d)
	}
}

func assertResolvedIcon(t *testing.T, packs []*icon.Pack, unknown, name string) {
	t.Helper()
	got, drawing := renderIcon(t, packs, name)
	if drawing.Missing {
		t.Errorf("%s: reported missing", name)
	}
	if name != "unknown" && got == unknown {
		t.Errorf("%s: drew the unknown icon", name)
	}
}

func TestIconPackMissing(t *testing.T) {
	pack, err := icon.Parse([]byte(packJSON))
	if err != nil {
		t.Fatal(err)
	}
	packs := []*icon.Pack{pack}
	unknown, _ := renderIcon(t, nil, "unknown")
	for _, name := range []string{"p:absent", "q:a", "absent", "p:arc"} {
		assertMissingIcon(t, packs, unknown, name)
	}
	for _, name := range []string{"p:a", "cloud", "database", "disk", "internet", "server", "unknown"} {
		assertResolvedIcon(t, packs, unknown, name)
	}
	if !strings.Contains(unknown, "<path class='emd-s-ink' d='M ") || strings.Contains(unknown, "foreignObject") {
		t.Errorf("unknown icon output: %s", unknown)
	}
}

func TestIconPacksReachLayout(t *testing.T) {
	pack, err := mermaid.ParseIconPack([]byte(packJSON))
	if err != nil {
		t.Fatal(err)
	}
	d := mermaid.Parse([]byte("flowchart LR\n  A --> B\n"))
	if _, err := mermaid.Layout(t.Context(), d, mermaid.LayoutOptions{IconPacks: []*mermaid.IconPack{pack}}); err != nil {
		t.Fatal(err)
	}
	if _, err := mermaid.Layout(t.Context(), d, mermaid.LayoutOptions{IconPacks: []*mermaid.IconPack{nil}}); !errors.Is(err, mermaid.ErrBadConfig) {
		t.Errorf("nil pack: %v", err)
	}
	for _, data := range []string{"{", `{"prefix":"p"}`, "{\"prefix\":\"p\",\"icons\":{\"a\":{\"body\":\"\xff\"}}}"} {
		if _, err := mermaid.ParseIconPack([]byte(data)); !errors.Is(err, mermaid.ErrBadIconPack) {
			t.Errorf("%q: %v", data, err)
		}
	}
}

const clickSource = "flowchart LR\n  A --> B\n  click A \"javascript:alert(1)\" \"danger\"\n  click B \"HTTPS://example.test/b?x=1&y=2\" \"Open <b>\"\n"

func renderClicks(t *testing.T, src string) (string, *layout.Diagram) {
	t.Helper()
	d := layout.ParseDiagram([]byte(src))
	in, err := d.Input(scene.ProfileVector, scene.Options{})
	if err != nil {
		t.Fatal(err)
	}
	s, _, err := layout.Layout(in)
	if err != nil {
		t.Fatal(err)
	}
	look, err := d.Look(syntax.ConfigValue{})
	if err != nil {
		t.Fatal(err)
	}
	var out bytes.Buffer
	if err := svg.Write(&out, s, svg.Options{Kind: d.Kind, Links: d.Links(), Look: look}); err != nil {
		t.Fatal(err)
	}
	return out.String(), d
}

func assertUnsafeURLDiagnostics(t *testing.T, d *layout.Diagram) {
	t.Helper()
	var unsafe []string
	for _, diagnostic := range d.Diagnostics {
		if diagnostic.Code != "interaction/unsafe-url" {
			continue
		}
		unsafe = append(unsafe, string(d.Source[diagnostic.Span.Start:diagnostic.Span.End]))
		if diagnostic.Severity.String() != "warning" || diagnostic.Message != "link URL is not allowed" || diagnostic.Help != "Use an http, https, or mailto link." {
			t.Errorf("%+v", diagnostic)
		}
	}
	if len(unsafe) != 1 || unsafe[0] != `"javascript:alert(1)"` {
		t.Fatalf("unsafe-url diagnostics cover %q", unsafe)
	}
}

func TestInteractionUnsafeURL(t *testing.T) {
	out, d := renderClicks(t, clickSource)
	assertUnsafeURLDiagnostics(t, d)
	if strings.Contains(out, "javascript") || strings.Contains(out, "danger") || strings.Count(out, "<a ") != 1 {
		t.Fatalf("an unsafe link must not reach the SVG:\n%s", out)
	}
	anchored := anchoredBlock(t, out)
	if !strings.HasPrefix(anchored, "href='HTTPS://example.test/b?x=1&amp;y=2'>\n<title>Open &lt;b&gt;</title>\n<g class='emd-node' ") || !strings.Contains(anchored, ">B</tspan>") || strings.Contains(anchored, ">A</tspan>") {
		t.Errorf("anchor wraps the wrong group:\n%s", anchored)
	}
}

func TestInteractionCallbacksAreIgnored(t *testing.T) {
	src := "flowchart LR\n  A --> B\n  click A call fn(1, 2)\n  click B plain \"tip\"\n"
	out, d := renderClicks(t, src)
	var got []string
	for _, diagnostic := range d.Diagnostics {
		if diagnostic.Code == "interaction/callback-ignored" {
			got = append(got, diagnostic.Message+"@"+string(d.Source[diagnostic.Span.Start:diagnostic.Span.End]))
			if diagnostic.Severity.String() != "info" || diagnostic.Help != "Static output never runs callbacks." {
				t.Errorf("%+v", diagnostic)
			}
		}
	}
	if strings.Join(got, ";") != "callback fn is ignored@fn;callback plain is ignored@plain" {
		t.Errorf("callback diagnostics: %q", got)
	}
	if strings.Contains(out, "<a ") || len(d.Links()) != 0 {
		t.Error("a callback must not become a link")
	}
}

func anchoredBlock(t *testing.T, out string) string {
	t.Helper()
	_, anchored, found := strings.Cut(out, "<a ")
	if !found {
		t.Fatalf("no anchor in:\n%s", out)
	}
	anchored, _, _ = strings.Cut(anchored, "</a>")
	return anchored
}

func countDiagnostics(d *layout.Diagram, code string) int {
	count := 0
	for _, diagnostic := range d.Diagnostics {
		if diagnostic.Code == code {
			count++
		}
	}
	return count
}

func TestStateClickLinksWrapTheirSimpleStateOnly(t *testing.T) {
	src := "stateDiagram-v2\n  A --> B\n  click A \"https://example.test/a?x=1&y=2\" \"Open <a>\"\n  click B href \"javascript:alert(1)\"\n  state C {\n    D --> E\n  }\n  click C href \"https://example.test/c\"\n  click E href \"https://example.test/e\"\n  click D \"https://example.test/d\" \"\"\n"
	out, d := renderClicks(t, src)
	if got := strings.Count(out, "<a "); got != 3 {
		t.Fatalf("anchors = %d, want 3 (A, D, E):\n%s", got, out)
	}
	if strings.Contains(out, "javascript") || strings.Contains(out, "example.test/c") || strings.Contains(out, "<title></title>") {
		t.Fatalf("unsafe URL, composite state, or empty tooltip reached the SVG:\n%s", out)
	}
	anchored := anchoredBlock(t, out)
	if !strings.HasPrefix(anchored, "href='https://example.test/a?x=1&amp;y=2'>\n<title>Open &lt;a&gt;</title>\n<g class='emd-node' ") || !strings.Contains(anchored, ">A</tspan>") || strings.Contains(anchored, ">B</tspan>") {
		t.Errorf("anchor wraps the wrong group:\n%s", anchored)
	}
	if unsafe := countDiagnostics(d, "interaction/unsafe-url"); unsafe != 1 {
		t.Errorf("unsafe-url diagnostics = %d, want 1", unsafe)
	}
}

func TestAgentflowClickLinksWrapTheirNode(t *testing.T) {
	src := "agentflow-beta\n  A --> B\n  click A \"https://example.test/a?x=1&y=2\" \"Open <a>\"\n  click B \"javascript:alert(1)\"\n"
	out, _ := renderClicks(t, src)
	if got := strings.Count(out, "<a "); got != 1 || strings.Contains(out, "javascript") {
		t.Fatalf("anchors = %d, want 1 and no unsafe URL:\n%s", got, out)
	}
	anchored := anchoredBlock(t, out)
	if !strings.HasPrefix(anchored, "href='https://example.test/a?x=1&amp;y=2'>\n<title>Open &lt;a&gt;</title>\n<g class='emd-node' ") || !strings.Contains(anchored, ">A</tspan>") || strings.Contains(anchored, ">B</tspan>") {
		t.Errorf("anchor wraps the wrong group:\n%s", anchored)
	}
}

func TestFlowchartClickOnASubgraphDrawsNoAnchor(t *testing.T) {
	src := "flowchart LR\n  subgraph S\n    C\n  end\n  click S \"https://example.test/s\"\n  click C \"https://example.test/c\"\n"
	out, _ := renderClicks(t, src)
	if got := strings.Count(out, "<a "); got != 1 || strings.Contains(out, "example.test/s") {
		t.Fatalf("anchors = %d, want 1 (C only):\n%s", got, out)
	}
	if !strings.Contains(anchoredBlock(t, out), ">C</tspan>") {
		t.Errorf("anchor wraps the wrong group:\n%s", out)
	}
}

func TestInteractionLinksStayOutOfText(t *testing.T) {
	src := []byte(clickSource)
	d := mermaid.Parse(src)
	svgOut, err := mermaid.RenderSVG(t.Context(), d, mermaid.SVGOptions{})
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Contains(svgOut, []byte("<a href='HTTPS://example.test/b?x=1&amp;y=2'>")) || bytes.Contains(svgOut, []byte("javascript")) {
		t.Errorf("public SVG: %s", svgOut)
	}
	text, err := mermaid.RenderText(t.Context(), d, mermaid.TextOptions{})
	if err != nil {
		t.Fatal(err)
	}
	if bytes.Contains(text, []byte("example.test")) || bytes.Contains(text, []byte("<a")) {
		t.Errorf("text output carries a link: %s", text)
	}
}

func renderWithConfig(t *testing.T, src, config string) string {
	t.Helper()
	out, err := mermaid.RenderSVGSource(t.Context(), []byte(src), mermaid.SVGOptions{LayoutOptions: mermaid.LayoutOptions{Config: []byte(config)}})
	if err != nil {
		t.Fatal(err)
	}
	return string(out)
}

func assertHandDrawnSeeds(t *testing.T, body, classic string) {
	t.Helper()
	hand := renderWithConfig(t, body, "look: handDrawn\nhandDrawnSeed: 7\n")
	if hand != renderWithConfig(t, body, "look: handDrawn\nhandDrawnSeed: 7\n") || hand == classic {
		t.Error("handDrawn must be deterministic and differ from classic")
	}
	if hand == renderWithConfig(t, body, "look: handDrawn\nhandDrawnSeed: 8\n") {
		t.Error("the seed must change the drawing")
	}
}

func TestLookFromConfigLayers(t *testing.T) {
	body := "flowchart LR\n  A --> B\n"
	classic := renderWithConfig(t, body, "")
	neo := renderWithConfig(t, "---\nconfig:\n  look: neo\n---\n"+body, "")
	if neo == classic || !strings.Contains(neo, "stroke-width='2'") || strings.Contains(classic, "stroke-width='2'") {
		t.Error("frontmatter look: neo must change stroke widths")
	}
	sameAsNeo := []struct{ message, src, config string }{
		{"an init directive must select the same look as frontmatter", "%%{init: {\"look\": \"neo\"}}%%\n" + body, ""},
		{"LayoutOptions.Config must select the same look", body, "look: neo\n"},
		{"LayoutOptions.Config must override frontmatter", "---\nconfig:\n  look: classic\n---\n" + body, "look: neo\n"},
		{"an init directive must override frontmatter", "---\nconfig:\n  look: classic\n---\n%%{init: {\"look\": \"neo\"}}%%\n" + body, ""},
	}
	for _, c := range sameAsNeo {
		if got := renderWithConfig(t, c.src, c.config); got != neo {
			t.Error(c.message)
		}
	}
	assertHandDrawnSeeds(t, body, classic)
}

func TestLookConfigErrors(t *testing.T) {
	d := mermaid.Parse([]byte("---\nconfig:\n  look: handDrawn\n  handDrawnSeed: 4294967296\n---\nflowchart LR\n  A --> B\n"))
	if !d.HasErrors() {
		t.Fatal("an out-of-range seed must be an error")
	}
	diagnostics := d.Diagnostics()
	if len(diagnostics) != 1 || diagnostics[0].Code != "config/malformed" || diagnostics[0].Message != "invalid config value 4294967296 for handDrawnSeed" {
		t.Fatalf("%+v", diagnostics)
	}
	for _, config := range []string{"look: neo\nhandDrawnSeed: abc\n", "- a\n", "just text\n"} {
		_, err := mermaid.RenderSVGSource(t.Context(), []byte("flowchart LR\n  A --> B\n"), mermaid.SVGOptions{LayoutOptions: mermaid.LayoutOptions{Config: []byte(config)}})
		if !errors.Is(err, mermaid.ErrBadConfig) {
			t.Errorf("config %q: %v", config, err)
		}
	}
}
