package cli

import (
	"bytes"
	"fmt"
	"image"
	"image/color"
	"image/png"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

const pngSource = "flowchart LR\n  A[Start] --> B{Choice}\n  B -->|yes| C[Done]\n  B -->|no| A\n"

func decodePNG(t *testing.T, data []byte) image.Image {
	t.Helper()
	img, err := png.Decode(bytes.NewReader(data))
	if err != nil {
		t.Fatalf("not a PNG: %v", err)
	}
	return img
}

func renderPNG(t *testing.T, args ...string) image.Image {
	t.Helper()
	out, stderr, code := invoke(t, pngSource, append([]string{"render", "-e", "png"}, args...)...)
	if code != 0 || stderr != "" {
		t.Fatalf("%v: exit %d, stderr %q", args, code, stderr)
	}
	return decodePNG(t, []byte(out))
}

func TestRenderPNGStdoutScale(t *testing.T) {
	one := renderPNG(t, "-s", "1").Bounds().Size()
	two := renderPNG(t).Bounds().Size()
	if one.X == 0 || one.Y == 0 {
		t.Fatalf("empty image %v", one)
	}
	if two.X < 2*one.X-1 || two.X > 2*one.X || two.Y < 2*one.Y-1 || two.Y > 2*one.Y {
		t.Fatalf("scale 2 size %v is not twice scale 1 size %v", two, one)
	}
	if got := renderPNG(t, "-s", "2").Bounds().Size(); got != two {
		t.Fatalf("explicit scale 2 %v != default %v", got, two)
	}
}

func TestRenderPNGBackgroundAndTheme(t *testing.T) {
	red := color.NRGBAModel.Convert(renderPNG(t, "-b", "#ff0000").At(0, 0)).(color.NRGBA)
	if red != (color.NRGBA{R: 255, A: 255}) {
		t.Fatalf("background pixel %v", red)
	}
	light := color.NRGBAModel.Convert(renderPNG(t, "-t", "elegant-light").At(0, 0))
	dark := color.NRGBAModel.Convert(renderPNG(t, "-t", "elegant-dark").At(0, 0))
	if light == dark {
		t.Fatalf("theme did not change the background: %v", light)
	}
}

func TestRenderPNGFileInference(t *testing.T) {
	dir := t.TempDir()
	src := filepath.Join(dir, "demo.mmd")
	if err := os.WriteFile(src, []byte(pngSource), 0o600); err != nil {
		t.Fatal(err)
	}
	for _, c := range []struct {
		name string
		args []string
	}{{"inferred", []string{"render", src, "-o", filepath.Join(dir, "inferred.png")}}, {"explicit", []string{"render", src, "-e", "png", "-o", filepath.Join(dir, "explicit.out")}}} {
		_, stderr, code := invoke(t, "", c.args...)
		if code != 0 || stderr != "" {
			t.Fatalf("%s: exit %d, stderr %q", c.name, code, stderr)
		}
	}
	for _, name := range []string{"inferred.png", "explicit.out"} {
		data, err := os.ReadFile(filepath.Join(dir, name))
		if err != nil {
			t.Fatal(err)
		}
		if img := decodePNG(t, data); img.Bounds().Dx() == 0 {
			t.Fatalf("%s: empty image", name)
		}
	}
}

func TestRenderPNGPixelLimit(t *testing.T) {
	var src strings.Builder
	src.WriteString("flowchart LR\n")
	for i := range 400 {
		fmt.Fprintf(&src, "  N%d --> N%d\n", i, i+1)
	}
	out, stderr, code := invoke(t, src.String(), "render", "-e", "png", "-s", "8")
	if code != 1 || out != "" || !strings.Contains(stderr, "image is too large:") {
		t.Fatalf("exit %d, stdout %d bytes, stderr %q", code, len(out), stderr)
	}
}

func expectOutlinedText(t *testing.T, paths string) {
	t.Helper()
	if strings.Contains(paths, "<text") || strings.Contains(paths, "<tspan") {
		t.Fatalf("paths mode kept text elements:\n%s", paths)
	}
	if got := strings.Count(paths, "<path class='emd-s-text' d='M"); got < 4 {
		t.Fatalf("paths mode drew %d text paths, want one per label of the sample", got)
	}
	if !strings.Contains(paths, "<title id='title'>Mermaid flowchart diagram</title>") {
		t.Fatalf("paths mode lost the title:\n%s", paths)
	}
}

func TestRenderSVGTextPaths(t *testing.T) {
	font, stderr, code := invoke(t, pngSource, "render", "-e", "svg")
	if code != 0 || stderr != "" || !strings.Contains(font, "<text ") {
		t.Fatalf("font mode: exit %d, stderr %q", code, stderr)
	}
	explicit, _, code := invoke(t, pngSource, "render", "-e", "svg", "--svg-text", "font")
	if code != 0 || explicit != font {
		t.Fatalf("explicit font mode differs: exit %d", code)
	}
	paths, stderr, code := invoke(t, pngSource, "render", "-e", "svg", "--svg-text", "paths")
	if code != 0 || stderr != "" {
		t.Fatalf("paths mode: exit %d, stderr %q", code, stderr)
	}
	expectOutlinedText(t, paths)
}
