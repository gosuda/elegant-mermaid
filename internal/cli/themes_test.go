package cli

import (
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"os"
	"slices"
	"strings"
	"testing"
)

type specTheme struct {
	Name   string            `json:"name"`
	Tokens map[string]string `json:"tokens"`
}

const themeDemo = "flowchart LR\n  A --> B\n"

func specThemes(t *testing.T) []specTheme {
	t.Helper()
	data, err := os.ReadFile("../../spec/data/themes.json")
	if err != nil {
		t.Fatal(err)
	}
	var rows []specTheme
	if err := json.Unmarshal(data, &rows); err != nil {
		t.Fatal(err)
	}
	if len(rows) != 20 {
		t.Fatalf("spec/data/themes.json holds %d themes, want 20", len(rows))
	}
	return rows
}

func specThemeList(t *testing.T) string {
	t.Helper()
	var names []string
	for _, row := range specThemes(t) {
		names = append(names, row.Name)
	}
	slices.Sort(names)
	return strings.Join(names, ", ")
}

func truecolourEscape(t *testing.T, hex string) string {
	t.Helper()
	var r, g, b int
	if _, err := fmt.Sscanf(hex, "#%02x%02x%02x", &r, &g, &b); err != nil {
		t.Fatalf("%q: %v", hex, err)
	}
	return fmt.Sprintf("\x1b[38;2;%d;%d;%dm", r, g, b)
}

func renderTruecolourText(t *testing.T, name string) string {
	t.Helper()
	var out, errout bytes.Buffer
	err := Run(context.Background(), Config{
		Args:     []string{"render", "-e", "text", "--color", "always", "-t", name},
		Stdin:    strings.NewReader(themeDemo),
		Stdout:   &out,
		Stderr:   &errout,
		Terminal: TerminalEnv{ColorTerm: "truecolor", Term: "xterm-256color"},
	})
	if err != nil || errout.Len() != 0 {
		t.Fatalf("%s: %v %q", name, err, errout.String())
	}
	return out.String()
}

func TestRenderAcceptsEverySpecTheme(t *testing.T) {
	for _, row := range specThemes(t) {
		svg, stderr, code := invoke(t, themeDemo, "render", "-e", "svg", "-t", row.Name)
		if bg := ".emd-bg{fill:" + row.Tokens["bg"] + "}"; code != 0 || stderr != "" || !strings.Contains(svg, bg) {
			t.Fatalf("%s svg: exit %d stderr %q, want %s in output", row.Name, code, stderr, bg)
		}
		text := renderTruecolourText(t, row.Name)
		if border := truecolourEscape(t, row.Tokens["border"]); !strings.Contains(text, border) {
			t.Fatalf("%s text: no %q border escape in %q", row.Name, border, text)
		}
	}
}

func TestRenderRejectsUnknownTheme(t *testing.T) {
	want := "invalid value nope for -t; expected one of: " + specThemeList(t) + "\n"
	for _, format := range []string{"svg", "text"} {
		out, stderr, code := invoke(t, themeDemo, "render", "-e", format, "-t", "nope")
		if code != 2 || out != "" || stderr != want {
			t.Fatalf("-e %s: exit %d stdout %q stderr %q, want exit 2 and %q", format, code, out, stderr, want)
		}
	}
}

func TestRenderHelpListsEverySpecTheme(t *testing.T) {
	out, stderr, code := invoke(t, "", "render", "--help")
	want := "Themes: " + specThemeList(t) + ". PNG needs"
	if code != 0 || stderr != "" || !strings.Contains(out, want) {
		t.Fatalf("exit %d stderr %q, want %q in %q", code, stderr, want, out)
	}
}
