package syntax

import (
	"os"
	"strings"
	"testing"
)

func TestConfigQuotedGanttFrontmatter(t *testing.T) {
	src, err := os.ReadFile("../../corpus/gantt/mermaid/gantt~0011.mmd")
	if err != nil {
		t.Fatal(err)
	}
	start := strings.Index(string(src), "\n") + 1
	end := strings.Index(string(src[start:]), "---") + start
	value, ds := ParseConfigYAML(src, start, end)
	if len(ds) != 0 {
		t.Fatalf("diagnostics: %+v", ds)
	}
	want := " // YAML supports multiline strings using a newline markers: \n #item36 { fill: CadetBlue }       \n\n// Custom marker workaround CSS from forum (below)    \n rect[id^=workaround] { height: calc(100% - 50px) ; transform: translate(9px, 25px); y: 0; width: 1.5px; stroke: none; fill: red; }   \n text[id^=workaround] { fill: red; y: 100%; font-size: 15px;} "
	got := value.Entries[2].Value.Entries[0].Value.Text
	if got != want {
		t.Fatalf("themeCSS = %q, want %q", got, want)
	}
}

func TestConfigQuotedClosingLine(t *testing.T) {
	for _, quote := range []string{"\"", "'"} {
		for _, tc := range []struct{ text, want string }{
			{"  key: Qone\n  two\n  Q", "one two "},
			{"  key: Qone\n two\n Q", "one two "},
			{"  key: Qone\n\ttwo\nQ", "one two "},
			{"key: Qone \n  two\n\n  three\nQ", "one two\nthree "},
			{"key: Q#{}[],:;\n---x\nQ", "#{}[],:; ---x "},
		} {
			text := strings.ReplaceAll(tc.text, "Q", quote)
			value, ds := ParseConfigYAML([]byte(text), 0, len(text))
			if len(ds) != 0 {
				t.Fatalf("%q: %+v", text, ds)
			}
			if value.Entries[0].Value.Text != tc.want {
				t.Fatalf("%q: %+v", text, value)
			}
		}
	}
}

func TestConfigQuotedUnterminatedContinuation(t *testing.T) {
	text := "key: \"one\nsecond"
	_, ds := ParseConfigYAML([]byte(text), 0, len(text))
	requireDiags(t, ds, []diagWant{{codeMalformed, msgMalformed, span(len(text), len(text))}})
}

func TestConfigQuotedDocumentMarker(t *testing.T) {
	for _, marker := range []string{"---", "..."} {
		text := "key: \"one\n" + marker + "\n two\""
		_, ds := ParseConfigYAML([]byte(text), 0, len(text))
		requireDiags(t, ds, []diagWant{{codeMalformed, msgMalformed, span(10, 13)}})
	}
}
