package lint

import (
	"encoding/json"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
)

const goldenDir = "../../spec/golden/lint"

func goldenFile(t *testing.T, name string) diag.FileDiagnostics {
	t.Helper()
	src, err := os.ReadFile(filepath.Join(goldenDir, name))
	require.NoError(t, err)
	report := LintSource(src, Config{})
	return diag.FileDiagnostics{Path: name, Kind: "flowchart", Source: report.Source, Diagnostics: report.Diagnostics}
}

func TestFormatTextOrdersFilesAndSeparatesThem(t *testing.T) {
	a := goldenFile(t, "error-duplicate-ids.mmd")
	b := a
	b.Path = "another.mmd"
	empty := diag.FileDiagnostics{Path: "0-clean.mmd", Source: []byte("flowchart LR\n  A --> B\n")}
	out, err := Render(FormatText, []diag.FileDiagnostics{a, empty, b}, RenderOptions{})
	require.NoError(t, err)
	text := string(out)
	require.Equal(t, 1, strings.Count(text, "\n\nerror-duplicate-ids.mmd:3:3"))
	require.True(t, strings.HasPrefix(text, "another.mmd:3:3: error[flowchart/duplicate-ids]"))
	require.NotContains(t, text, "0-clean.mmd")
	require.True(t, strings.HasSuffix(text, "= note: first declared here at error-duplicate-ids.mmd:2:3\n"))

	none, err := Render(FormatText, nil, RenderOptions{})
	require.NoError(t, err)
	require.Empty(t, none)
}

func TestFormatTextColour(t *testing.T) {
	file := goldenFile(t, "error-duplicate-ids.mmd")
	plain, err := Render(FormatText, []diag.FileDiagnostics{file}, RenderOptions{})
	require.NoError(t, err)
	coloured, err := Render(FormatText, []diag.FileDiagnostics{file}, RenderOptions{Colour: true})
	require.NoError(t, err)
	require.Contains(t, string(coloured), "\x1b[")
	require.Equal(t, string(plain), stripSGR(string(coloured)))
}

func stripSGR(s string) string {
	var out strings.Builder
	for i := 0; i < len(s); i++ {
		if s[i] != 0x1b {
			out.WriteByte(s[i])
			continue
		}
		for i < len(s) && s[i] != 'm' {
			i++
		}
	}
	return out.String()
}

func decode(t *testing.T, data []byte) map[string]any {
	t.Helper()
	var doc map[string]any
	require.NoError(t, json.Unmarshal(data, &doc))
	return doc
}

func dig(t *testing.T, v any, path ...any) any {
	t.Helper()
	for _, step := range path {
		switch key := step.(type) {
		case string:
			obj, ok := v.(map[string]any)
			require.True(t, ok, "%v is not an object", key)
			v, ok = obj[key]
			require.True(t, ok, "missing key %q", key)
		case int:
			list, ok := v.([]any)
			require.True(t, ok, "not a list at %d", key)
			require.Greater(t, len(list), key)
			v = list[key]
		}
	}
	return v
}

func numbers(t *testing.T, v any, path []any, keys ...string) []int {
	t.Helper()
	out := make([]int, len(keys))
	for i, key := range keys {
		out[i] = int(dig(t, v, append(path, key)...).(float64))
	}
	return out
}

func TestFormatColumnsAfterAnAstralCharacter(t *testing.T) {
	src := "flowchart LR\n  B[\"\U0001F600\"] --> A[x]\n  A[y] --> C\n"
	report := LintSource([]byte(src), Config{})
	require.Equal(t, []string{"flowchart/duplicate-ids:3"}, summarize(src, report.Diagnostics))
	files := []diag.FileDiagnostics{{Path: "emoji.mmd", Kind: "flowchart", Source: report.Source, Diagnostics: report.Diagnostics}}
	related := []any{"files", 0, "diagnostics", 0, "related", 0}
	machine, err := Render(FormatJSON, files, RenderOptions{})
	require.NoError(t, err)
	require.Equal(t, []int{2, 14}, numbers(t, decode(t, machine), related, "line", "column"))
	sarif, err := Render(FormatSARIF, files, RenderOptions{Version: "0.1.0"})
	require.NoError(t, err)
	region := []any{"runs", 0, "results", 0, "relatedLocations", 0, "physicalLocation", "region"}
	require.Equal(t, []int{2, 15}, numbers(t, decode(t, sarif), region, "startLine", "startColumn"))
}

func TestFormatGitHub(t *testing.T) {
	file := goldenFile(t, "error-duplicate-ids.mmd")
	out, err := Render(FormatGitHub, []diag.FileDiagnostics{file}, RenderOptions{})
	require.NoError(t, err)
	require.Equal(t, "::error file=error-duplicate-ids.mmd,line=3,col=3,endLine=3,endColumn=4,title=flowchart/duplicate-ids::Node id declared twice with different labels\n", string(out))

	odd := file
	odd.Path = "a:b,c%d.mmd"
	out, err = Render(FormatGitHub, []diag.FileDiagnostics{odd}, RenderOptions{})
	require.NoError(t, err)
	require.True(t, strings.HasPrefix(string(out), "::error file=a%3Ab%2Cc%25d.mmd,line=3,"))
}

func TestFormatSeverityMapping(t *testing.T) {
	src := "flowchart LR\n  A[Start] --> B[End]\n  A[Begin] --> C[End]\n"
	for _, c := range []struct {
		severity diag.Severity
		sarif    string
		command  string
		json     string
	}{
		{diag.SeverityError, `"level":"error"`, "::error ", `"severity":"error"`},
		{diag.SeverityWarning, `"level":"warning"`, "::warning ", `"severity":"warning"`},
		{diag.SeverityInfo, `"level":"note"`, "::notice ", `"severity":"info"`},
	} {
		cfg := Config{Severity: map[string]diag.Severity{"flowchart/duplicate-ids": c.severity}}
		report := LintSource([]byte(src), cfg)
		files := []diag.FileDiagnostics{{Path: "a.mmd", Kind: "flowchart", Source: report.Source, Diagnostics: report.Diagnostics}}
		sarif, err := Render(FormatSARIF, files, RenderOptions{Version: "0.1.0"})
		require.NoError(t, err)
		require.Contains(t, string(sarif), c.sarif)
		github, err := Render(FormatGitHub, files, RenderOptions{})
		require.NoError(t, err)
		require.True(t, strings.HasPrefix(string(github), c.command))
		machine, err := Render(FormatJSON, files, RenderOptions{})
		require.NoError(t, err)
		require.Contains(t, string(machine), c.json)
	}
}

func TestFormatOrderingAcrossFiles(t *testing.T) {
	file := goldenFile(t, "error-duplicate-ids.mmd")
	second := file
	second.Path = "a.mmd"
	for _, format := range []Format{FormatJSON, FormatSARIF, FormatGitHub} {
		forward, err := Render(format, []diag.FileDiagnostics{file, second}, RenderOptions{Version: "0.1.0"})
		require.NoError(t, err)
		reverse, err := Render(format, []diag.FileDiagnostics{second, file}, RenderOptions{Version: "0.1.0"})
		require.NoError(t, err)
		require.Equal(t, string(forward), string(reverse), format.String())
		require.Less(t, strings.Index(string(forward), "a.mmd"), strings.Index(string(forward), "error-duplicate-ids.mmd"))
	}
}

func TestParseFormat(t *testing.T) {
	for _, name := range []string{"text", "json", "sarif", "github"} {
		f, ok := ParseFormat(name)
		require.True(t, ok)
		require.Equal(t, name, f.String())
	}
	_, ok := ParseFormat("xml")
	require.False(t, ok)
	_, ok = ParseFormat("")
	require.False(t, ok)
}

func TestGoldenFixCases(t *testing.T) {
	safe, err := os.ReadFile(filepath.Join(goldenDir, "safe-fix-arrow-invalid.mmd"))
	require.NoError(t, err)
	out, applied := ApplyFixes(safe, Config{}, diag.FixSafe)
	require.Equal(t, 1, applied)
	require.Contains(t, string(out), "A --> B")

	unsafe, err := os.ReadFile(filepath.Join(goldenDir, "unsafe-fix-end-without-subgraph.mmd"))
	require.NoError(t, err)
	out, applied = ApplyFixes(unsafe, Config{}, diag.FixSafe)
	require.Zero(t, applied)
	require.Equal(t, string(unsafe), string(out))
	out, applied = ApplyFixes(unsafe, Config{}, diag.FixUnsafe)
	require.Equal(t, 1, applied)
	require.NotContains(t, string(out), "end")
}
