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

func TestFormatText(t *testing.T) {
	file := goldenFile(t, "error-duplicate-ids.mmd")
	require.Len(t, file.Diagnostics, 1)
	out, err := Render(FormatText, []diag.FileDiagnostics{file}, RenderOptions{})
	require.NoError(t, err)
	want := "error-duplicate-ids.mmd:3:3: error[flowchart/duplicate-ids]: Node id declared twice with different labels\n" +
		"  |\n" +
		"3 |   A[Begin] --> C[End]\n" +
		"  |   ^\n" +
		"  = help: Give each node one label, or use a new id for the second node.\n" +
		"  = note: first declared here at error-duplicate-ids.mmd:2:3\n"
	require.Equal(t, want, string(out))
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

func TestFormatJSON(t *testing.T) {
	file := goldenFile(t, "error-duplicate-ids.mmd")
	out, err := Render(FormatJSON, []diag.FileDiagnostics{file}, RenderOptions{})
	require.NoError(t, err)
	require.True(t, strings.HasSuffix(string(out), "}\n"))
	doc := decode(t, out)
	require.EqualValues(t, 1, dig(t, doc, "version"))
	require.Equal(t, "error-duplicate-ids.mmd", dig(t, doc, "files", 0, "path"))
	require.Equal(t, "flowchart", dig(t, doc, "files", 0, "kind"))
	d := []any{"files", 0, "diagnostics", 0}
	require.Equal(t, "flowchart/duplicate-ids", dig(t, doc, append(d, "code")...))
	require.Equal(t, "error", dig(t, doc, append(d, "severity")...))
	require.Equal(t, []int{3, 3, 3, 4}, numbers(t, doc, d, "line", "column", "end_line", "end_column"))
	require.Equal(t, "first declared here", dig(t, doc, append(d, "related", 0, "message")...))
	require.Equal(t, []int{2, 3}, numbers(t, doc, append(d, "related", 0), "line", "column"))
	require.Equal(t, []any{}, dig(t, doc, append(d, "fixes")...))
	require.Equal(t, []int{1, 1, 0, 0}, numbers(t, doc, []any{"summary"}, "files", "errors", "warnings", "info"))
	require.Contains(t, string(out), `"related":[{"span":{"start":`)
}

func TestFormatSARIF(t *testing.T) {
	file := goldenFile(t, "error-duplicate-ids.mmd")
	out, err := Render(FormatSARIF, []diag.FileDiagnostics{file}, RenderOptions{Version: "0.1.0"})
	require.NoError(t, err)
	doc := decode(t, out)
	require.Equal(t, "2.1.0", dig(t, doc, "version"))
	driver := []any{"runs", 0, "tool", "driver"}
	require.Equal(t, "emd", dig(t, doc, append(driver, "name")...))
	require.Equal(t, "0.1.0", dig(t, doc, append(driver, "version")...))
	require.Len(t, dig(t, doc, append(driver, "rules")...), 1)
	rule := append(driver, "rules", 0)
	require.Equal(t, "flowchart/duplicate-ids", dig(t, doc, append(rule, "id")...))
	require.Equal(t, "Node id declared twice with different labels", dig(t, doc, append(rule, "shortDescription", "text")...))
	require.Equal(t, "Give each node one label, or use a new id for the second node.", dig(t, doc, append(rule, "help", "text")...))
	result := []any{"runs", 0, "results", 0}
	require.Equal(t, "flowchart/duplicate-ids", dig(t, doc, append(result, "ruleId")...))
	require.Equal(t, "error", dig(t, doc, append(result, "level")...))
	require.Equal(t, "Node id declared twice with different labels", dig(t, doc, append(result, "message", "text")...))
	physical := append(result, "locations", 0, "physicalLocation")
	require.Equal(t, "error-duplicate-ids.mmd", dig(t, doc, append(physical, "artifactLocation", "uri")...))
	require.Equal(t, []int{3, 3, 3, 4}, numbers(t, doc, append(physical, "region"), "startLine", "startColumn", "endLine", "endColumn"))
	related := append(result, "relatedLocations", 0, "physicalLocation", "region")
	require.Equal(t, []int{2, 3}, numbers(t, doc, related, "startLine", "startColumn"))
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

func TestFormatSeverityOverrideText(t *testing.T) {
	read := memoryFS(map[string]string{"/work/emd.json": `{"lint":{"severity":{"flowchart/duplicate-ids":"info"}}}`})
	cfg, err := LoadConfig("/work", read)
	require.NoError(t, err)
	src, err := os.ReadFile(filepath.Join(goldenDir, "error-duplicate-ids.mmd"))
	require.NoError(t, err)
	report := LintSource(src, cfg)
	out, err := Render(FormatText, []diag.FileDiagnostics{{Path: "error-duplicate-ids.mmd", Source: report.Source, Diagnostics: report.Diagnostics}}, RenderOptions{})
	require.NoError(t, err)
	require.True(t, strings.HasPrefix(string(out), "error-duplicate-ids.mmd:3:3: info[flowchart/duplicate-ids]: "))
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

func TestGoldenCasesParse(t *testing.T) {
	entries, err := os.ReadDir(goldenDir)
	require.NoError(t, err)
	var cases []string
	for _, e := range entries {
		if strings.HasSuffix(e.Name(), ".mmd") {
			cases = append(cases, strings.TrimSuffix(e.Name(), ".mmd"))
		}
	}
	require.Equal(t, []string{"error-duplicate-ids", "safe-fix-arrow-invalid", "suppressed-duplicate-ids", "unsafe-fix-end-without-subgraph", "warning-quote-unclosed"}, cases)
}

func TestGoldenSuppressedCase(t *testing.T) {
	src, err := os.ReadFile(filepath.Join(goldenDir, "suppressed-duplicate-ids.mmd"))
	require.NoError(t, err)
	require.Empty(t, LintSource(src, Config{}).Diagnostics)
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
