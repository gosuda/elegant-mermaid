package cli

import (
	"encoding/json"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

const (
	arrowSource = "flowchart LR\n  A -> B\n"
	arrowFixed  = "flowchart LR\n  A --> B\n"
	endSource   = "flowchart TD\n  A --> B\n  end\n"
	endFixed    = "flowchart TD\n  A --> B\n"
	dupSource   = "flowchart LR\n  A[Start] --> B[End]\n  A[Begin] --> C[End]\n"
	betaSource  = "block-beta\n  columns 1\n"
	cleanSource = "flowchart LR\n  A --> B\n"
	goldenDir   = "../../spec/golden/lint"
)

func writeLintFiles(t *testing.T, files map[string]string) string {
	t.Helper()
	dir := t.TempDir()
	for name, text := range files {
		path := filepath.Join(dir, name)
		if err := os.MkdirAll(filepath.Dir(path), 0o750); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(path, []byte(text), 0o600); err != nil {
			t.Fatal(err)
		}
	}
	return dir
}

func readText(t *testing.T, path string) string {
	t.Helper()
	data, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	return string(data)
}

func lintJSONPaths(t *testing.T, stdout string) []string {
	t.Helper()
	var doc struct {
		Files []hostCheckFile `json:"files"`
	}
	if err := json.Unmarshal([]byte(stdout), &doc); err != nil {
		t.Fatalf("%v: %s", err, stdout)
	}
	var paths []string
	for _, f := range doc.Files {
		paths = append(paths, f.Path)
	}
	return paths
}

func expectInvocation(t *testing.T, src string, args []string, stdout, stderr string, code int) {
	t.Helper()
	out, errout, got := invoke(t, src, args...)
	if out != stdout || errout != stderr || got != code {
		t.Fatalf("%q: exit=%d stdout=%q stderr=%q; want exit=%d stdout=%q stderr=%q", args, got, out, errout, code, stdout, stderr)
	}
}

func TestLintFixStdin(t *testing.T) {
	expectInvocation(t, arrowSource, []string{"lint", "--fix", "-"}, arrowFixed, "", 0)

	out, errout, code := invoke(t, endSource, "lint", "--fix", "-")
	if out != endSource || code != 1 || !strings.HasPrefix(errout, "<stdin>:3:3: error[flowchart/end-without-subgraph]") {
		t.Fatalf("safe fixes only: exit=%d stdout=%q stderr=%q", code, out, errout)
	}
	expectInvocation(t, endSource, []string{"lint", "--fix", "--unsafe-fixes", "-"}, endFixed, "", 0)
	expectInvocation(t, endSource, []string{"lint", "--fix", "--output-format", "text", "-"}, endSource, errout, 1)
}

func TestLintFixStdinUnclosedQuoteNeedsUnsafeFixes(t *testing.T) {
	const quote = "sequenceDiagram\n  participant \"Bob\n  A->>Bob: hi\n"
	const quoteFixed = "sequenceDiagram\n  participant \"Bob\"\n  A->>Bob: hi\n"
	out, errout, code := invoke(t, quote, "lint", "--fix", "-")
	if out != quote || code != 0 || !strings.HasPrefix(errout, "<stdin>:2:15: warning[sequence/quote-unclosed]") {
		t.Fatalf("safe fixes only: exit=%d stdout=%q stderr=%q", code, out, errout)
	}
	expectInvocation(t, quote, []string{"lint", "--fix", "--unsafe-fixes", "-"}, quoteFixed, "", 0)
	if _, _, code = invoke(t, quote, "lint", "--deny-warnings", "-"); code != 1 {
		t.Fatalf("--deny-warnings: exit=%d", code)
	}
}

func TestLintStdinDiagnostics(t *testing.T) {
	out, errout, code := invoke(t, arrowSource, "lint", "-")
	if code != 1 || errout != "" || !strings.HasPrefix(out, "<stdin>:2:5: error[flowchart/arrow-invalid]") {
		t.Fatalf("exit=%d stdout=%q stderr=%q", code, out, errout)
	}
	expectInvocation(t, cleanSource, []string{"lint", "-"}, "", "", 0)
	out, _, code = invoke(t, arrowSource, "lint", "--output-format", "github", "-")
	if code != 1 || !strings.HasPrefix(out, "::error file=<stdin>,line=2,col=5,endLine=2,endColumn=7,title=flowchart/arrow-invalid::") {
		t.Fatalf("github: exit=%d stdout=%q", code, out)
	}
}

func expectSafeFixRewrite(t *testing.T, dir, arrow string) {
	t.Helper()
	if err := os.Chmod(arrow, 0o640); err != nil {
		t.Fatal(err)
	}
	expectInvocation(t, "", []string{"lint", "--fix", arrow}, "", "", 0)
	if got := readText(t, arrow); got != arrowFixed {
		t.Fatalf("fixed file: %q", got)
	}
	if info, err := os.Stat(arrow); err != nil || info.Mode().Perm() != 0o640 {
		t.Fatalf("mode after rewrite: %v %v", info, err)
	}
	entries, err := os.ReadDir(dir)
	if err != nil || len(entries) != 3 {
		t.Fatalf("directory after rewrite: %v %v", entries, err)
	}
}

func expectUnsafeFixNeedsOptIn(t *testing.T, unsafe string) {
	t.Helper()
	out, _, code := invoke(t, "", "lint", "--fix", unsafe)
	if code != 1 || !strings.Contains(out, "error[flowchart/end-without-subgraph]") || readText(t, unsafe) != endSource {
		t.Fatalf("safe fixes only: exit=%d stdout=%q file=%q", code, out, readText(t, unsafe))
	}
	expectInvocation(t, "", []string{"lint", "--fix", "--unsafe-fixes", unsafe}, "", "", 0)
	if got := readText(t, unsafe); got != endFixed {
		t.Fatalf("unsafe fix: %q", got)
	}
}

func expectFixLeavesUnfixableFile(t *testing.T, dup string) {
	t.Helper()
	out, _, code := invoke(t, "", "lint", "--fix", dup)
	if code != 1 || !strings.Contains(out, "error[flowchart/duplicate-ids]") || readText(t, dup) != dupSource {
		t.Fatalf("no fix available: exit=%d stdout=%q file=%q", code, out, readText(t, dup))
	}
}

func TestLintFixRewritesFiles(t *testing.T) {
	dir := writeLintFiles(t, map[string]string{"a.mmd": arrowSource, "unsafe.mmd": endSource, "dup.mmd": dupSource})
	expectSafeFixRewrite(t, dir, filepath.Join(dir, "a.mmd"))
	expectUnsafeFixNeedsOptIn(t, filepath.Join(dir, "unsafe.mmd"))
	expectFixLeavesUnfixableFile(t, filepath.Join(dir, "dup.mmd"))
}

func TestLintExitCodes(t *testing.T) {
	dir := writeLintFiles(t, map[string]string{"beta.mmd": betaSource, "dup.mmd": dupSource})
	beta, dup := filepath.Join(dir, "beta.mmd"), filepath.Join(dir, "dup.mmd")
	out, _, code := invoke(t, "", "lint", beta)
	if code != 0 || !strings.Contains(out, "warning[common/no-experimental]") {
		t.Fatalf("warning only: exit=%d stdout=%q", code, out)
	}
	if _, _, code = invoke(t, "", "lint", "--deny-warnings", beta); code != 1 {
		t.Fatalf("warning under --deny-warnings: exit=%d", code)
	}
	if _, _, code = invoke(t, "", "lint", dup); code != 1 {
		t.Fatalf("error: exit=%d", code)
	}
	if out, _, code = invoke(t, "", "lint", "--ignore", "flowchart/duplicate-ids", dup); code != 0 || out != "" {
		t.Fatalf("ignored error: exit=%d stdout=%q", code, out)
	}
}

func TestLintUsageErrors(t *testing.T) {
	for _, c := range []struct {
		args    []string
		message string
	}{
		{[]string{"lint", "--unsafe-fixes", "x.mmd"}, "--unsafe-fixes requires --fix"},
		{[]string{"lint", "--output-format", "xml"}, "invalid value xml for --output-format; expected one of: text, json, sarif, github"},
		{[]string{"lint", "--color", "sometimes"}, "invalid value sometimes for --color; expected one of: auto, always, never"},
		{[]string{"lint", "--select", "nope/code"}, "unknown diagnostic code: nope/code; use a code printed by emd check or emd lint"},
		{[]string{"lint", "--ignore", "flowchart/duplicate-ids,bogus"}, "unknown diagnostic code: bogus; use a code printed by emd check or emd lint"},
		{[]string{"lint", "--bogus"}, "unknown flag --bogus; run emd lint --help"},
		{[]string{"lint", "--select"}, "missing value for --select"},
		{[]string{"lint", "--fix=maybe"}, "invalid value maybe for --fix; expected one of: true, false"},
		{[]string{"lint", "--fix", "--output-format", "json", "-"}, "lint --fix - supports only text diagnostics; remove --output-format or pass a file path"},
		{[]string{"lint", "--fix", "-", "--output-format", "sarif"}, "lint --fix - supports only text diagnostics; remove --output-format or pass a file path"},
		{[]string{"check", "--output-format", "xml"}, "invalid value xml for --output-format; expected one of: text, json, sarif, github"},
	} {
		expectInvocation(t, "", c.args, "", c.message+"\n", 2)
	}
	_, errout, code := invoke(t, "", "lint", "no-such-dir-for-emd-lint")
	if code != 2 || !strings.HasPrefix(errout, "cannot read no-such-dir-for-emd-lint") {
		t.Fatalf("missing path: exit=%d stderr=%q", code, errout)
	}
}

func TestLintWalk(t *testing.T) {
	dir := writeLintFiles(t, map[string]string{
		"a.mmd":                    cleanSource,
		"sub/b.mermaid":            cleanSource,
		"c.md":                     "# Title\n\n```mermaid\n" + cleanSource + "```\n",
		"d.markdown":               "text only\n",
		".hidden/e.mmd":            dupSource,
		"node_modules/f.mmd":       dupSource,
		"target/g.mmd":             dupSource,
		"notes.txt":                dupSource,
		"empty/notes.txt":          "none\n",
		"deep/.cache/ignored.mmd":  dupSource,
		"deep/visible/included.md": "```mermaid\n" + cleanSource + "```\n",
	})
	t.Chdir(dir)
	out, errout, code := invoke(t, "", "lint", "--output-format", "json")
	if code != 0 || errout != "" {
		t.Fatalf("implicit scan: exit=%d stdout=%q stderr=%q", code, out, errout)
	}
	want := []string{"a.mmd", "c.md", "d.markdown", "deep/visible/included.md", "sub/b.mermaid"}
	if got := lintJSONPaths(t, out); strings.Join(got, ",") != strings.Join(want, ",") {
		t.Fatalf("walk order %v; want %v", got, want)
	}
	expectInvocation(t, "", []string{"lint", "empty"}, "", "no Mermaid files found in empty\n", 2)
	expectInvocation(t, "", []string{"lint", "notes.txt"}, "", "no Mermaid files found in notes.txt\n", 2)
	t.Chdir(filepath.Join(dir, "empty"))
	expectInvocation(t, "", []string{"lint"}, "", "no Mermaid files found in .\n", 0)
}

func TestLintMarkdownHost(t *testing.T) {
	host := "# Title\n\ntext\n\n```mermaid\nflowchart LR\n  A -> B\n```\n\ntail\n"
	dir := writeLintFiles(t, map[string]string{"doc.md": host})
	path := filepath.Join(dir, "doc.md")
	out, _, code := invoke(t, "", "lint", "--output-format", "json", path)
	if code != 1 {
		t.Fatalf("exit=%d stdout=%q", code, out)
	}
	var doc struct {
		Files []hostCheckFile `json:"files"`
	}
	if err := json.Unmarshal([]byte(out), &doc); err != nil || len(doc.Files) != 1 || len(doc.Files[0].Diagnostics) != 1 {
		t.Fatalf("%v: %s", err, out)
	}
	d := doc.Files[0].Diagnostics[0]
	if d.Code != "flowchart/arrow-invalid" || d.Line != 7 || d.Column != 5 || host[d.Span.Start:d.Span.End] != "->" {
		t.Fatalf("diagnostic: %+v", d)
	}
	expectInvocation(t, "", []string{"lint", "--fix", path}, "", "", 0)
	want := strings.Replace(host, "A -> B", "A --> B", 1)
	if got := readText(t, path); got != want {
		t.Fatalf("host after --fix: %q; want %q", got, want)
	}
}

func TestEmdJSON(t *testing.T) {
	dir := writeLintFiles(t, map[string]string{
		"emd.json":        `{"lint":{"ignore":["flowchart/duplicate-ids"]}}`,
		"sub/dup.mmd":     dupSource,
		"other.json":      `{"lint":{"severity":{"flowchart/duplicate-ids":"info"}}}`,
		"bad/emd.json":    `{"lint":`,
		"bad/dup.mmd":     dupSource,
		"codes/emd.json":  `{"lint":{"select":["flowchart/nope"]}}`,
		"codes/dup.mmd":   dupSource,
		"extra/emd.json":  `{"other":1}`,
		"extra/dup.mmd":   dupSource,
		"select/emd.json": `{"lint":{"select":["common/no-experimental"]}}`,
		"select/dup.mmd":  dupSource,
	})
	dup := filepath.Join(dir, "sub", "dup.mmd")
	selectDup := filepath.Join(dir, "select", "dup.mmd")
	expectInvocation(t, "", []string{"lint", dup}, "", "", 0)

	for _, c := range []struct {
		name     string
		args     []string
		code     int
		contains string
	}{
		{"--no-config", []string{"lint", "--no-config", dup}, 1, "error[flowchart/duplicate-ids]"},
		{"--lint-config", []string{"lint", "--lint-config", filepath.Join(dir, "other.json"), dup}, 0, "info[flowchart/duplicate-ids]"},
		{"--select keeps the file ignore", []string{"lint", "--select", "flowchart/duplicate-ids", dup}, 0, ""},
		{"--ignore replaces the file ignore", []string{"lint", "--ignore", "meta/unknown-rule", dup}, 1, "error[flowchart/duplicate-ids]"},
		{"file select replaces the default set", []string{"lint", selectDup}, 0, ""},
		{"flag select replaces the file select", []string{"lint", "--select", "flowchart/duplicate-ids", selectDup}, 1, "duplicate-ids"},
	} {
		out, _, code := invoke(t, "", c.args...)
		if code != c.code || !strings.Contains(out, c.contains) || (c.contains == "" && out != "") {
			t.Fatalf("%s: exit=%d stdout=%q", c.name, code, out)
		}
	}
}

func TestEmdJSONErrors(t *testing.T) {
	dir := writeLintFiles(t, map[string]string{
		"bad/emd.json":   `{"lint":`,
		"bad/dup.mmd":    dupSource,
		"codes/emd.json": `{"lint":{"select":["flowchart/nope"]}}`,
		"codes/dup.mmd":  dupSource,
		"extra/emd.json": `{"other":1}`,
		"extra/dup.mmd":  dupSource,
	})
	for _, c := range []struct{ name, message string }{
		{"bad", "not valid JSON"},
		{"extra", `unknown key "other"`},
	} {
		config := filepath.Join(dir, c.name, "emd.json")
		expectInvocation(t, "", []string{"lint", filepath.Join(dir, c.name, "dup.mmd")}, "", "invalid emd.json "+config+": "+c.message+"\n", 2)
		expectInvocation(t, "", []string{"lint", "--lint-config", config, filepath.Join(dir, c.name, "dup.mmd")}, "", "invalid emd.json "+config+": "+c.message+"\n", 2)
		out, _, code := invoke(t, "", "lint", "--no-config", filepath.Join(dir, c.name, "dup.mmd"))
		if code != 1 || !strings.Contains(out, "error[flowchart/duplicate-ids]") {
			t.Fatalf("--no-config skips the broken %s config: exit=%d stdout=%q", c.name, code, out)
		}
	}
	expectInvocation(t, "", []string{"lint", filepath.Join(dir, "codes", "dup.mmd")}, "", "unknown diagnostic code: flowchart/nope; use a code printed by emd check or emd lint\n", 2)
	missing := filepath.Join(dir, "absent.json")
	_, errout, code := invoke(t, "", "lint", "--lint-config", missing, filepath.Join(dir, "bad", "dup.mmd"))
	if code != 2 || !strings.HasPrefix(errout, "cannot read "+missing+": ") {
		t.Fatalf("missing --lint-config: exit=%d stderr=%q", code, errout)
	}
}

func TestEmdJSONStdinStartsInTheWorkingDirectory(t *testing.T) {
	dir := writeLintFiles(t, map[string]string{
		"emd.json": `{"lint":{"ignore":["flowchart/duplicate-ids"]}}`,
		"deep/x":   "",
	})
	t.Chdir(filepath.Join(dir, "deep"))
	expectInvocation(t, dupSource, []string{"lint", "-"}, "", "", 0)
	out, _, code := invoke(t, dupSource, "lint", "--no-config", "-")
	if code != 1 || !strings.HasPrefix(out, "<stdin>:3:3: error[flowchart/duplicate-ids]") {
		t.Fatalf("--no-config on stdin: exit=%d stdout=%q", code, out)
	}
}

func TestExplain(t *testing.T) {
	const duplicate = "code: flowchart/duplicate-ids\n" +
		"kind: flowchart\n" +
		"severity: error\n" +
		"fix_safety: none\n" +
		"summary: Node id declared twice with different labels\n" +
		"help: Give each node one label, or use a new id for the second node.\n" +
		"rationale: Mermaid keeps one of the two declarations and drops the other, so the rendered diagram is wrong.\n" +
		"suppression: %% emd-disable-next-line flowchart/duplicate-ids: reason\n"
	expectInvocation(t, "", []string{"explain", "flowchart/duplicate-ids"}, duplicate, "", 0)

	const asJSON = `{"code":"flowchart/duplicate-ids","kind":"flowchart","severity":"error","fix_safety":"none",` +
		`"summary":"Node id declared twice with different labels",` +
		`"help":"Give each node one label, or use a new id for the second node.",` +
		`"rationale":"Mermaid keeps one of the two declarations and drops the other, so the rendered diagram is wrong.",` +
		`"suppression":"%% emd-disable-next-line flowchart/duplicate-ids: reason"}` + "\n"
	expectInvocation(t, "", []string{"explain", "flowchart/duplicate-ids", "--output-format", "json"}, asJSON, "", 0)
	expectInvocation(t, "", []string{"explain", "--output-format=json", "flowchart/duplicate-ids"}, asJSON, "", 0)

	out, _, code := invoke(t, "", "explain", "flowchart/node-unclosed-bracket")
	if code != 0 || !strings.HasPrefix(out, "code: flowchart/unclosed-node-bracket\nkind: flowchart\nseverity: error\nfix_safety: unsafe\n") {
		t.Fatalf("alias: exit=%d stdout=%q", code, out)
	}
	if !strings.HasSuffix(out, "suppression: %% emd-disable-next-line flowchart/unclosed-node-bracket: reason\n") {
		t.Fatalf("alias suppression: %q", out)
	}
}

func TestExplainKindAndEmptyHelp(t *testing.T) {
	for _, c := range []struct{ code, kind string }{
		{"meta/unknown-rule", "common"},
		{"config/malformed", "common"},
		{"source/invalid-utf8", "common"},
		{"common/unknown-diagram-kind", "common"},
		{"agentflow/unterminated", "agentflow"},
	} {
		out, _, code := invoke(t, "", "explain", c.code)
		if code != 0 || !strings.HasPrefix(out, "code: "+c.code+"\nkind: "+c.kind+"\n") {
			t.Fatalf("%s: exit=%d stdout=%q", c.code, code, out)
		}
	}
	out, _, _ := invoke(t, "", "explain", "agentflow/unterminated")
	if !strings.Contains(out, "\nhelp: \nrationale: ") {
		t.Fatalf("empty help line: %q", out)
	}
	out, _, _ = invoke(t, "", "explain", "common/acc-title-missing")
	if !strings.Contains(out, "\nseverity: off\n") {
		t.Fatalf("off severity: %q", out)
	}
}

func TestExplainErrors(t *testing.T) {
	for _, c := range []struct {
		args    []string
		message string
	}{
		{[]string{"explain", "flowchart/nope"}, "unknown diagnostic code: flowchart/nope; use a code printed by emd check or emd lint"},
		{[]string{"explain"}, "missing CODE; run emd explain --help"},
		{[]string{"explain", "a", "b"}, "unexpected argument b; run emd explain --help"},
		{[]string{"explain", "meta/unknown-rule", "--output-format", "sarif"}, "invalid value sarif for --output-format; expected one of: text, json"},
		{[]string{"explain", "--color", "never", "meta/unknown-rule"}, "unknown flag --color; run emd explain --help"},
	} {
		expectInvocation(t, "", c.args, "", c.message+"\n", 2)
	}
}

func TestHelpListsLintAndExplain(t *testing.T) {
	out, _, code := invoke(t, "", "--help")
	if code != 0 || !strings.Contains(out, "lint     Check lint rules and optionally apply fixes\n") || !strings.Contains(out, "explain  Explain a diagnostic code\n") {
		t.Fatalf("root help: exit=%d %q", code, out)
	}
	for command, example := range map[string]string{
		"lint":    "Example: emd lint --fix demo.mmd\n",
		"explain": "Example: emd explain flowchart/unexpected-token\n",
		"check":   "Example: emd check docs/\n",
	} {
		out, _, code = invoke(t, "", command, "--help")
		if code != 0 || !strings.HasSuffix(out, example) {
			t.Fatalf("%s help: exit=%d %q", command, code, out)
		}
	}
	out, _, _ = invoke(t, "", "lint", "--help")
	for _, flag := range []string{"--fix", "--unsafe-fixes", "--select CODES", "--ignore CODES", "--deny-warnings", "--output-format text|json|sarif|github", "--lint-config FILE", "--no-config", "--color auto|always|never"} {
		if !strings.Contains(out, flag) {
			t.Fatalf("lint help lacks %s: %q", flag, out)
		}
	}
}

func TestCheckMachineFormatsMatchTheLintGoldens(t *testing.T) {
	t.Chdir(goldenDir)
	for _, name := range []string{"safe-fix-arrow-invalid", "unsafe-fix-end-without-subgraph"} {
		for format, extension := range map[string]string{"sarif": ".sarif", "github": ".github"} {
			expectInvocation(t, "", []string{"check", "--output-format", format, name + ".mmd"}, readText(t, name+extension), "", 1)
		}
	}
	expectInvocation(t, "", []string{"check", "--output-format", "sarif", "suppressed-duplicate-ids.mmd"}, readText(t, "suppressed-duplicate-ids.sarif"), "", 0)
	for format, extension := range map[string]string{"sarif": ".sarif", "github": ".github"} {
		expectInvocation(t, "", []string{"check", "--output-format", format, "warning-quote-unclosed.mmd"}, readText(t, "warning-quote-unclosed"+extension), "", 0)
	}
}

type wasmReply struct {
	OK          bool              `json:"ok"`
	Output      string            `json:"output"`
	Diagnostics []json.RawMessage `json:"diagnostics"`
	Applied     int               `json:"applied"`
}

func wasmReplyOf(t *testing.T, op, src, options string) wasmReply {
	t.Helper()
	var r wasmReply
	if err := json.Unmarshal([]byte(WasmCall(op, src, options)), &r); err != nil {
		t.Fatal(err)
	}
	if r.Diagnostics == nil {
		t.Fatalf("%s: diagnostics must be an array", op)
	}
	return r
}

func expectWasmVerdict(t *testing.T, label string, r wasmReply, ok bool, diagnostics int) {
	t.Helper()
	if r.OK != ok || len(r.Diagnostics) != diagnostics {
		t.Fatalf("%s: %+v", label, r)
	}
}

func expectWasmLintMatchesCLI(t *testing.T) {
	t.Helper()
	r := wasmReplyOf(t, "lint", dupSource, "")
	cli, _, _ := invoke(t, dupSource, "lint", "--output-format", "json", "-")
	if r.OK || r.Output != cli || len(r.Diagnostics) != 1 || r.Applied != 0 {
		t.Fatalf("lint: %+v; cli=%q", r, cli)
	}
}

func expectWasmLintOptionRejected(t *testing.T, options string) {
	t.Helper()
	bad := wasmReplyOf(t, "lint", dupSource, options)
	if bad.OK || bad.Output != "invalid option: lint" || len(bad.Diagnostics) != 0 || bad.Applied != 0 {
		t.Fatalf("%s: %+v", options, bad)
	}
}

func expectWasmCheckIgnoresLintOption(t *testing.T) {
	t.Helper()
	plain := wasmReplyOf(t, "check", dupSource, "")
	keyed := wasmReplyOf(t, "check", dupSource, `{"lint":{"select":["nope"]}}`)
	if keyed.Output != plain.Output || keyed.OK != plain.OK {
		t.Fatalf("an option the op does not read must be ignored: %+v", keyed)
	}
}

func TestWasmLint(t *testing.T) {
	expectWasmLintMatchesCLI(t)
	expectWasmVerdict(t, "ignored", wasmReplyOf(t, "lint", dupSource, `{"lint":{"ignore":["flowchart/duplicate-ids"]},"max":"unsafe"}`), true, 0)
	expectWasmVerdict(t, "info", wasmReplyOf(t, "lint", dupSource, `{"lint":{"severity":{"flowchart/duplicate-ids":"info"}}}`), true, 1)
	for _, options := range []string{`{"lint":{"select":["nope"]}}`, `{"lint":[]}`, `{"lint":{"severity":{"flowchart/duplicate-ids":"fatal"}}}`, `{"lint":{"extra":1}}`, `{"lint":null}`} {
		expectWasmLintOptionRejected(t, options)
	}
	expectWasmCheckIgnoresLintOption(t)
}

type wasmFixCase struct {
	name        string
	src         string
	options     string
	output      string
	applied     int
	diagnostics int
}

func expectWasmFix(t *testing.T, c wasmFixCase) wasmReply {
	t.Helper()
	r := wasmReplyOf(t, "fix", c.src, c.options)
	if !r.OK || r.Output != c.output || r.Applied != c.applied || len(r.Diagnostics) != c.diagnostics {
		t.Fatalf("%s: %+v", c.name, r)
	}
	return r
}

func TestWasmFix(t *testing.T) {
	expectWasmFix(t, wasmFixCase{"safe fix", arrowSource, "", arrowFixed, 1, 0})
	expectWasmFix(t, wasmFixCase{"unsafe fix skipped", endSource, "", endSource, 0, 1})
	unsafe := expectWasmFix(t, wasmFixCase{"unsafe fix", endSource, `{"max":"unsafe"}`, endFixed, 1, 0})
	cli, _, _ := invoke(t, endSource, "lint", "--fix", "--unsafe-fixes", "-")
	if unsafe.Output != cli {
		t.Fatalf("fix output %q differs from the CLI %q", unsafe.Output, cli)
	}
	expectWasmFix(t, wasmFixCase{"remaining diagnostics", dupSource, "", dupSource, 0, 1})
	if bad := wasmReplyOf(t, "fix", arrowSource, `{"max":"all"}`); bad.OK || bad.Output != "invalid option: max" {
		t.Fatalf("bad max: %+v", bad)
	}
}

func TestLintColour(t *testing.T) {
	always, _, _ := invoke(t, arrowSource, "lint", "--color", "always", "-")
	if !strings.Contains(always, "\x1b[") {
		t.Fatalf("--color always: %q", always)
	}
	never, _, _ := invoke(t, arrowSource, "lint", "--color", "never", "-")
	if strings.Contains(never, "\x1b") || stripSGRBytes(always) != never {
		t.Fatalf("--color never: %q vs %q", never, always)
	}
	for _, format := range []string{"json", "sarif", "github"} {
		out, _, _ := invoke(t, arrowSource, "lint", "--color", "always", "--output-format", format, "-")
		if strings.Contains(out, "\x1b") {
			t.Fatalf("%s carries colour: %q", format, out)
		}
	}
	_, errout, _ := invoke(t, endSource, "lint", "--fix", "--color", "always", "-")
	if !strings.Contains(errout, "\x1b[") {
		t.Fatalf("--fix - diagnostics on stderr ignore --color always: %q", errout)
	}
}

func stripSGRBytes(s string) string {
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

type grammarFinding struct {
	Code     string                   `json:"code"`
	Severity string                   `json:"severity"`
	Message  string                   `json:"message"`
	Span     struct{ Start, End int } `json:"span"`
	Related  []struct {
		Span    struct{ Start, End int } `json:"span"`
		Message string                   `json:"message"`
	} `json:"related"`
}
type grammarExpectation struct {
	code, severity string
	exit, count    int
}

func checkGrammarDiagnostics(t *testing.T, source string, args []string, want grammarExpectation) []grammarFinding {
	t.Helper()
	out, stderr, exit := invoke(t, source, args...)
	if exit != want.exit || stderr != "" {
		t.Fatalf("exit=%d stderr=%q stdout=%s", exit, stderr, out)
	}
	var document struct {
		Files []struct {
			Diagnostics []grammarFinding `json:"diagnostics"`
		} `json:"files"`
	}
	if err := json.Unmarshal([]byte(out), &document); err != nil {
		t.Fatalf("decode diagnostics: %v: %s", err, out)
	}
	var diagnostics []grammarFinding
	for _, file := range document.Files {
		diagnostics = append(diagnostics, file.Diagnostics...)
	}
	var matches []grammarFinding
	for _, d := range diagnostics {
		if d.Code != want.code {
			continue
		}
		if d.Severity != want.severity {
			t.Fatalf("severity: %+v", d)
		}
		matches = append(matches, d)
	}
	if len(matches) != want.count {
		t.Fatalf("got %d %s diagnostics, want %d: %s", len(matches), want.code, want.count, out)
	}
	return matches
}

func TestGrammarOwnedDiagnostics(t *testing.T) {
	t.Run("frame ownership", checkFrameOwnership)
	t.Run("commit warning", checkCommitWarning)
	checkGrammarScoresAndSets(t)
}

func checkFrameOwnership(t *testing.T) {
	t.Helper()
	const frameCode = "eventmodeling/duplicate-frame-id"
	const frames = "eventmodeling\ntf 1 ui A\ntf 1 cmd B\n"
	ds := checkGrammarDiagnostics(t, frames, []string{"check", "--output-format", "json", "-"}, grammarExpectation{frameCode, "error", 1, 1})
	if ds[0].Span.Start != strings.LastIndex(frames, "1") || ds[0].Span.End != ds[0].Span.Start+1 || len(ds[0].Related) != 1 || ds[0].Related[0].Span.Start != strings.Index(frames, "1") || ds[0].Related[0].Span.End != ds[0].Related[0].Span.Start+1 || ds[0].Related[0].Message != "first declared here" {
		t.Fatalf("frame spans: %+v", ds)
	}
	for _, source := range []string{strings.Replace(frames, "tf 1 cmd", "tf 2 cmd", 1), strings.Replace(frames, "tf 1 ui", "tf 01 ui", 1)} {
		checkGrammarDiagnostics(t, source, []string{"check", "--output-format", "json", "-"}, grammarExpectation{frameCode, "error", 0, 0})
	}
	for name, config := range map[string]string{
		"ignore":   `{"lint":{"ignore":["` + frameCode + `"]}}`,
		"off":      `{"lint":{"severity":{"` + frameCode + `":"off"}}}`,
		"severity": `{"lint":{"severity":{"` + frameCode + `":"info"}}}`,
	} {
		t.Run(name, func(t *testing.T) {
			dir := writeLintFiles(t, map[string]string{"lint.json": config})
			checkGrammarDiagnostics(t, frames, []string{"lint", "--lint-config", filepath.Join(dir, "lint.json"), "--color", "never", "--output-format", "json", "-"}, grammarExpectation{frameCode, "error", 1, 1})
		})
	}
	suppressed := strings.Replace(frames, "tf 1 cmd", "%% emd-disable-next-line "+frameCode+": deliberate duplicate\ntf 1 cmd", 1)
	checkGrammarDiagnostics(t, suppressed, []string{"lint", "--no-config", "--color", "never", "--output-format", "json", "-"}, grammarExpectation{frameCode, "error", 1, 1})
}

func checkCommitWarning(t *testing.T) {
	t.Helper()
	const code = "gitgraph/duplicate-commit-id"
	const source = "gitGraph\ncommit id:\"x\"\ncommit id:\"x\"\n"
	for _, args := range [][]string{{"check", "--output-format", "json", "-"}, {"lint", "--no-config", "--color", "never", "--output-format", "json", "-"}} {
		ds := checkGrammarDiagnostics(t, source, args, grammarExpectation{code, "warning", 0, 1})
		if ds[0].Message != "commit id x already exists" || ds[0].Span.Start != strings.LastIndex(source, "\"x\"") || ds[0].Span.End != ds[0].Span.Start+3 {
			t.Fatalf("commit warning: %+v", ds)
		}
	}
	suppressed := "gitGraph\ncommit id:\"x\"\n%% emd-disable-next-line " + code + ": repeated id\ncommit id:\"x\"\n"
	checkGrammarDiagnostics(t, suppressed, []string{"lint", "--no-config", "--color", "never", "--output-format", "json", "-"}, grammarExpectation{code, "warning", 0, 0})
}

func checkGrammarScoresAndSets(t *testing.T) {
	t.Helper()
	for _, tc := range []struct {
		name, source, code, message string
		exit, count                 int
	}{
		{"low score", "journey\nTask: 0: Bob\n", "journey/score-out-of-range", "score 0 is outside the range 1 to 5", 1, 1},
		{"high score", "journey\nTask: 6: Bob\n", "journey/score-out-of-range", "score 6 is outside the range 1 to 5", 1, 1},
		{"minimum score", "journey\nTask: 1: Bob\n", "journey/score-out-of-range", "", 0, 0},
		{"maximum score", "journey\nTask: 5: Bob\n", "journey/score-out-of-range", "", 0, 0},
		{"signed score", "journey\nTask: +003: Bob\n", "journey/score-out-of-range", "", 0, 0},
		{"malformed score", "journey\nTask: abc: Bob\n", "journey/unexpected-token", "", 1, 1},
		{"no sets", "venn-beta\n", "venn/no-sets", "venn diagram has no sets", 1, 1},
		{"one set", "venn-beta\nset A\n", "venn/no-sets", "", 0, 0},
	} {
		t.Run(tc.name, func(t *testing.T) {
			ds := checkGrammarDiagnostics(t, tc.source, []string{"check", "--output-format", "json", "-"}, grammarExpectation{tc.code, "error", tc.exit, tc.count})
			if tc.message != "" && ds[0].Message != tc.message {
				t.Fatalf("message: %+v", ds)
			}
		})
	}
}
