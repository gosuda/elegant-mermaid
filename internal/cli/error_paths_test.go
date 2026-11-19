package cli

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func chainDiagram(edges int) string {
	var text strings.Builder
	text.WriteString("flowchart LR\n")
	for i := range edges {
		fmt.Fprintf(&text, "n%d[node] --> n%d\n", i, i+1)
	}
	return text.String()
}

func TestErrorPaths(t *testing.T) {
	dir := t.TempDir()
	for name, text := range map[string]string{
		"good.mmd":     "flowchart LR\n A[alpha] --> B\n",
		"broken.dump":  `{"nope`,
		"latin1.dump":  "\xff",
		"model.dump":   `{"version":1,"stage":"model"}`,
		"big.mmd":      chainDiagram(2001),
		"wide.mmd":     chainDiagram(400),
		"broken.yaml":  "not: [valid",
		"list.yaml":    "- a\n",
		"seed.yaml":    "handDrawnSeed: -3\n",
		"latin1.yaml":  "a: \xff\n",
		"broken.json":  `{"prefix":"x","icons":`,
		"latin1.json":  "\xff\xfe",
		"ok.script":    "settle\n",
		"cases.txt":    "1 +\n",
		"cases-ok.txt": "isqrt 99 -> 9\n",
	} {
		writeViewInput(t, filepath.Join(dir, name), text)
	}
	if err := os.Mkdir(filepath.Join(dir, "dir"), 0o700); err != nil {
		t.Fatal(err)
	}
	t.Chdir(dir)
	for _, c := range []struct {
		args   []string
		stdout string
		stderr string
		code   int
	}{
		{[]string{"view", "missing.mmd"}, "", "cannot read missing.mmd: no such file or directory\n", 2},
		{[]string{"view", "dir"}, "", "cannot read dir: is a directory\n", 2},
		{[]string{"view", "a", "b"}, "", "view accepts one INPUT\n", 2},
		{[]string{"view"}, "", "view requires a readable file path; stdin is not supported\n", 2},
		{[]string{"view", "-"}, "", "view requires a readable file path; stdin is not supported\n", 2},
		{[]string{"view", "--graphics", "bogus"}, "", "view requires a readable file path; stdin is not supported\n", 2},
		{[]string{"view", "missing.mmd", "-t", "nope"}, "", "unknown theme: nope\n", 2},
		{[]string{"view", "good.mmd", "--script", "missing.script"}, "", "cannot read missing.script: no such file or directory\n", 2},
		{[]string{"view", "good.mmd", "--script", "dir"}, "", "cannot read dir: is a directory\n", 2},
		{[]string{"layout", "--dump", "good.mmd"}, "", "--dump requires --metrics\n", 2},
		{[]string{"layout", "--metrics", "--dump", "missing.dump"}, "", "cannot read missing.dump: no such file or directory\n", 2},
		{[]string{"layout", "--metrics", "--dump", "dir"}, "", "cannot read dir: is a directory\n", 2},
		{[]string{"layout", "--metrics", "--dump", "broken.dump"}, "", "broken.dump: malformed layout dump: invalid JSON\n", 2},
		{[]string{"layout", "--metrics", "--dump", "good.mmd"}, "", "good.mmd: malformed layout dump: invalid JSON\n", 2},
		{[]string{"layout", "--metrics", "--dump", "latin1.dump"}, "", "latin1.dump: malformed layout dump: invalid UTF-8\n", 2},
		{[]string{"layout", "--metrics", "--dump", "model.dump"}, "", "model.dump: malformed layout dump: expected version 1 layout dump\n", 2},
		{[]string{"layout", "big.mmd"}, "", "model exceeds the limit of 2000; actual 2002\n", 1},
		{[]string{"layout", "--metrics", "big.mmd"}, "", "model exceeds the limit of 2000; actual 2002\n", 1},
		{[]string{"render", "big.mmd", "-e", "svg"}, "", "model exceeds the limit of 2000; actual 2002\n", 1},
		{[]string{"render", "big.mmd", "-e", "text"}, "", "model exceeds the limit of 2000; actual 2002\n", 1},
		{[]string{"render", "wide.mmd", "-e", "png", "-s", "8", "-o", "out.png"}, "", "image is too large: 340289x544 pixels\n", 1},
		{[]string{"layout", "missing.mmd"}, "", "cannot read missing.mmd: no such file or directory\n", 2},
		{[]string{"render", "missing.mmd"}, "", "cannot read missing.mmd: no such file or directory\n", 2},
		{[]string{"render", "dir"}, "", "cannot read dir: is a directory\n", 2},
		{[]string{"render", "-o", "absent/out.svg", "good.mmd"}, "", "cannot write absent/out.svg: no such file or directory\n", 2},
		{[]string{"render", "-e", "svg", "-o", "dir", "good.mmd"}, "", "cannot write dir: is a directory\n", 2},
		{[]string{"render", "-c", "missing.yaml", "good.mmd"}, "", "cannot read missing.yaml: no such file or directory\n", 2},
		{[]string{"render", "-c", "broken.yaml", "good.mmd"}, "", "broken.yaml: invalid config: malformed config value\n", 2},
		{[]string{"render", "-c", "list.yaml", "good.mmd"}, "", "list.yaml: invalid config: config must be a mapping\n", 2},
		{[]string{"render", "-c", "seed.yaml", "good.mmd"}, "", "seed.yaml: invalid config: invalid config value -3 for handDrawnSeed\n", 2},
		{[]string{"render", "-c", "latin1.yaml", "good.mmd"}, "", "latin1.yaml: invalid config: invalid UTF-8 at byte 3\n", 2},
		{[]string{"render", "--icon-pack", "missing.json", "good.mmd"}, "", "cannot read missing.json: no such file or directory\n", 2},
		{[]string{"render", "--icon-pack", "broken.json", "good.mmd"}, "", "broken.json: malformed icon pack: invalid JSON at byte 22: expected a value\n", 2},
		{[]string{"render", "--icon-pack", "latin1.json", "good.mmd"}, "", "latin1.json: malformed icon pack: invalid UTF-8\n", 2},
		{[]string{"check", "missing.mmd"}, "", "cannot read missing.mmd: no such file or directory\n", 2},
		{[]string{"lint", "missing.mmd"}, "", "cannot read missing.mmd: no such file or directory\n", 2},
		{[]string{"kernel-eval", "-h"}, "Usage: emd kernel-eval FILE\n", "", 0},
		{[]string{"kernel-eval", "--help"}, "Usage: emd kernel-eval FILE\n", "", 0},
		{[]string{"kernel-eval", "--bogus"}, "", "unknown flag --bogus; run emd kernel-eval --help\n", 2},
		{[]string{"kernel-eval", "a", "b"}, "", "kernel-eval accepts one INPUT\n", 2},
		{[]string{"kernel-eval", "missing"}, "", "cannot read missing: no such file or directory\n", 2},
		{[]string{"kernel-eval", "dir"}, "", "cannot read dir: is a directory\n", 2},
		{[]string{"kernel-eval", "cases.txt"}, "", "bad case line 1\n", 2},
		{[]string{"kernel-eval", "cases-ok.txt"}, "9\n", "", 0},
	} {
		out, stderr, code := invoke(t, "", c.args...)
		if out != c.stdout || stderr != c.stderr || code != c.code {
			t.Errorf("%q: stdout=%q stderr=%q exit=%d; want stdout=%q stderr=%q exit=%d", c.args, out, stderr, code, c.stdout, c.stderr, c.code)
		}
	}
}
