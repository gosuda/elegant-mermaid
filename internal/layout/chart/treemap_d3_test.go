package chart_test

import (
	"encoding/json"
	"os"
	"os/exec"
	"path/filepath"
	"slices"
	"strconv"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/layout"
	model "github.com/gosuda/elegant-mermaid/internal/model/treemap"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/treemap"
)

const d3Tolerance = 64

type d3Node struct {
	ID       string    `json:"id"`
	Value    *float64  `json:"value,omitempty"`
	Children []*d3Node `json:"children,omitempty"`
}

type d3Rect [4]int64

func d3Script(t *testing.T) string {
	t.Helper()
	if _, err := exec.LookPath("node"); err != nil {
		t.Skip("node is not installed")
	}
	script, err := filepath.Abs(filepath.Join("..", "..", "..", "tools", "upstream-oracle", "d3.mjs"))
	require.NoError(t, err)
	if _, err := os.Stat(filepath.Join(filepath.Dir(script), "node_modules", "d3-hierarchy")); err != nil {
		t.Skip("tools/upstream-oracle has no installed d3-hierarchy")
	}
	return script
}

func valueSum(n *model.Node) int64 {
	if len(n.Children) == 0 {
		return n.Value
	}
	var total int64
	for _, c := range n.Children {
		total += valueSum(c)
	}
	return total
}

func byValueThenDeclaration(a, b *model.Node) int {
	sa, sb := valueSum(a), valueSum(b)
	switch {
	case sa > sb:
		return -1
	case sa < sb:
		return 1
	}
	return a.Index - b.Index
}

func d3Children(nodes []*model.Node, ids map[*model.Node]string) []*d3Node {
	sorted := slices.Clone(nodes)
	slices.SortStableFunc(sorted, byValueThenDeclaration)
	out := make([]*d3Node, len(sorted))
	for i, n := range sorted {
		out[i] = &d3Node{ID: ids[n], Children: d3Children(n.Children, ids)}
		if len(n.Children) == 0 {
			v := float64(n.Value)
			out[i].Value = &v
		}
	}
	return out
}

func preorderIDs(roots []*model.Node) map[*model.Node]string {
	ids := map[*model.Node]string{}
	var walk func(n *model.Node)
	walk = func(n *model.Node) {
		ids[n] = "n" + strconv.Itoa(len(ids))
		for _, c := range n.Children {
			walk(c)
		}
	}
	for _, r := range roots {
		walk(r)
	}
	return ids
}

func runD3(t *testing.T, script string, description any) map[string]d3Rect {
	t.Helper()
	payload, err := json.Marshal(description)
	require.NoError(t, err)
	file := filepath.Join(t.TempDir(), "tree.json")
	require.NoError(t, os.WriteFile(file, payload, 0o600))
	out, err := exec.Command("node", script, "treemap", file).Output()
	require.NoError(t, err)
	rects := map[string]d3Rect{}
	for line := range strings.SplitSeq(strings.TrimSpace(string(out)), "\n") {
		fields := strings.Fields(line)
		require.Len(t, fields, 5, line)
		var r d3Rect
		for i := range r {
			r[i], err = strconv.ParseInt(fields[i+1], 10, 64)
			require.NoError(t, err)
		}
		rects[fields[0]] = r
	}
	return rects
}

func hasConfigKey(m *model.Model, key string) bool {
	return slices.ContainsFunc(m.Config, func(c model.ConfigEntry) bool { return c.Key == key })
}

func absDiff(a, b int64) int64 {
	if a < b {
		return b - a
	}
	return a - b
}

func TestTreemapLeavesMatchD3WithinOnePixel(t *testing.T) {
	script := d3Script(t)
	compared, worst := 0, int64(0)
	for _, path := range treemapCorpusFiles(t) {
		data, err := os.ReadFile(path)
		require.NoError(t, err)
		ast, parsed := parser.Parse(data, syntax.Preprocess(data).Removed)
		m, resolved := model.Resolve(data, ast)
		if len(parsed)+len(resolved) > 0 || len(m.Roots) == 0 || hasConfigKey(m, "padding") {
			continue
		}
		// sceneOf skips the whole test on a rejected source, so leave out
		// files the layout rejects (config warnings) and compare the rest.
		if len(layout.ParseDiagram(data).Diagnostics) != 0 {
			continue
		}
		s := sceneOf(t, string(data), scene.ProfileVector)
		root := box(t, s, "root").Rect
		description := map[string]any{
			"width": root.W / 64, "height": root.H / 64,
			"tree": &d3Node{ID: "root", Children: d3Children(m.Roots, preorderIDs(m.Roots))},
		}
		want := runD3(t, script, description)
		for _, b := range s.Boxes {
			expected, leaf := want[b.ID]
			if !leaf {
				continue
			}
			compared++
			got := d3Rect{int64(b.Rect.X), int64(b.Rect.Y - root.Y), int64(b.Rect.X + b.Rect.W), int64(b.Rect.Y + b.Rect.H - root.Y)}
			for i := range got {
				worst = max(worst, absDiff(got[i], expected[i]))
				require.LessOrEqual(t, absDiff(got[i], expected[i]), int64(d3Tolerance), "%s %s coordinate %d: ours %v d3 %v", path, b.ID, i, got, expected)
			}
		}
	}
	require.Positive(t, compared)
	t.Logf("compared %d leaf rectangles, largest deviation %d units", compared, worst)
}
