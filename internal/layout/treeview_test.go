package layout

import (
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const treeviewDemo = "treeView-beta\n  src/\n      a.js ## d\n  b\n"

func treeviewLayoutOf(t *testing.T, src string, profile scene.Profile) (scene.Scene, []diag.Diagnostic) {
	t.Helper()
	d := ParseDiagram([]byte(src))
	require.Empty(t, d.Diagnostics)
	in, err := d.Input(profile, scene.Options{})
	require.NoError(t, err)
	s, ds, err := Layout(in)
	require.NoError(t, err)
	clause, failed, err := s.Validate()
	require.NoError(t, err)
	require.False(t, failed, clause)
	return s, ds
}

func texts(s scene.Scene) []string {
	var out []string
	for _, g := range s.Groups {
		for _, item := range g.Items {
			if text, ok := item.(*scene.Text); ok {
				out = append(out, text.Lines[0][0].Text)
			}
		}
	}
	return out
}

func TestTreeviewVectorGeometry(t *testing.T) {
	s, _ := treeviewLayoutOf(t, treeviewDemo, scene.ProfileVector)
	label, body := measure.ForRole(measure.RoleLabel), measure.ForRole(measure.RoleBody)
	width := func(m measure.Metric, text string) int32 {
		w, err := m.TextWidth(text)
		require.NoError(t, err)
		return w + 640
	}
	require.Equal(t, []geom.Rect{
		{X: 1024, Y: 1024, W: width(label, "/"), H: 1920},
		{X: 1984, Y: 2944, W: width(label, "src"), H: 1920},
		{X: 2944, Y: 4864, W: width(body, "a.js"), H: 1920},
		{X: 1984, Y: 6784, W: width(body, "b"), H: 1920},
	}, []geom.Rect{s.Boxes[0].Rect, s.Boxes[1].Rect, s.Boxes[2].Rect, s.Boxes[3].Rect})
	require.Len(t, s.Boxes, 4)
	require.Equal(t, geom.Size{W: s.Canvas.W, H: 4*1920 + 2*1024}, s.Canvas)
}

func TestTreeviewVectorGuidesAreRuleLinesOfConfiguredThickness(t *testing.T) {
	s, _ := treeviewLayoutOf(t, "---\nconfig:\n  treeView:\n    lineThickness: 3\n    rowIndent: 80\n---\ntreeView-beta\n a\n  b\n", scene.ProfileVector)
	var widths []scene.Width
	for _, g := range s.Groups {
		if g.Role != scene.GroupRoleEdge {
			continue
		}
		line, ok := g.Items[0].(*scene.Polyline)
		require.True(t, ok)
		require.Equal(t, "rule", line.Style)
		widths = append(widths, line.Width)
	}
	require.Equal(t, []scene.Width{{Kind: scene.WidthUnits, Units: 192}, {Kind: scene.WidthUnits, Units: 192}}, widths)
	require.Equal(t, int32(1024+80*64+320), s.Boxes[1].Rect.X)
}

func TestTreeviewDescriptionsAlignInOneColumn(t *testing.T) {
	s, _ := treeviewLayoutOf(t, "treeView-beta\n a ## x\n  bbbbbbbb ## y\n", scene.ProfileVector)
	var xs []int32
	for _, g := range s.Groups {
		for _, item := range g.Items {
			if text, ok := item.(*scene.Text); ok && text.Style == "text-muted" {
				xs = append(xs, text.Rect.X)
			}
		}
	}
	require.Len(t, xs, 2)
	require.Equal(t, xs[0], xs[1])
}

func TestTreeviewDirectoriesUseLabelRoleAndFilesBodyRole(t *testing.T) {
	s, _ := treeviewLayoutOf(t, treeviewDemo, scene.ProfileVector)
	roles := map[string]scene.TextRole{}
	for _, g := range s.Groups {
		for _, item := range g.Items {
			if text, ok := item.(*scene.Text); ok {
				roles[text.Lines[0][0].Text] = text.Role
			}
		}
	}
	require.Equal(t, scene.TextRoleLabel, roles["src"])
	require.Equal(t, scene.TextRoleBody, roles["a.js"])
	require.Equal(t, scene.TextRoleBody, roles["d"])
}

func TestTreeviewHighlightBandSpansToTheRightEdge(t *testing.T) {
	s, _ := treeviewLayoutOf(t, "treeView-beta\n a :::highlight\n b\n", scene.ProfileVector)
	var bands []geom.Rect
	for _, g := range s.Groups {
		for _, item := range g.Items {
			if r, ok := item.(*scene.Rect); ok {
				bands = append(bands, r.Rect)
			}
		}
	}
	require.Len(t, bands, 1)
	require.Equal(t, s.Boxes[1].Rect.X, bands[0].X)
	require.Equal(t, s.Boxes[1].Rect.Y, bands[0].Y)
	require.Greater(t, bands[0].X+bands[0].W, s.Boxes[1].Rect.X+s.Boxes[1].Rect.W-1)
}

func TestTreeviewMissingIconIsReported(t *testing.T) {
	_, ds := treeviewLayoutOf(t, "treeView-beta\n a icon(nope:x)\n b icon()\n", scene.ProfileVector)
	require.Len(t, ds, 1)
	require.Equal(t, "icon/pack-missing", ds[0].Code)
	require.Contains(t, ds[0].Message, "nope:x")
}

func TestTreeviewCellDrawsGuidePrefixesAndDirectorySlash(t *testing.T) {
	s, _ := treeviewLayoutOf(t, treeviewDemo, scene.ProfileCell)
	require.Equal(t, []string{"/", "├── ", "src/", "│   └── ", "a.js", "d", "└── ", "b"}, texts(s))
	require.Equal(t, int32(1), s.Boxes[0].Rect.H)
	require.Equal(t, int32(1+4), s.Boxes[1].Rect.X)
	require.Equal(t, int32(1+8), s.Boxes[2].Rect.X)
}

func TestTreeviewCellAndVectorShareIdentities(t *testing.T) {
	vector, _ := treeviewLayoutOf(t, treeviewDemo, scene.ProfileVector)
	cell, _ := treeviewLayoutOf(t, treeviewDemo, scene.ProfileCell)
	require.Len(t, cell.Boxes, len(vector.Boxes))
	for i := range vector.Boxes {
		require.Equal(t, vector.Boxes[i].ID, cell.Boxes[i].ID)
	}
	for i := range vector.Routes {
		require.Equal(t, vector.Routes[i].ID, cell.Routes[i].ID)
		require.Equal(t, vector.Routes[i].From, cell.Routes[i].From)
		require.Equal(t, vector.Routes[i].To, cell.Routes[i].To)
	}
}

func TestTreeviewModelDumpNamesBoxesRoutesAndLabels(t *testing.T) {
	dump := diagramModelDump(t, treeviewDemo)
	require.Contains(t, dump, `{"id":"n0","role":"node","parent":"","exclusive":true,"shape":"directory"}`)
	require.Contains(t, dump, `{"id":"n2","role":"node","parent":"","exclusive":true,"shape":"file"}`)
	require.Contains(t, dump, `{"id":"e1","from":"n1","to":"n2","orthogonal":true,"marker_end":"none"}`)
	require.Contains(t, dump, `"owner":"n2","text":"a.js"`)
	require.Contains(t, dump, `"owner":"n2","text":"d"`)
	require.Equal(t, 4, strings.Count(dump, `"role":"node"`))
}

func TestTreeviewLimitsApply(t *testing.T) {
	d := ParseDiagram([]byte("treeView-beta\n a\n b\n"))
	in, err := d.Input(scene.ProfileVector, scene.Options{Limits: scene.Limits{MaxNodes: 2}})
	require.NoError(t, err)
	_, _, err = Layout(in)
	require.Error(t, err)
}
