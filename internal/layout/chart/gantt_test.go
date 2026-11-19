package chart_test

import (
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/cells"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/layout"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func ganttCorpusFiles(t *testing.T) []string {
	t.Helper()
	paths, err := filepath.Glob(filepath.Join("..", "..", "..", "corpus", "gantt", "*", "*.mmd"))
	require.NoError(t, err)
	require.NotEmpty(t, paths)
	slices.Sort(paths)
	return paths
}

func ganttSceneOf(t *testing.T, source string, profile scene.Profile) scene.Scene {
	t.Helper()
	d := layout.ParseDiagram([]byte(source))
	for _, diagnostic := range d.Diagnostics {
		require.NotEqual(t, "error", diagnostic.Severity.String(), diagnostic.Code+": "+diagnostic.Message)
	}
	in, err := d.Input(profile, scene.Options{})
	require.NoError(t, err)
	s, _, err := layout.Layout(in)
	require.NoError(t, err)
	return s
}

func ganttBox(t *testing.T, s scene.Scene, id string) geom.Rect {
	t.Helper()
	for _, b := range s.Boxes {
		if b.ID == id {
			return b.Rect
		}
	}
	t.Fatalf("no box %q", id)
	return geom.Rect{}
}

func ganttLabels(s scene.Scene, prefix string) []string {
	var out []string
	for _, l := range s.Labels {
		if strings.HasPrefix(l.ID, prefix) {
			out = append(out, l.Text)
		}
	}
	return out
}

func ganttBands(s scene.Scene) []geom.Rect {
	var out []geom.Rect
	for _, g := range s.Groups {
		for _, item := range g.Items {
			if r, ok := item.(*scene.Rect); ok && r.Style == "band" && g.Role == scene.GroupRoleDecor {
				out = append(out, r.Rect)
			}
		}
	}
	return out
}

func TestGanttCorpusScenesAreValid(t *testing.T) {
	for _, path := range ganttCorpusFiles(t) {
		data, err := os.ReadFile(path)
		require.NoError(t, err)
		d := layout.ParseDiagram(data)
		failed := false
		for _, diagnostic := range d.Diagnostics {
			failed = failed || diagnostic.Severity.String() == "error"
		}
		if failed {
			continue
		}
		for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
			t.Run(strings.ReplaceAll(path, string(filepath.Separator), "/")+"/"+profile.String(), func(t *testing.T) {
				s := ganttSceneOf(t, string(data), profile)
				clause, invalid, err := s.Validate()
				require.NoError(t, err)
				require.False(t, invalid, clause.Message)
				if profile == scene.ProfileCell {
					result, err := cells.Render(s, cells.Options{})
					require.NoError(t, err)
					require.Zero(t, result.RefusedClusters)
				}
			})
		}
	}
}

func TestGanttVectorGeometry(t *testing.T) {
	s := ganttSceneOf(t, "gantt\ndateFormat YYYY-MM-DD\nsection A\nOne :a, 2014-01-01, 30d\nTwo :after a, 10d\n", scene.ProfileVector)
	require.Equal(t, geom.Rect{X: 0, Y: 3200, W: 76800, H: 2*1536 + 1536}, ganttBox(t, s, "plot"))
	require.Equal(t, geom.Rect{X: 0, Y: 3200, W: 76800, H: 1536}, ganttBox(t, s, "s0"))
	require.Equal(t, geom.Rect{X: 4800, Y: 3200 + 1536, W: 67200 * 30 / 40, H: 1280}, ganttBox(t, s, "t0"))
	require.Equal(t, geom.Rect{X: 4800 + 67200*30/40, Y: 3200 + 2*1536, W: 67200 * 10 / 40, H: 1280}, ganttBox(t, s, "t1"))
	require.Equal(t, geom.Size{W: 76800, H: 3200 + 3*1536 + 3200}, s.Canvas)
}

func TestGanttAutoTicksUseTwoDayStep(t *testing.T) {
	s := ganttSceneOf(t, "gantt\ndateFormat YYYY-MM-DD\nOne :a, 2014-01-01, 30d\n", scene.ProfileVector)
	ticks := ganttLabels(s, "x.t")
	require.Len(t, ticks, 16)
	require.Equal(t, []string{"2014-01-01", "2014-01-03", "2014-01-05"}, ticks[:3])
	require.Equal(t, "2014-01-31", ticks[15])
}

func TestGanttExplicitWeekTicksHonourWeekday(t *testing.T) {
	source := "gantt\ndateFormat YYYY-MM-DD\nweekday monday\ntickInterval 2week\nOne :a, 2014-01-01, 30d\n"
	s := ganttSceneOf(t, source, scene.ProfileVector)
	require.Equal(t, []string{"2014-01-13", "2014-01-27"}, ganttLabels(s, "x.t"))
	s = ganttSceneOf(t, strings.Replace(source, "2week", "1week", 1), scene.ProfileVector)
	require.Equal(t, []string{"2014-01-06", "2014-01-13", "2014-01-20", "2014-01-27"}, ganttLabels(s, "x.t"))
}

func TestGanttExcludedWeekendIsOneBand(t *testing.T) {
	s := ganttSceneOf(t, "gantt\ndateFormat YYYY-MM-DD\nexcludes weekends\nOne :a, 2014-01-03, 3d\n", scene.ProfileVector)
	day := int32(67200 / 5)
	require.Equal(t, []geom.Rect{{X: 4800 + day, Y: 3200, W: 2 * day, H: 1536}}, ganttBands(s))
}

func TestGanttBarEndsBeforeTrailingExcludedDays(t *testing.T) {
	s := ganttSceneOf(t, "gantt\ndateFormat YYYY-MM-DD\nexcludes weekends\nOne :a, 2014-01-03, 1d\nTwo :b, 2014-01-03, 3d\n", scene.ProfileVector)
	one := ganttBox(t, s, "t0")
	two := ganttBox(t, s, "t1")
	require.Equal(t, int32(4800), one.X)
	require.Equal(t, int32(4800), two.X)
	require.Less(t, one.W, two.W)
	require.Equal(t, int32(67200/5), one.W)
}

func TestGanttMilestoneAndVertGeometry(t *testing.T) {
	source := "gantt\ndateFormat YYYY-MM-DD\nOne :a, 2014-01-01, 10d\nMark :milestone, m, 2014-01-06, 0d\nLine :vert, v, 2014-01-11, 0d\n"
	s := ganttSceneOf(t, source, scene.ProfileVector)
	mark := ganttBox(t, s, "t1")
	require.Equal(t, geom.Size{W: 1280, H: 1280}, geom.Size{W: mark.W, H: mark.H})
	require.Equal(t, int32(4800+67200/2-640), mark.X)
	vert := ganttBox(t, s, "t2")
	require.Equal(t, int32(128), vert.W)
	require.Equal(t, int32(4800+67200-64), vert.X)
	require.Equal(t, int32(2*1536), vert.H)
	require.Equal(t, []string{"One", "Mark", "Line"}, ganttLabels(s, "t"))
	label := s.Labels[slices.IndexFunc(s.Labels, func(l scene.Label) bool { return l.ID == "t2.label" })].Rect
	require.Greater(t, label.Y, s.Canvas.H-3200)
}

func TestGanttTagStylePrecedence(t *testing.T) {
	s := ganttSceneOf(t, "gantt\ndateFormat YYYY-MM-DD\nsection S\nA :crit, done, 2014-01-01, 1d\nB :done, active, 2014-01-02, 1d\nC :active, 2014-01-03, 1d\nD :2014-01-04, 1d\n", scene.ProfileVector)
	var styles []string
	for _, g := range s.Groups {
		if g.Role != scene.GroupRoleNode || !strings.HasPrefix(g.Owner, "t") {
			continue
		}
		for _, item := range g.Items {
			if r, ok := item.(*scene.Rect); ok && r.Style != "plate" {
				styles = append(styles, r.Style)
			}
		}
	}
	require.Equal(t, []string{"error", "success", "note", "series"}, styles)
}

func TestGanttCellTopAxisKeepsTitleRowFree(t *testing.T) {
	s := ganttSceneOf(t, "gantt\ntitle T\ndateFormat YYYY-MM-DD\ntopAxis\nOne :a, 2014-01-01, 30d\n", scene.ProfileCell)
	top := ganttLabels(s, "xt.t")
	require.NotEmpty(t, top)
	for _, l := range s.Labels {
		if strings.HasPrefix(l.ID, "xt.t") && len(l.Lines) > 0 {
			require.Equal(t, int32(1), l.Rect.Y)
		}
	}
	result, err := cells.Render(s, cells.Options{})
	require.NoError(t, err)
	require.Zero(t, result.RefusedClusters)
}

func TestGanttTickBudget(t *testing.T) {
	d := layout.ParseDiagram([]byte("gantt\ndateFormat YYYY-MM-DD\nOne :a, 0001-01-01, 90000y\n"))
	in, err := d.Input(scene.ProfileVector, scene.Options{})
	require.NoError(t, err)
	_, diagnostics, err := layout.Layout(in)
	require.NoError(t, err)
	require.Len(t, diagnostics, 1)
	require.Equal(t, "layout/budget-exhausted", diagnostics[0].Code)
}

func TestGanttEmptyDiagramLaysOut(t *testing.T) {
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		s := ganttSceneOf(t, "gantt\ntitle Empty\n", profile)
		clause, invalid, err := s.Validate()
		require.NoError(t, err)
		require.False(t, invalid, clause.Message)
		require.Equal(t, "1970-01-01", ganttLabels(s, "x.t")[0])
	}
}
