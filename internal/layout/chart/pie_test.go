package chart_test

import (
	"fmt"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/cells"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/layout"
	"github.com/gosuda/elegant-mermaid/internal/layout/chart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func pieCorpusFiles(t *testing.T) []string {
	t.Helper()
	paths, err := filepath.Glob(filepath.Join("..", "..", "..", "corpus", "pie", "*", "*.mmd"))
	require.NoError(t, err)
	require.NotEmpty(t, paths)
	slices.Sort(paths)
	return paths
}

func pieScene(t *testing.T, source string) scene.Scene {
	t.Helper()
	d := layout.ParseDiagram([]byte(source))
	require.Empty(t, d.Diagnostics)
	in, err := d.Input(scene.ProfileVector, scene.Options{})
	require.NoError(t, err)
	s, _, err := layout.Layout(in)
	require.NoError(t, err)
	clause, failed, err := s.Validate()
	require.NoError(t, err)
	require.False(t, failed, clause.Message)
	return s
}

func slicePaths(s scene.Scene) map[string]*scene.Path {
	out := map[string]*scene.Path{}
	for _, g := range s.Groups {
		for _, item := range g.Items {
			if p, ok := item.(*scene.Path); ok {
				out[g.Owner] = p
			}
		}
	}
	return out
}

func arcs(p *scene.Path) []*scene.ArcTo {
	var out []*scene.ArcTo
	for _, c := range p.Commands {
		if a, ok := c.(*scene.ArcTo); ok {
			out = append(out, a)
		}
	}
	return out
}

func sweepsOf(t *testing.T, s scene.Scene, count int) []int32 {
	t.Helper()
	paths := slicePaths(s)
	var out []int32
	for i := range count {
		p, ok := paths[fmt.Sprintf("s%d", i)]
		if !ok {
			out = append(out, 0)
			continue
		}
		out = append(out, arcs(p)[0].Sweep)
	}
	return out
}

func pieSource(header string, values ...string) string {
	var b strings.Builder
	b.WriteString(header + "\n")
	for i, v := range values {
		fmt.Fprintf(&b, "  \"L%d\" : %s\n", i, v)
	}
	return b.String()
}

func labelText(s scene.Scene, id string) (string, bool) {
	for _, l := range s.Labels {
		if l.ID == id {
			return l.Text, true
		}
	}
	return "", false
}

func TestPieCorpusScenesAreValid(t *testing.T) {
	for _, path := range pieCorpusFiles(t) {
		data, err := os.ReadFile(path)
		require.NoError(t, err)
		if len(layout.ParseDiagram(data).Diagnostics) != 0 {
			continue
		}
		t.Run(strings.ReplaceAll(path, string(filepath.Separator), "/"), func(t *testing.T) {
			s := pieScene(t, string(data))
			require.Equal(t, scene.ProfileVector, s.Options.Profile)
			for _, charset := range []cells.Charset{cells.CharsetUnicode, cells.CharsetASCII} {
				_, err := cells.Render(s, cells.Options{Charset: charset})
				require.NoError(t, err)
			}
		})
	}
}

func TestPieSeriesLabels(t *testing.T) {
	for _, path := range pieCorpusFiles(t) {
		data, err := os.ReadFile(path)
		require.NoError(t, err)
		d := layout.ParseDiagram(data)
		if len(d.Diagnostics) != 0 {
			continue
		}
		s := pieScene(t, string(data))
		assertPieSeriesLabels(t, s, path)
	}
}

func assertPieSeriesLabels(t *testing.T, s scene.Scene, path string) {
	t.Helper()
	texts := textContents(s)
	used := map[uint8]bool{}
	for _, g := range s.Groups {
		for _, item := range g.Items {
			switch v := item.(type) {
			case *scene.Rect:
				recordSeries(used, v.Shape)
			case *scene.Path:
				recordSeries(used, v.Shape)
			}
		}
	}
	legend := 0
	for _, l := range s.Labels {
		if strings.HasPrefix(l.ID, "legend.") {
			legend++
			require.True(t, texts[l.Text], "%s: legend %q is not drawn", path, l.Text)
		}
	}
	require.Equal(t, min(legend, 12), len(used), path)
}

func TestPieSweepsSumToTurnAndRoundRemaindersToLargestFractions(t *testing.T) {
	s := pieScene(t, pieSource("pie", "1", "1", "1"))
	require.Equal(t, []int32{21846, 21845, 21845}, sweepsOf(t, s, 3))
	s = pieScene(t, pieSource("pie", "2", "1", "1", "2"))
	require.Equal(t, []int32{21845, 10923, 10923, 21845}, sweepsOf(t, s, 4))
	state := uint32(1)
	next := func(n uint32) string {
		state ^= state << 13
		state ^= state >> 17
		state ^= state << 5
		return fmt.Sprint(state % n)
	}
	for range 60 {
		count := int(state%11) + 2
		values := make([]string, count)
		for i := range values {
			values[i] = next(1000)
		}
		values[0] = "1"
		s = pieScene(t, pieSource("pie", values...))
		var sum int32
		for _, v := range sweepsOf(t, s, count) {
			sum += v
		}
		require.Equal(t, int32(65536), sum, values)
	}
}

func TestPieSlicesStartAtTwelveOClockInDeclarationOrder(t *testing.T) {
	s := pieScene(t, pieSource("pie", "1", "1", "2"))
	paths := slicePaths(s)
	first := arcs(paths["s0"])[0]
	require.Equal(t, int32(65536-16384), first.A0)
	require.Equal(t, int32(16384), first.Sweep)
	second := arcs(paths["s1"])[0]
	require.Equal(t, first.A0+first.Sweep-65536, second.A0)
	third := arcs(paths["s2"])[0]
	require.Equal(t, int32(32768), third.Sweep)
	require.Equal(t, int32(65536-16384+32768-65536), third.A0)
}

func TestPieZeroValuesAndZeroTotal(t *testing.T) {
	s := pieScene(t, pieSource("pie showData", "0", "5", "0"))
	paths := slicePaths(s)
	require.Len(t, paths, 1)
	require.Contains(t, paths, "s1")
	for i, want := range []string{"L0 [0]", "L1 [5]", "L2 [0]"} {
		text, ok := labelText(s, fmt.Sprintf("legend.%d", i))
		require.True(t, ok)
		require.Equal(t, want, text)
	}
	s = pieScene(t, pieSource("pie", "0", "0"))
	require.Empty(t, slicePaths(s))
	require.Len(t, s.Boxes, 1)
	_, ok := labelText(s, "legend.1")
	require.True(t, ok)
}

func TestPieSliverKeepsItsSliceWithoutPercentLabel(t *testing.T) {
	s := pieScene(t, pieSource("pie", "1", "1000", "250"))
	require.Contains(t, slicePaths(s), "s0")
	_, ok := labelText(s, "s0.pct")
	require.False(t, ok)
	text, ok := labelText(s, "s1.pct")
	require.True(t, ok)
	require.Equal(t, "80%", text)
}

func TestPiePercentRoundsHalfUp(t *testing.T) {
	s := pieScene(t, pieSource("pie", "1", "3"))
	for id, want := range map[string]string{"s0.pct": "25%", "s1.pct": "75%"} {
		text, _ := labelText(s, id)
		require.Equal(t, want, text)
	}
	s = pieScene(t, pieSource("pie", "1", "199"))
	text, _ := labelText(s, "s0.pct")
	require.Equal(t, "1%", text)
}

func TestPieSingleSliceIsTwoHalfArcsWithoutRadialLine(t *testing.T) {
	s := pieScene(t, pieSource("pie", "7"))
	p := slicePaths(s)["s0"]
	require.Len(t, arcs(p), 2)
	for _, c := range p.Commands {
		_, line := c.(*scene.LineTo)
		require.False(t, line)
	}
	require.Equal(t, int32(32768), arcs(p)[0].Sweep)
	require.Equal(t, (arcs(p)[0].A0+32768)%65536, arcs(p)[1].A0)
}

func TestPieDonut(t *testing.T) {
	front := "---\nconfig:\n  pie:\n    donutHole: 0.5\n---\n"
	s := pieScene(t, pieSource(front+"pie", "1", "1"))
	for _, p := range slicePaths(s) {
		a := arcs(p)
		require.Len(t, a, 2)
		require.Equal(t, a[0].R/2, a[1].R)
		require.Equal(t, -a[0].Sweep, a[1].Sweep)
		require.Equal(t, (a[0].A0+a[0].Sweep)%65536, a[1].A0)
	}
	s = pieScene(t, pieSource(front+"pie", "1"))
	require.Len(t, arcs(slicePaths(s)["s0"]), 4)
	s = pieScene(t, pieSource("---\nconfig:\n  pie:\n    donutHole: 0.95\n---\npie", "1", "1"))
	require.Len(t, arcs(slicePaths(s)["s0"]), 1)
}

func TestPieTextPositionMovesPercentLabels(t *testing.T) {
	distance := func(source string) int64 {
		s := pieScene(t, source)
		plot := box(t, s, "plot")
		cx, cy := int64(plot.Rect.X)+int64(plot.Rect.W)/2, int64(plot.Rect.Y)+int64(plot.Rect.H)/2
		l := label(t, s, "s0.pct")
		dx := int64(l.Rect.X) + int64(l.Rect.W)/2 - cx
		dy := int64(l.Rect.Y) + int64(l.Rect.H)/2 - cy
		return dx*dx + dy*dy
	}
	near := distance("---\nconfig:\n  pie:\n    textPosition: 0.2\n---\n" + pieSource("pie", "1", "1"))
	far := distance("---\nconfig:\n  pie:\n    textPosition: 0.9\n---\n" + pieSource("pie", "1", "1"))
	require.Less(t, near, far)
}

func TestPieLegendShowDataFormatsValues(t *testing.T) {
	s := pieScene(t, pieSource("pie showData", "42.96", "5", "0.5", "10.050"))
	for i, want := range []string{"L0 [42.96]", "L1 [5]", "L2 [0.5]", "L3 [10.05]"} {
		text, _ := labelText(s, fmt.Sprintf("legend.%d", i))
		require.Equal(t, want, text)
	}
}

func TestPieLongTitleStaysInsideCanvas(t *testing.T) {
	title := "pie title " + strings.Repeat("a very long diagram title ", 8)
	s := pieScene(t, pieSource(title, "1", "2"))
	l := label(t, s, "title")
	require.GreaterOrEqual(t, l.Rect.X, int32(0))
	require.LessOrEqual(t, int64(l.Rect.X)+int64(l.Rect.W), int64(s.Canvas.W))
	require.Greater(t, box(t, s, "plot").Rect.X, int32(0))
}

func TestPieManyLegendRowsStayInsideCanvas(t *testing.T) {
	values := make([]string, 40)
	for i := range values {
		values[i] = "1"
	}
	s := pieScene(t, pieSource("pie", values...))
	for _, l := range s.Labels {
		require.GreaterOrEqual(t, l.Rect.Y, int32(0), l.ID)
		require.LessOrEqual(t, int64(l.Rect.Y)+int64(l.Rect.H), int64(s.Canvas.H), l.ID)
	}
}

func TestPieLayoutRejectsOverflowingValues(t *testing.T) {
	d := layout.ParseDiagram([]byte(pieSource("pie", "99999999999")))
	require.Empty(t, d.Diagnostics)
	_, err := d.Input(scene.ProfileVector, scene.Options{})
	require.ErrorIs(t, err, chart.ErrOverflow)
	d = layout.ParseDiagram([]byte(pieSource("pie", "2000000", "2000000")))
	_, err = d.Input(scene.ProfileVector, scene.Options{})
	require.ErrorIs(t, err, chart.ErrOverflow)
}

func TestPieIgnoresRequestedProfile(t *testing.T) {
	d := layout.ParseDiagram([]byte(pieSource("pie", "1", "2")))
	vector, err := d.Input(scene.ProfileVector, scene.Options{})
	require.NoError(t, err)
	cell, err := d.Input(scene.ProfileCell, scene.Options{})
	require.NoError(t, err)
	require.Equal(t, vector, cell)
	require.Equal(t, scene.ProfileVector, cell.Profile)
}

func TestPieSliceBoxesContainTheirArcsAndLabels(t *testing.T) {
	s := pieScene(t, pieSource("pie", "3", "2", "1", "5"))
	for id, p := range slicePaths(s) {
		b := box(t, s, id).Rect
		for _, c := range p.Commands {
			var at geom.Point
			switch v := c.(type) {
			case *scene.MoveTo:
				at = v.P
			case *scene.LineTo:
				at = v.P
			default:
				continue
			}
			in, err := geom.Contains(b, geom.Rect{X: at.X, Y: at.Y})
			require.NoError(t, err)
			require.True(t, in, id)
		}
	}
}
