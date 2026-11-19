package quadrant_test

import (
	"os"
	"path/filepath"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/quadrant"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/quadrant"
)

func resolveAll(t *testing.T, text string) (*model.Model, []diag.Diagnostic) {
	t.Helper()
	start, ds := parser.Parse([]byte(text), syntax.Preprocess([]byte(text)).Removed)
	require.Empty(t, ds)
	return model.Resolve([]byte(text), start)
}

func resolve(t *testing.T, text string) *model.Model {
	t.Helper()
	m, rs := resolveAll(t, text)
	require.Empty(t, rs)
	return m
}

func TestCorpusResolvesWithoutDiagnostics(t *testing.T) {
	paths, err := filepath.Glob(filepath.Join("..", "..", "..", "corpus", "quadrant", "*", "*.mmd"))
	require.NoError(t, err)
	require.NotEmpty(t, paths)
	for _, path := range paths {
		src, err := os.ReadFile(path)
		require.NoError(t, err)
		_, rs := resolveAll(t, string(src))
		require.Empty(t, rs, path)
	}
}

func TestAxisTextsFillLowThenHigh(t *testing.T) {
	m := resolve(t, "quadrantChart\nx-axis Low Reach --> High Reach\ny-axis Low --> High\n")
	require.Equal(t, "Low Reach", m.XLeft)
	require.Equal(t, "High Reach", m.XRight)
	require.Equal(t, "Low", m.YBottom)
	require.Equal(t, "High", m.YTop)
}

func TestTrailingDelimiterAppendsAnArrowAndKeepsTheOtherField(t *testing.T) {
	m := resolve(t, "quadrantChart\nx-axis A --> B\nx-axis Left -->\ny-axis Solo\n")
	require.Equal(t, "Left ⟶", m.XLeft)
	require.Equal(t, "B", m.XRight)
	require.Equal(t, "Solo", m.YBottom)
	require.Equal(t, "", m.YTop)
}

func TestQuadrantTextsFollowTheirNumber(t *testing.T) {
	m := resolve(t, "quadrantChart\nquadrant-3 Third\nquadrant-1  First  \nquadrant-1 \"Again\"\n")
	require.Equal(t, [4]string{"Again", "", "Third", ""}, m.Quadrants)
}

func TestCoordinatesAreThousandths(t *testing.T) {
	m := resolve(t, "quadrantChart\nA: [0.3, 0.6]\nB: [1, 0]\nC: [0.12345, 0.9999]\nD: [0,5, 0x7]\n")
	var got [][2]int64
	for _, p := range m.Points {
		got = append(got, [2]int64{p.X, p.Y})
	}
	require.Equal(t, [][2]int64{{300, 600}, {1000, 0}, {123, 1000}, {500, 700}}, got)
}

func TestPointsKeepDeclarationOrderAndDuplicates(t *testing.T) {
	m := resolve(t, "quadrantChart\nA: [0.1, 0.1]\nA: [0.2, 0.2]\nB:::c1: [0.3, 0.3]\n")
	require.Len(t, m.Points, 3)
	require.Equal(t, int64(200), m.Points[1].X)
	require.Equal(t, "c1", m.Points[2].Class)
}

func TestInlineStylesOverrideClassStylesAndLateClassesApply(t *testing.T) {
	m := resolve(t, "quadrantChart\nA:::hot: [0.1, 0.1] radius: 3\nB:::hot: [0.2, 0.2]\nC:::none: [0.3, 0.3]\nclassDef hot color: #abc, radius: 20, stroke-width: 4px\n")
	a, b, c := m.Points[0], m.Points[1], m.Points[2]
	require.Equal(t, int64(3), a.Radius)
	require.Equal(t, "#abc", a.Color)
	require.Equal(t, "4px", a.StrokeWidth)
	require.Equal(t, int64(20), b.Radius)
	require.Equal(t, int64(model.NoRadius), c.Radius)
	require.Equal(t, "", c.Color)
}

func TestLaterClassDefinitionReplacesTheWholeEarlierOne(t *testing.T) {
	m := resolve(t, "quadrantChart\nclassDef k radius: 9, color: #fff\nclassDef k stroke-color: #000000\nA:::k: [0.1, 0.1]\n")
	require.Equal(t, int64(model.NoRadius), m.Points[0].Radius)
	require.Equal(t, "", m.Points[0].Color)
	require.Equal(t, "#000000", m.Points[0].StrokeColor)
}

func TestRepeatedKeyTakesTheLastValue(t *testing.T) {
	m := resolve(t, "quadrantChart\nA: [0.1, 0.1] radius: 1, radius: 2\n")
	require.Equal(t, int64(2), m.Points[0].Radius)
}

func TestStyleDiagnostics(t *testing.T) {
	for _, c := range []struct {
		name, style, code, message string
		start, end                 int
	}{
		{"radius word", "radius: big", "quadrant/invalid-radius", "value for radius big is invalid, please use a valid number", 8, 11},
		{"radius missing", "radius", "quadrant/invalid-radius", "value for radius undefined is invalid, please use a valid number", 6, 6},
		{"radius empty", "radius:", "quadrant/invalid-radius", "value for radius  is invalid, please use a valid number", 7, 7},
		{"color", "color: #12", "quadrant/invalid-color", "value for color #12 is invalid, please use a valid hex code", 7, 10},
		{"stroke color", "stroke-color : red", "quadrant/invalid-stroke-color", "value for stroke-color red is invalid, please use a valid hex code", 15, 18},
		{"stroke width", "stroke-width: 3", "quadrant/invalid-stroke-width", "value for stroke-width 3 is invalid, please use a valid number of pixels (eg. 10px)", 14, 15},
		{"unknown key", "Radius: 3", "quadrant/unsupported-style", "style named Radius is not supported.", 0, 6},
	} {
		t.Run(c.name, func(t *testing.T) {
			prefix := "quadrantChart\nA: [0.1, 0.1] "
			_, rs := resolveAll(t, prefix+c.style+"\n")
			require.Len(t, rs, 1)
			require.Equal(t, c.code, rs[0].Code)
			require.Equal(t, c.message, rs[0].Message)
			require.Equal(t, source.Span{Start: len(prefix) + c.start, End: len(prefix) + c.end}, rs[0].Span)
		})
	}
}

func TestClassDefStylesAreValidatedToo(t *testing.T) {
	_, rs := resolveAll(t, "quadrantChart\nclassDef k radius: x, size: 1\n")
	require.Len(t, rs, 2)
	require.Equal(t, "quadrant/invalid-radius", rs[0].Code)
	require.Equal(t, "quadrant/unsupported-style", rs[1].Code)
}

func TestTitlesAndAccessibilityAreTrimmedAndReplaced(t *testing.T) {
	m := resolve(t, "quadrantChart\ntitle   First  \ntitle Second\naccTitle:  T1 \naccDescr: D1\naccDescr {\n D2 \n}\n")
	require.Equal(t, "Second", m.Title)
	require.Equal(t, "T1", m.AccTitle)
	require.Equal(t, "D2", m.AccDescr)
}

func TestFrontmatterTitleIsOverriddenByAStatement(t *testing.T) {
	m := resolve(t, "---\ntitle: From front\n---\nquadrantChart\n")
	require.Equal(t, "From front", m.Title)
	m = resolve(t, "---\ntitle: From front\n---\nquadrantChart\ntitle Later\n")
	require.Equal(t, "Later", m.Title)
}

func TestHonouredConfigKeysAreKeptSortedAndRangeChecked(t *testing.T) {
	text := "---\nconfig:\n  quadrantChart:\n    chartWidth: 900\n    chartHeight: 0\n    titleFontSize: 30\n    unknownKey: 3\n    pointRadius: 7\n    quadrantPadding: 2.5\n    xAxisPosition: bottom\n---\n%%{init: {\"quadrantChart\": {\"chartWidth\": 400, \"titlePadding\": 3}}}%%\nquadrantChart\n"
	m := resolve(t, text)
	got := map[string]int64{}
	var keys []string
	for _, e := range m.Config {
		got[e.Key] = e.Value
		keys = append(keys, e.Key)
	}
	require.Equal(t, []string{"chartWidth", "pointRadius", "titleFontSize", "titlePadding"}, keys)
	require.Equal(t, int64(400), got["chartWidth"])
}

func TestEntitiesDecodeInLabels(t *testing.T) {
	m := resolve(t, "quadrantChart\ntitle a #35; b #amp; c\nquadrant-1 \"x #bogus; y #62; z\"\n")
	require.Equal(t, "a # b & c", m.Title)
	require.Equal(t, "x #bogus; y > z", m.Quadrants[0])
}
