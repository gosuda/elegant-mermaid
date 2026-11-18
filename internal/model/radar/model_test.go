package radar

import (
	"encoding/json"
	"os"
	"path/filepath"
	"slices"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/radar"
)

func resolve(src string) (*Model, []diag.Diagnostic) {
	prep := syntax.Preprocess([]byte(src))
	start, parsed := syn.Parse([]byte(src), prep.Removed)
	model, resolved := Resolve([]byte(src), start)
	return model, append(parsed, resolved...)
}

func codes(ds []diag.Diagnostic) []string {
	out := make([]string, len(ds))
	for i, d := range ds {
		out[i] = d.Code
	}
	return out
}

func errors(ds []diag.Diagnostic) []diag.Diagnostic {
	return slices.DeleteFunc(slices.Clone(ds), func(d diag.Diagnostic) bool { return d.Severity != diag.SeverityError })
}

func TestAcceptanceMatchesTheUpstreamParser(t *testing.T) {
	for _, tc := range []struct {
		name   string
		src    string
		accept bool
	}{
		{"float", "radar-beta\n axis A, B\n curve c {1.5, 2}\n", true},
		{"max float", "radar-beta\n axis A, B\n curve c {1, 2}\n max 2.5\n", true},
		{"colon header", "radar-beta:\n axis A, B\n", true},
		{"colon sep", "radar-beta :\n axis A, B\n", true},
		{"header only", "radar-beta\n", true},
		{"no newline", "radar-beta", true},
		{"axis same line", "radar-beta axis A, B", true},
		{"two statements one line", "radar-beta\n axis A curve c {1,2}\n", true},
		{"semicolon", "radar-beta\n axis A; axis B\n", false},
		{"curve name true", "radar-beta\n axis A\n curve true {1}\n", false},
		{"curve name circle", "radar-beta\n axis A\n curve circle {1}\n", false},
		{"axis name 3d", "radar-beta\n axis 3d\n", false},
		{"axis name a-b", "radar-beta\n axis a-b, c_d\n curve x {1,2}\n", true},
		{"axis name dash end", "radar-beta\n axis a-\n", false},
		{"axis keyword name", "radar-beta\n axis axis\n", false},
		{"axis name max", "radar-beta\n axis max, min\n", false},
		{"trailing comma", "radar-beta\n axis A,\n", false},
		{"entry newline", "radar-beta\n axis A, B\n curve c {\n 1,\n 2\n }\n", true},
		{"entry newline before comma", "radar-beta\n axis A, B\n curve c {\n 1\n ,2\n }\n", false},
		{"mix", "radar-beta\n axis A, B\n curve c {A 1, 2}\n", false},
		{"mix2", "radar-beta\n axis A, B\n curve c {1, B 2}\n", false},
		{"detailed colon", "radar-beta\n axis A, B\n curve c {A: 1, B: 2}\n", true},
		{"empty entries", "radar-beta\n axis A\n curve c {}\n", false},
		{"trailing comma entries", "radar-beta\n axis A\n curve c {1,}\n", false},
		{"unknown axis ref", "radar-beta\n axis A\n curve c {Z: 1}\n", false},
		{"unknown extra axis ref", "radar-beta\n axis A\n curve c {A: 1, Z: 1}\n", true},
		{"curve before axis", "radar-beta\n curve c {A: 1}\n axis A\n", true},
		{"curve before axis positional", "radar-beta\n curve c {1}\n axis A\n", true},
		{"options", "radar-beta\n axis A\n showLegend false\n ticks 3, max 5, min 1\n", true},
		{"options comma", "radar-beta\n axis A\n curve c {2}\n ticks 3, max 5\n", true},
		{"showLegend bad", "radar-beta\n axis A\n showLegend yes\n", false},
		{"graticule bad", "radar-beta\n axis A\n graticule square\n", false},
		{"ticks zero", "radar-beta\n axis A\n curve c {1}\n ticks 0\n", true},
		{"ticks frac", "radar-beta\n axis A\n curve c {1}\n ticks 2.5\n", true},
		{"ticks big", "radar-beta\n axis A\n curve c {1}\n ticks 100\n", true},
		{"title acc", "radar-beta\n title Foo\n accTitle: t\n accDescr: d\n axis A\n", true},
		{"title no space", "radar-beta\n titlefoo\n axis A\n", false},
		{"label empty", "radar-beta\n axis A[\"\"]\n curve c[\"\"]{1}\n", true},
		{"label single quote", "radar-beta\n axis A['x y']\n", true},
		{"label no quotes", "radar-beta\n axis A[x]\n", false},
		{"comment", "radar-beta %% hi\n axis A %% c\n %% full\n curve c {1} %% x\n", true},
		{"leading blank", "\n\nradar-beta\n axis A\n", true},
		{"int leading zero", "radar-beta\n axis A\n curve c {01}\n", false},
		{"int 0.5", "radar-beta\n axis A\n curve c {0.5}\n", true},
		{"int 1.", "radar-beta\n axis A\n curve c {1.}\n", false},
		{"int .5", "radar-beta\n axis A\n curve c {.5}\n", false},
		{"curve no braces", "radar-beta\n axis A\n curve c 1\n", false},
		{"axis no names", "radar-beta\n axis\n", false},
		{"detailed no colon", "radar-beta\n axis A\n curve c {A 1}\n", true},
		{"detailed repeated", "radar-beta\n axis A, B\n curve c {A: 1, A: 2, B: 3}\n", true},
		{"many on one line", "radar-beta\n axis A curve c {1} showLegend true\n", true},
		{"ticks neg", "radar-beta\n axis A\n ticks -1\n", false},
		{"id with dot", "radar-beta\n axis A.B\n", false},
		{"unicode name", "radar-beta\n axis é\n", false},
		{"crlf", "radar-beta\r\n axis A\r\n curve c {1}\r\n", true},
		{"lone cr", "radar-beta\r axis A\r curve c {1}\r", true},
		{"subset", "radar-beta\n axis A, B, C\n curve c {A: 1, B: 4}\n", false},
	} {
		_, ds := resolve(tc.src)
		require.Equal(t, tc.accept, len(errors(ds)) == 0, "%s: %v", tc.name, ds)
	}
}

func TestCorpusVerdicts(t *testing.T) {
	data, err := os.ReadFile(filepath.Join("..", "..", "..", "corpus", "verdicts.json"))
	require.NoError(t, err)
	var verdicts map[string]struct {
		Accept bool `json:"accept"`
		Kind   string
	}
	require.NoError(t, json.Unmarshal(data, &verdicts))
	paths, err := filepath.Glob(filepath.Join("..", "..", "..", "corpus", "radar", "*", "*.mmd"))
	require.NoError(t, err)
	require.NotEmpty(t, paths)
	for _, path := range paths {
		src, err := os.ReadFile(path)
		require.NoError(t, err)
		key, err := filepath.Rel(filepath.Join("..", "..", ".."), path)
		require.NoError(t, err)
		verdict, found := verdicts[filepath.ToSlash(key)]
		require.True(t, found, key)
		_, ds := resolve(string(src))
		require.Equal(t, verdict.Accept, len(errors(ds)) == 0, "%s: %v", key, ds)
	}
}

func TestLabelsDefaultToNamesOnly(t *testing.T) {
	m, ds := resolve("radar-beta\naxis A[\"\"], B, C[\"See\"]\ncurve x[\"\"]{1,2,3}, y{3,2,1}\n")
	require.Empty(t, errors(ds))
	var axes, curves []string
	for _, a := range m.Axes {
		axes = append(axes, a.Label)
	}
	for _, c := range m.Curves {
		curves = append(curves, c.Label)
	}
	require.Equal(t, []string{"", "B", "See"}, axes)
	require.Equal(t, []string{"", "y"}, curves)
}

func TestPositionalCurvesKeepAllValues(t *testing.T) {
	m, ds := resolve("radar-beta\naxis A, B\ncurve x{1,2,3.0005}, y{4}\n")
	require.Empty(t, errors(ds))
	require.Equal(t, []int64{1000, 2000, 3001}, m.Curves[0].Values)
	require.Equal(t, []int64{4000}, m.Curves[1].Values)
}

func TestKeyedCurvesFollowAxisOrderAndFirstEntryWins(t *testing.T) {
	m, ds := resolve("radar-beta\ncurve k{C: 9, A 1, B: 2, A: 7, D: 5}\naxis A, B, C\n")
	require.Empty(t, errors(ds))
	require.Equal(t, []int64{1000, 2000, 9000}, m.Curves[0].Values)
}

func TestDuplicateAxesStayOrdered(t *testing.T) {
	m, ds := resolve("radar-beta\naxis A, A\ncurve k{A: 3}\n")
	require.Empty(t, errors(ds))
	require.Len(t, m.Axes, 2)
	require.Equal(t, []int64{3000, 3000}, m.Curves[0].Values)
}

func TestKeyedCurveErrors(t *testing.T) {
	_, ds := resolve("radar-beta\ncurve k{A: 1}\n")
	require.Equal(t, []string{"radar/axes-required"}, codes(ds))
	require.Equal(t, "keyed curve requires declared axes", ds[0].Message)
	_, ds = resolve("radar-beta\naxis A, b[\"Bee\"]\ncurve k{A: 1}\n")
	require.Equal(t, []string{"radar/missing-axis-entry"}, codes(ds))
	require.Equal(t, "missing entry for axis Bee", ds[0].Message)
	require.Equal(t, 34, ds[0].Span.Start)
}

func TestOptionsLastDeclarationWins(t *testing.T) {
	m, ds := resolve("radar-beta\naxis A\ncurve c{1}\nshowLegend false\nticks 3\nticks 4, max 9, max 8\nmin 1\ngraticule polygon\ngraticule circle\nshowLegend true\n")
	require.Empty(t, ds)
	o := m.Options
	require.True(t, o.ShowLegend)
	require.Equal(t, int64(4000), o.Ticks)
	require.True(t, o.HasMax)
	require.Equal(t, int64(8000), o.Max)
	require.Equal(t, int64(1000), o.Min)
	require.Equal(t, GraticuleCircle, o.Graticule)
}

func TestOptionDefaults(t *testing.T) {
	m, ds := resolve("radar-beta\naxis A\ncurve c{1}\n")
	require.Empty(t, ds)
	require.Equal(t, Options{ShowLegend: true, Ticks: 5000}, m.Options)
}

func TestTicksAboveTheCapAreClamped(t *testing.T) {
	m, ds := resolve("radar-beta\naxis A\ncurve c{1}\nticks 33\n")
	require.Equal(t, []string{"radar/ticks-clamped"}, codes(ds))
	require.Equal(t, diag.SeverityWarning, ds[0].Severity)
	require.Equal(t, "ticks 33 exceeds 32; using 32", ds[0].Message)
	require.Equal(t, int64(32000), m.Options.Ticks)
	m, ds = resolve("radar-beta\naxis A\ncurve c{1}\nticks 32\n")
	require.Empty(t, ds)
	require.Equal(t, int64(32000), m.Options.Ticks)
	m, ds = resolve("radar-beta\naxis A\ncurve c{1}\nticks 0\n")
	require.Empty(t, ds)
	require.Equal(t, int64(0), m.Options.Ticks)
}

func TestEmptyRange(t *testing.T) {
	src := "radar-beta\naxis A\ncurve c{0}\n"
	_, ds := resolve(src)
	require.Equal(t, []string{"radar/empty-range"}, codes(ds))
	require.Equal(t, diag.SeverityError, ds[0].Severity)
	require.Equal(t, 0, ds[0].Span.Start)
	_, ds = resolve("radar-beta\naxis A\ncurve c{4}\nmin 4\n")
	require.Equal(t, []string{"radar/empty-range"}, codes(ds))
	require.Equal(t, 33, ds[0].Span.Start)
	_, ds = resolve("radar-beta\naxis A\ncurve c{4}\nmin 1\nmax 1\n")
	require.Equal(t, []string{"radar/empty-range"}, codes(ds))
	require.Equal(t, 39, ds[0].Span.Start)
	_, ds = resolve("radar-beta\naxis A\nmax 0\n")
	require.Equal(t, []string{"radar/empty-range"}, codes(ds))
	_, ds = resolve("radar-beta\naxis A\n")
	require.Empty(t, ds)
	_, ds = resolve("radar-beta\naxis A\ncurve c{-1}\n")
	require.NotEmpty(t, ds)
}

func TestMetadataAndFrontmatter(t *testing.T) {
	m, ds := resolve("---\ntitle: Front\n---\nradar-beta\naxis A\n")
	require.Empty(t, ds)
	require.Equal(t, "Front", m.Title)
	m, ds = resolve("---\ntitle: Front\n---\nradar-beta\ntitle  Body #amp; x\naccTitle: at\naccDescr: ad\naxis A\n")
	require.Empty(t, ds)
	require.Equal(t, "Body & x", m.Title)
	require.Equal(t, "at", m.AccTitle)
	require.Equal(t, "ad", m.AccDescr)
	m, ds = resolve("---\ntitle: Front\n---\nradar-beta\ntitle\naxis A\n")
	require.Empty(t, ds)
	require.Equal(t, "Front", m.Title)
}

func TestConfigKeys(t *testing.T) {
	m, ds := resolve("---\nconfig:\n  radar:\n    width: 400\n    height: 0\n    marginTop: 100\n    curveTension: 0.1\n    axisScaleFactor: 0.5\n---\nradar-beta\naxis A\n")
	require.Empty(t, ds)
	require.Equal(t, []ConfigEntry{{"curveTension", 100}, {"marginTop", 100}, {"width", 400}}, m.Config)
	m, ds = resolve("%%{init: {\"radar\": {\"width\": 500, \"curveTension\": 1, \"marginRight\": 7}}}%%\nradar-beta\naxis A\n")
	require.Empty(t, ds)
	require.Equal(t, []ConfigEntry{{"curveTension", 1000}, {"marginRight", 7}, {"width", 500}}, m.Config)
	m, ds = resolve("---\nconfig:\n  radar:\n    curveTension: 1.5\n    width: -3\n---\nradar-beta\naxis A\n")
	require.Empty(t, ds)
	require.Empty(t, m.Config)
}

func TestThousandths(t *testing.T) {
	for literal, want := range map[string]int64{"0": 0, "7": 7000, "0.5": 500, "1.0005": 1001, "1.0004": 1000, "12.3456": 12346, "0.0005": 1, "100": 100000} {
		require.Equal(t, want, Thousandths(literal), literal)
	}
}
