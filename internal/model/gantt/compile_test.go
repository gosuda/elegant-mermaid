package gantt

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/civil"
	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/gantt"
)

func resolveSource(src string) (*Model, []diag.Diagnostic) {
	start, parsed := syn.Parse([]byte(src), syntax.Preprocess([]byte(src)).Removed)
	m, resolved := Resolve([]byte(src), start)
	return m, append(parsed, resolved...)
}

func codes(ds []diag.Diagnostic) []string {
	out := make([]string, len(ds))
	for i, d := range ds {
		out[i] = d.Code + ": " + d.Message
	}
	return out
}

func day(y, m, d int64) int64 { return civil.Join(y, m, d, 0, 0, 0) }

func TestChainedTasks(t *testing.T) {
	m, ds := resolveSource("gantt\ndateFormat YYYY-MM-DD\nsection A\nOne :a1, 2014-01-01, 30d\nTwo :after a1, 20d\nThree :2014-03-01, 2014-03-05\nFour :a4, 2014-02-01, until a1\n")
	require.Empty(t, ds)
	require.Len(t, m.Tasks, 4)
	require.Equal(t, day(2014, 1, 1), m.Tasks[0].StartSeconds)
	require.Equal(t, day(2014, 1, 31), m.Tasks[0].EndSeconds)
	require.Equal(t, day(2014, 1, 31), m.Tasks[1].StartSeconds)
	require.Equal(t, day(2014, 2, 20), m.Tasks[1].EndSeconds)
	require.Equal(t, day(2014, 3, 5), m.Tasks[2].EndSeconds)
	require.True(t, m.Tasks[2].ManualEnd)
	require.Equal(t, "task1", m.Tasks[1].ID)
	require.Equal(t, []Row{{RowSection, 0}, {RowTask, 0}, {RowTask, 1}, {RowTask, 2}, {RowTask, 3}}, m.Rows)
}

func TestImplicitPredecessorAndInclusiveEnd(t *testing.T) {
	m, ds := resolveSource("gantt\ndateFormat YYYY-MM-DD\ninclusiveEndDates\nOne :a, 2014-01-01, 2014-01-03\nTwo :4d\n")
	require.Empty(t, ds)
	require.Equal(t, day(2014, 1, 4), m.Tasks[0].EndSeconds)
	require.Equal(t, day(2014, 1, 4), m.Tasks[1].StartSeconds)
	require.Equal(t, day(2014, 1, 8), m.Tasks[1].EndSeconds)
}

func TestWeekendExclusionExtendsEnd(t *testing.T) {
	m, ds := resolveSource("gantt\ndateFormat YYYY-MM-DD\nexcludes weekends\nOne :a, 2014-01-03, 3d\n")
	require.Empty(t, ds)
	require.Equal(t, day(2014, 1, 8), m.Tasks[0].EndSeconds)
	require.True(t, m.Tasks[0].HasRenderEnd)
	require.Equal(t, day(2014, 1, 8), m.Tasks[0].RenderEnd)
}

func TestExclusionLimit(t *testing.T) {
	_, ds := resolveSource("gantt\ndateFormat YYYY-MM-DD\nexcludes monday tuesday wednesday thursday friday saturday sunday\nOne :a, 2014-01-03, 3d\n")
	require.Equal(t, []string{"gantt/exclusion-limit: cannot find a non-excluded end within 10000 days"}, codes(ds))
}

func TestDurationUnits(t *testing.T) {
	cases := map[string]int64{
		"90s":    90,
		"2m":     120,
		"1.5h":   5400,
		"1500ms": 1,
		"2w":     14 * 86400,
		"1.5d":   2 * 86400,
		"0.4d":   0,
		"1M":     31 * 86400,
		"1y":     365 * 86400,
	}
	for text, want := range cases {
		m, ds := resolveSource("gantt\ndateFormat YYYY-MM-DD\nOne :a, 2014-01-01, " + text + "\n")
		require.Empty(t, ds, text)
		require.Equal(t, day(2014, 1, 1)+want, m.Tasks[0].EndSeconds, text)
	}
	m, _ := resolveSource("gantt\ndateFormat YYYY-MM-DD\nOne :a, 2014-01-31, 1M\n")
	require.Equal(t, day(2014, 2, 28), m.Tasks[0].EndSeconds)
	m, _ = resolveSource("gantt\ndateFormat YYYY-MM-DD\nOne :a, 2012-02-29, 1y\n")
	require.Equal(t, day(2013, 2, 28), m.Tasks[0].EndSeconds)
}

func TestInvalidEndKeepsStart(t *testing.T) {
	m, ds := resolveSource("gantt\ndateFormat YYYY-MM-DD\nOne :a, 2014-01-01, soon\n")
	require.Equal(t, []string{"gantt/invalid-end: soon is neither a date nor a duration; task has zero duration"}, codes(ds))
	require.Equal(t, diag.SeverityWarning, ds[0].Severity)
	require.Equal(t, m.Tasks[0].StartSeconds, m.Tasks[0].EndSeconds)
}

func TestReferenceWarningsAndEpochFallback(t *testing.T) {
	m, ds := resolveSource("gantt\ndateFormat YYYY-MM-DD\nOne :a, after nope other, 2d\nTwo :b, 2014-01-01, until missing\n")
	require.Equal(t, []string{
		"gantt/unknown-task-reference: after references unknown task id nope",
		"gantt/unknown-task-reference: after references unknown task id other",
		"gantt/unknown-task-reference: until references unknown task id missing",
	}, codes(ds))
	require.Equal(t, int64(0), m.Tasks[0].StartSeconds)
	require.Equal(t, int64(2*86400), m.Tasks[0].EndSeconds)
	require.Equal(t, int64(0), m.Tasks[1].EndSeconds)
}

func TestErrors(t *testing.T) {
	cases := map[string]string{
		"gantt\nOne :3d\n": "gantt/predecessor-missing: task has no preceding task",
		"gantt\ndateFormat YYYY-MM-DD\nOne :a, 2014-13-01, 3d\n": "gantt/invalid-date: invalid date 2014-13-01",
		"gantt\nOne :crit\n":                                "gantt/task-data-invalid: task requires one, two, or three data fields after tags",
		"gantt\nOne :a, 2014-01-01, 3d, 4d\n":               "gantt/task-data-invalid: task requires one, two, or three data fields after tags",
		"gantt\nOne :a, after b, 1d\nTwo :b, after a, 1d\n": "gantt/unresolved-task: task dates remain unresolved after eleven passes",
	}
	for src, want := range cases {
		_, ds := resolveSource(src)
		require.NotEmpty(t, ds, src)
		require.Equal(t, want, codes(ds)[0], src)
	}
}

func TestTagsAndDataArity(t *testing.T) {
	m, ds := resolveSource("gantt\ndateFormat YYYY-MM-DD\nOne :done, crit, id1, 2014-01-01, 1d\nTwo :milestone, 2014-01-03, 0d\nThree :vert, v1, 2014-01-02, 0d\n")
	require.Empty(t, ds)
	require.True(t, m.Tasks[0].Done && m.Tasks[0].Crit && !m.Tasks[0].Active)
	require.Equal(t, "id1", m.Tasks[0].ID)
	require.True(t, m.Tasks[1].Milestone)
	require.True(t, m.Tasks[2].Vert)
	require.Equal(t, []int{0, 1, -1}, []int{m.Tasks[0].Order, m.Tasks[1].Order, m.Tasks[2].Order})
}

func TestTimestampFormats(t *testing.T) {
	m, ds := resolveSource("gantt\ndateFormat X\nOne :a, 1700000000, 1700003600\n")
	require.Empty(t, ds)
	require.Equal(t, int64(1700000), m.Tasks[0].StartSeconds)
	require.Equal(t, int64(1700003600), m.Tasks[0].EndSeconds)
	m, ds = resolveSource("gantt\ndateFormat x\nOne :a, 1700000000123, 1700000003123\n")
	require.Empty(t, ds)
	require.Equal(t, int64(1700000000), m.Tasks[0].StartSeconds)
	require.Equal(t, int64(1700000003), m.Tasks[0].EndSeconds)
}

func TestFallbackDatesWithoutDateFormat(t *testing.T) {
	m, ds := resolveSource("gantt\nOne :a, 2014-01-01, 2d\n")
	require.Empty(t, ds)
	require.Equal(t, day(2014, 1, 1), m.Tasks[0].StartSeconds)
}

func TestAxisAndTickDirectives(t *testing.T) {
	_, ds := resolveSource("gantt\naxisFormat %L\ntickInterval 5millisecond\nodd :a, 2014-01-01, 1d\n")
	require.Equal(t, []string{
		"gantt/axis-format-unsupported: axis format contains unsupported code %L; using %Y-%m-%d",
		"gantt/tick-interval-unsupported: millisecond tick interval is not supported; using automatic ticks",
	}, codes(ds)[:2])
	_, ds = resolveSource("gantt\ntodayMarker off\n")
	require.Equal(t, []string{"gantt/today-marker-ignored: today marker is ignored"}, codes(ds))
	require.Equal(t, diag.SeverityInfo, ds[0].Severity)
}

func TestClickLinksAndCallbacks(t *testing.T) {
	m, ds := resolveSource("gantt\ndateFormat YYYY-MM-DD\nOne :a1, 2014-01-01, 1d\nclick a1 href \"https://example.com\" call run(\"x, y\", 2)\nclick a1 href \"javascript:alert(1)\"\nclick nope href \"https://other\"\n")
	require.Equal(t, []string{
		"interaction/callback-ignored: callback run is ignored",
		"interaction/unsafe-url: link URL is not allowed",
	}, codes(ds))
	require.True(t, m.Tasks[0].HasLink)
	require.Equal(t, "https://example.com", m.Tasks[0].Link)
	require.Equal(t, []string{"x, y", "2"}, m.Clicks[0].Callback.Args)
}

func TestConfigAndFrontmatter(t *testing.T) {
	m, ds := resolveSource("---\ntitle: \"Plan #35;\"\nconfig:\n  gantt:\n    barHeight: 30\n    topAxis: true\n    weekday: monday\n    axisFormat: \"%d\"\n---\ngantt\n")
	require.Empty(t, ds)
	require.Equal(t, "Plan #", m.TitleLabel)
	n, ok := m.ConfigInteger("barHeight")
	require.True(t, ok)
	require.Equal(t, int64(30), n)
	require.True(t, m.ConfigBool("topAxis"))
	s, _ := m.ConfigString("weekday")
	require.Equal(t, "monday", s)
}

func TestSplitCallbackArgs(t *testing.T) {
	require.Equal(t, []string{"a", "b, c", ""}, splitCallbackArgs(`a, "b, c", ""`))
}
