package layout

import (
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const timelineSample = "timeline\n" +
	"title History\n" +
	"1 : first : second\n" +
	"section Early\n" +
	"2 : third\n" +
	"  : fourth\n" +
	"3\n" +
	"section Late\n" +
	"4 : fifth\n"

func timelineErrors(ds []diag.Diagnostic) []diag.Diagnostic {
	var out []diag.Diagnostic
	for _, d := range ds {
		if d.Severity == diag.SeverityError {
			out = append(out, d)
		}
	}
	return out
}

func timelineInput(t *testing.T, src string, profile scene.Profile) Input {
	t.Helper()
	d := ParseDiagram([]byte(src))
	require.Empty(t, timelineErrors(d.Diagnostics))
	in, err := d.Input(profile, scene.Options{})
	require.NoError(t, err)
	return in
}

func TestTimelineInputEncodesTheModel(t *testing.T) {
	in := timelineInput(t, timelineSample, scene.ProfileVector)
	require.Equal(t, scene.DirectionLR, in.Direction)
	var boxes []string
	for _, b := range in.Boxes {
		boxes = append(boxes, b.ID+"|"+b.Shape+"|"+b.Text)
	}
	require.Equal(t, []string{
		"title|title|History", "s0|section|Early", "s1|section|Late",
		"p0|period|1", "p0.e0|event|first", "p0.e1|event|second",
		"p1|period:0|2", "p1.e0|event|third", "p1.e1|event|fourth",
		"p2|period:0|3", "p3|period:1|4", "p3.e0|event|fifth",
	}, boxes)
	var routes []string
	for _, r := range in.Routes {
		routes = append(routes, r.ID+"|"+r.From+">"+r.To+"|"+r.Line)
	}
	require.Equal(t, []string{
		"e0|p0>p0.e0|dotted", "e1|p0.e0>p0.e1|dotted",
		"e2|p1>p1.e0|dotted", "e3|p1.e0>p1.e1|dotted", "e4|p3>p3.e0|dotted",
	}, routes)
}

func TestTimelineVerticalFansEveryEventFromItsPeriod(t *testing.T) {
	in := timelineInput(t, "timeline TD\np : a : b : c\n", scene.ProfileCell)
	require.Equal(t, scene.DirectionTB, in.Direction)
	var routes []string
	for _, r := range in.Routes {
		routes = append(routes, r.From+">"+r.To)
	}
	require.Equal(t, []string{"p0>p0.e0", "p0>p0.e1", "p0>p0.e2"}, routes)
}

func TestTimelineIdsStayUnique(t *testing.T) {
	in := timelineInput(t, "timeline\ntitle title\nsection s0\np0 : p0.e0 : e0\n", scene.ProfileCell)
	seen := map[string]bool{}
	var ids []string
	for _, b := range in.Boxes {
		require.NotEqual(t, b.Text, b.ID)
		ids = append(ids, b.ID)
	}
	for _, r := range in.Routes {
		ids = append(ids, r.ID)
	}
	for _, id := range ids {
		require.False(t, seen[id], id)
		seen[id] = true
	}
}

func TestTimelineLayoutSatisfiesTheHardConstraints(t *testing.T) {
	for _, src := range []string{
		timelineSample,
		strings.Replace(timelineSample, "timeline\n", "timeline TD\n", 1),
		"timeline\n",
		"timeline\ntitle only\n",
		"timeline\nsection empty\nsection also empty\n",
		"timeline\nsection a very long section name that has to wrap over several lines of the band\n1 : x\n",
		"timeline TD\nsection a very long section name that has to wrap over several lines of the band\n1 : x : y\n",
		"timeline\n2002 : " + strings.Repeat("wide ", 40) + "\n",
		"timeline\n: orphan\n1\n",
	} {
		for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
			d := ParseDiagram([]byte(src))
			in, err := d.Input(profile, scene.Options{})
			require.NoError(t, err, src)
			s, _, err := Layout(in)
			require.NoError(t, err, src)
			clause, failed, err := s.Validate()
			require.NoError(t, err, src)
			require.False(t, failed, "%q %v: %s", src, profile, clause)
		}
	}
}

func TestTimelineCorpusLayoutsAreValid(t *testing.T) {
	paths, err := filepath.Glob(filepath.Join("..", "..", "corpus", "timeline", "*", "*.mmd"))
	require.NoError(t, err)
	require.NotEmpty(t, paths)
	for _, path := range paths {
		src, err := os.ReadFile(path)
		require.NoError(t, err)
		d := ParseDiagram(src)
		if len(timelineErrors(d.Diagnostics)) > 0 {
			continue
		}
		for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
			in, err := d.Input(profile, scene.Options{})
			require.NoError(t, err, path)
			s, _, err := Layout(in)
			require.NoError(t, err, path)
			clause, failed, err := s.Validate()
			require.NoError(t, err, path)
			require.False(t, failed, "%s %v: %s", path, profile, clause)
		}
	}
}

func TestTimelineRejectsMalformedInput(t *testing.T) {
	base := func() Input {
		return Input{Kind: "timeline", Options: scene.DefaultOptions()}
	}
	for name, mutate := range map[string]func(*Input){
		"unknown shape":      func(in *Input) { in.Boxes = []Box{{ID: "x", Shape: "bar", Exclusive: true}} },
		"bad section index":  func(in *Input) { in.Boxes = []Box{{ID: "p", Shape: "period:x", Exclusive: true}} },
		"section out of set": func(in *Input) { in.Boxes = []Box{{ID: "p", Shape: "period:3", Exclusive: true}} },
		"negative section":   func(in *Input) { in.Boxes = []Box{{ID: "p", Shape: "period:-1", Exclusive: true}} },
		"event first":        func(in *Input) { in.Boxes = []Box{{ID: "e", Shape: "event", Exclusive: true}} },
		"unlinked event": func(in *Input) {
			in.Boxes = []Box{{ID: "p", Shape: "period", Exclusive: true}, {ID: "e", Shape: "event", Exclusive: true}}
		},
		"stray route": func(in *Input) {
			in.Boxes = []Box{{ID: "p", Shape: "period", Exclusive: true}}
			in.Routes = []Route{{ID: "r", From: "p", To: "q"}}
		},
	} {
		in := base()
		mutate(&in)
		_, _, err := Layout(in)
		require.ErrorIs(t, err, errTimelineInput, name)
	}
}

func TestTimelineCellSceneDrawsSectionsAndEventsAsRectsAndPeriodsAsRoundRects(t *testing.T) {
	s, _, err := Layout(timelineInput(t, timelineSample, scene.ProfileCell))
	require.NoError(t, err)
	var kinds []string
	for _, group := range s.Groups {
		if group.Role != scene.GroupRoleNode {
			continue
		}
		for _, item := range group.Items {
			switch item.(type) {
			case *scene.Rect:
				kinds = append(kinds, "rect")
			case *scene.RoundRect:
				kinds = append(kinds, "round")
			}
		}
	}
	require.Contains(t, kinds, "rect")
	require.Contains(t, kinds, "round")
}
