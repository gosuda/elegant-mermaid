package layout

import (
	"bytes"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const journeySample = "journey\n" +
	"title My day\n" +
	"Warm up: 4\n" +
	"section Go to work\n" +
	"  Make tea: 5: Me\n" +
	"  Do work: 1: Me, Cat, \n" +
	"section Go home\n" +
	"  Sit down: 3: Me\n"

func journeyErrors(ds []diag.Diagnostic) []diag.Diagnostic {
	var out []diag.Diagnostic
	for _, d := range ds {
		if d.Severity == diag.SeverityError {
			out = append(out, d)
		}
	}
	return out
}

func journeyLayoutInput(t *testing.T, src string, profile scene.Profile) Input {
	t.Helper()
	d := ParseDiagram([]byte(src))
	require.Empty(t, journeyErrors(d.Diagnostics), src)
	in, err := d.Input(profile, scene.Options{})
	require.NoError(t, err)
	return in
}

func journeyBoxRows(in Input) []string {
	var rows []string
	for _, b := range in.Boxes {
		rows = append(rows, strings.Join([]string{b.ID, b.Shape, b.Parent, b.Text}, "|"))
	}
	return rows
}

func TestJourneyInputEncodesTitleBandsTasksAndPeople(t *testing.T) {
	in := journeyLayoutInput(t, journeySample, scene.ProfileVector)
	require.Equal(t, scene.DirectionTB, in.Direction)
	require.Equal(t, []string{
		"title|title||My day",
		"s0|section||Go to work",
		"s1|section||Go home",
		"t0|task:4||Warm up",
		"t1|task:5|s0|Make tea",
		"t1.people|people|t1|Me",
		"t2|task:1|s0|Do work",
		"t2.people|people|t2|Me, Cat",
		"t3|task:3|s1|Sit down",
		"t3.people|people|t3|Me",
	}, journeyBoxRows(in))
	require.Equal(t, scene.RoleGroup, in.Boxes[1].Role)
	require.True(t, in.Boxes[3].Exclusive)
	require.False(t, in.Boxes[5].Exclusive)
}

func TestJourneyConsecutiveSectionsWithOneNameShareABand(t *testing.T) {
	src := "journey\nsection A\nt1: 3\nsection A\nt2: 3\nsection B\nt3: 3\nsection A\nt4: 3\nsection Empty\n"
	in := journeyLayoutInput(t, src, scene.ProfileCell)
	var bands []string
	for _, b := range in.Boxes {
		if b.Role == scene.RoleGroup {
			bands = append(bands, b.ID+"="+b.Text)
		}
	}
	require.Equal(t, []string{"s0=A", "s1=B", "s2=A"}, bands)
	require.Equal(t, "s0", in.Boxes[3].Parent)
	require.Equal(t, "s0", in.Boxes[4].Parent)
	require.Equal(t, "s2", in.Boxes[6].Parent)
}

func TestJourneyLayoutSatisfiesTheHardConstraints(t *testing.T) {
	for _, src := range []string{
		journeySample,
		"journey\n",
		"journey\ntitle only\n",
		"journey\nA: 3\n",
		"journey\nsection S\nA very long task name that must wrap onto several lines to fit its card: 5: A rather long actor name, another long actor name\n",
		"journey\nsection  \nA: 3\n",
	} {
		for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
			s, _, err := Layout(journeyLayoutInput(t, src, profile))
			require.NoError(t, err, src)
			clause, failed, err := s.Validate()
			require.NoError(t, err, src)
			require.False(t, failed, "%q %v: %s", src, profile, clause)
		}
	}
}

func TestJourneyLongTextWrapsInsideTheCard(t *testing.T) {
	src := "journey\nsection S\nA very long task name that must wrap onto several lines: 5: Me\nShort: 3\n"
	short, _, err := Layout(journeyLayoutInput(t, "journey\nsection S\nShort: 3\n", scene.ProfileCell))
	require.NoError(t, err)
	long, _, err := Layout(journeyLayoutInput(t, src, scene.ProfileCell))
	require.NoError(t, err)
	var card, other int32
	for _, b := range long.Boxes {
		switch b.ID {
		case "t0":
			card = b.Rect.H
		case "t1":
			other = b.Rect.H
		}
	}
	require.Greater(t, card, short.Boxes[1].Rect.H)
	require.Equal(t, card, other)
}

func TestJourneyConfigOverridesApplyToTheVectorProfileOnly(t *testing.T) {
	src := "%%{init: {\"journey\": {\"width\": 300, \"height\": 80, \"diagramMarginX\": 20}}}%%\njourney\nsection S\nA: 3\nB: 4\n"
	vector, _, err := Layout(journeyLayoutInput(t, src, scene.ProfileVector))
	require.NoError(t, err)
	task := func(s scene.Scene, id string) scene.Box {
		for _, b := range s.Boxes {
			if b.ID == id {
				return b
			}
		}
		t.Fatalf("no box %s", id)
		return scene.Box{}
	}
	require.Equal(t, int32(300*64), task(vector, "t0").Rect.W)
	require.Equal(t, int32(80*64), task(vector, "t0").Rect.H)
	require.Equal(t, int32((300+20)*64), task(vector, "t1").Rect.X-task(vector, "t0").Rect.X)
	cell, _, err := Layout(journeyLayoutInput(t, src, scene.ProfileCell))
	require.NoError(t, err)
	require.Equal(t, int32(18), task(cell, "t0").Rect.W)
	var keys []string
	for _, c := range vector.Options.Config {
		keys = append(keys, c.Key)
	}
	require.Equal(t, []string{"diagramMarginX", "height", "width"}, keys)
}

func TestJourneyModelDumpCarriesShapesAndText(t *testing.T) {
	var out bytes.Buffer
	require.NoError(t, WriteModelDump(&out, journeyLayoutInput(t, journeySample, scene.ProfileCell)))
	dump := out.String()
	require.Contains(t, dump, `"shape":"task:5"`)
	require.Contains(t, dump, `"text":"Me, Cat"`)
	require.Contains(t, dump, `"kind":"journey"`)
	require.NotContains(t, dump, `"canvas"`)
}

func TestJourneyRejectsInvalidScoresBeforeLayout(t *testing.T) {
	d := ParseDiagram([]byte("journey\nA: 9\n"))
	require.Len(t, journeyErrors(d.Diagnostics), 1)
	require.Equal(t, "journey/score-out-of-range", journeyErrors(d.Diagnostics)[0].Code)
	_, err := d.Input(scene.ProfileVector, scene.Options{})
	require.NoError(t, err, "the document-level error is reported by the caller, not by Input")
}

func TestJourneyCorpusLayoutsAreValidAndDeterministic(t *testing.T) {
	paths, err := filepath.Glob(filepath.Join("..", "..", "corpus", "journey", "*", "*.mmd"))
	require.NoError(t, err)
	require.NotEmpty(t, paths)
	for _, path := range paths {
		src, err := os.ReadFile(path)
		require.NoError(t, err)
		d := ParseDiagram(src)
		if len(journeyErrors(d.Diagnostics)) > 0 {
			continue
		}
		for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
			in, err := d.Input(profile, scene.Options{})
			require.NoError(t, err, path)
			first, _, err := Layout(in)
			require.NoError(t, err, path)
			second, _, err := Layout(in)
			require.NoError(t, err, path)
			require.Equal(t, first.AppendJSON(nil), second.AppendJSON(nil), path)
			clause, failed, err := first.Validate()
			require.NoError(t, err, path)
			require.False(t, failed, "%s %v: %s", path, profile, clause)
		}
	}
}
