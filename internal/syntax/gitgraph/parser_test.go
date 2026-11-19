package gitgraph

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

func parse(src string) (*Start, []diag.Diagnostic) {
	return Parse([]byte(src), nil)
}

func messages(ds []diag.Diagnostic) []string {
	out := make([]string, len(ds))
	for i, d := range ds {
		out[i] = d.Code + ": " + d.Message
	}
	return out
}

func TestHeaderForms(t *testing.T) {
	for _, tc := range []struct {
		src       string
		header    string
		direction string
	}{
		{"gitGraph\ncommit", "gitGraph", ""},
		{"gitGraph:\ncommit", "gitGraph:", ""},
		{"gitGraph :\ncommit", "gitGraph", ""},
		{"gitGraph LR:\ncommit", "gitGraph", "LR"},
		{"gitGraph TB:\ncommit", "gitGraph", "TB"},
		{"gitGraph  BT :\ncommit", "gitGraph", "BT"},
	} {
		start, ds := parse(tc.src)
		require.Empty(t, ds, tc.src)
		require.Equal(t, tc.header, start.Header.Kind, tc.src)
		require.Len(t, start.Statements, 1, tc.src)
		if tc.direction == "" {
			require.Nil(t, start.Direction, tc.src)
			continue
		}
		require.Equal(t, tc.direction, start.Direction.Kind, tc.src)
	}
}

func TestDirectionWithoutColonIsRejected(t *testing.T) {
	_, ds := parse("gitGraph LR\ncommit")
	require.Equal(t, []string{"gitgraph/unexpected-token: unexpected \n, expected one of: :"}, messages(ds))
	require.Equal(t, source.Span{Start: 11, End: 12}, ds[0].Span)
}

func TestStatementForms(t *testing.T) {
	start, ds := parse("gitGraph\n" +
		"commit id: \"a\" \"bare\" tag: \"t1\" tag: 't2' type: REVERSE\n" +
		"commit msg: \"m\"\n" +
		"branch feature/x-1.0 order: 3\n" +
		"checkout \"quoted name\"\n" +
		"switch main\n" +
		"merge dev id: \"m\" tag: \"v\" type: HIGHLIGHT\n" +
		"cherry-pick id: \"a\" parent: \"p\" tag: \"c\"\n")
	require.Empty(t, ds)
	require.Len(t, start.Statements, 7)
	commit := start.Statements[0].Kind.(*Commit)
	require.Equal(t, "a", commit.ID.Text)
	require.Equal(t, "bare", commit.Message.Text)
	require.Equal(t, []string{"t1", "t2"}, []string{commit.Tags[0].Text, commit.Tags[1].Text})
	require.Equal(t, "REVERSE", commit.Type.Text)
	require.Equal(t, "m", start.Statements[1].Kind.(*Commit).Message.Text)
	branch := start.Statements[2].Kind.(*Branch)
	require.Equal(t, "feature/x-1.0", branch.Name.Text)
	require.Equal(t, int64(3), branch.Order.Value)
	require.Equal(t, "quoted name", start.Statements[3].Kind.(*Checkout).Branch.Text)
	require.True(t, start.Statements[4].Kind.(*Checkout).Switch)
	merge := start.Statements[5].Kind.(*Merge)
	require.Equal(t, []string{"dev", "m", "HIGHLIGHT"}, []string{merge.Branch.Text, merge.ID.Text, merge.Type.Text})
	pick := start.Statements[6].Kind.(*CherryPicking)
	require.Equal(t, []string{"a", "p", "c"}, []string{pick.ID.Text, pick.Parent.Text, pick.Tags[0].Text})
}

func TestStatementSpansExcludeTrailingTrivia(t *testing.T) {
	src := "gitGraph\ncommit id: \"a\"   %% note\nbranch x\n"
	start, ds := parse(src)
	require.Empty(t, ds)
	require.Equal(t, source.Span{Start: 9, End: 23}, start.Statements[0].Span)
	require.Equal(t, source.Span{Start: 34, End: 42}, start.Statements[1].Span)
}

func TestRepeatedScalarsKeepTheLastValue(t *testing.T) {
	start, ds := parse("gitGraph\ncommit id: \"a\" id: \"b\" type: NORMAL type: HIGHLIGHT\n")
	require.Empty(t, ds)
	commit := start.Statements[0].Kind.(*Commit)
	require.Equal(t, "b", commit.ID.Text)
	require.Equal(t, "HIGHLIGHT", commit.Type.Text)
}

func TestKeywordsNeedBoundaries(t *testing.T) {
	_, ds := parse("gitGraph\ncommitted\ncommit-1 id: \"x\"\nbranch commit\n")
	require.Equal(t, []string{
		"gitgraph/unknown-statement: unknown statement committed",
		"gitgraph/unknown-statement: unknown statement commit-1",
		"gitgraph/unexpected-token: unexpected commit, expected one of: REFERENCE, STRING",
	}, messages(ds))
	_, ds = parse("gitGraph\nbranch \"commit\"\nbranch cherry-pick-2\n")
	require.Empty(t, ds)
}

func TestIntegerTokenFollowsTheAuthorityPattern(t *testing.T) {
	for src, want := range map[string]int{"0": 1, "7": 1, "42": 2, "1.5": 0, "12.5": 1, "007": 1, "x": 0} {
		require.Equal(t, want, integerLength(src), src)
	}
	_, ds := parse("gitGraph\nbranch a order: 1.5\n")
	require.Equal(t, []string{"gitgraph/unexpected-token: unexpected 1.5, expected one of: INT"}, messages(ds))
	_, ds = parse("gitGraph\nbranch 123\n")
	require.Equal(t, []string{"gitgraph/unexpected-token: unexpected 123, expected one of: REFERENCE, STRING"}, messages(ds))
}

func TestStringEscapes(t *testing.T) {
	start, ds := parse("gitGraph\ncommit id: \"a\\\"b\\nc\\\\d\\q\"\n")
	require.Empty(t, ds)
	require.Equal(t, "a\"b\nc\\dq", start.Statements[0].Kind.(*Commit).ID.Text)
}

func TestRecoveryContinuesAfterARejectedStatement(t *testing.T) {
	start, ds := parse("gitGraph\ncommit id: foo\ncommit id: \"a\" extra\ncommit\n")
	require.Equal(t, []string{
		"gitgraph/unexpected-token: unexpected foo, expected one of: STRING",
		"gitgraph/unexpected-token: unexpected extra, expected one of: EOF, NEWLINE, STRING, id:, msg:, tag:, type:",
	}, messages(ds))
	require.Len(t, start.Statements, 1)
}

func TestUnknownStatementSpansTheLine(t *testing.T) {
	src := "gitGraph\nfoo bar \"baz\"\ncommit\n"
	start, ds := parse(src)
	require.Equal(t, []string{"gitgraph/unknown-statement: unknown statement foo"}, messages(ds))
	require.Equal(t, source.Span{Start: 9, End: 22}, ds[0].Span)
	require.Len(t, start.Statements, 1)
}

func TestUnterminatedProducesOnlyTheOpenerDiagnostic(t *testing.T) {
	for src, opener := range map[string]source.Span{
		"gitGraph\ncommit id: \"abc":         {Start: 20, End: 24},
		"gitGraph\ncommit msg: 'abc\ncommit": {Start: 21, End: 32},
		"gitGraph\naccDescr {\nnever":        {Start: 18, End: 25},
	} {
		_, ds := parse(src)
		require.Len(t, ds, 1, src)
		require.Equal(t, "gitgraph/unterminated", ds[0].Code, src)
		require.Equal(t, opener, ds[0].Span, src)
	}
}

func TestMetadataValues(t *testing.T) {
	src := "gitGraph\ntitle   My   diagram \naccTitle:  T\t\t t \naccDescr: d %% c\naccDescr {\n  one   two\n\n  three  \n}\ntitle\n"
	start, ds := parse(src)
	require.Empty(t, ds)
	var got []string
	for _, statement := range start.Statements {
		meta := statement.Kind.(*Metadata)
		got = append(got, meta.Field+"="+meta.Value)
	}
	require.Equal(t, []string{"title=My diagram", "accTitle=T t", "accDescr=d", "accDescr=one two\nthree", "title="}, got)
}

func TestCommentsAndLineEndings(t *testing.T) {
	start, ds := parse("gitGraph\r\n%% only a comment\r\ncommit %% trailing\r\n\r\ncommit\rbranch x\n")
	require.Empty(t, ds)
	require.Len(t, start.Statements, 3)
}

func TestRemovedSpansAreSkipped(t *testing.T) {
	src := "---\ntitle: x\n---\ngitGraph\ncommit\n"
	start, ds := Parse([]byte(src), []source.Span{{Start: 0, End: 17}})
	require.Empty(t, ds)
	require.Equal(t, "gitGraph", start.Header.Kind)
	require.Len(t, start.Statements, 1)
}
