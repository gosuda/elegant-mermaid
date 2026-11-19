package timeline

import (
	"strings"
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

func statementSpans(start *Start) []source.Span {
	var out []source.Span
	for _, line := range start.Document.Lines {
		if line.Statement != nil {
			out = append(out, line.Statement.Span)
		}
	}
	return out
}

func statements(start *Start) []string {
	var out []string
	for _, line := range start.Document.Lines {
		if line.Statement == nil {
			continue
		}
		switch node := line.Statement.Kind.(type) {
		case *Title:
			out = append(out, "title="+node.Token.Value)
		case *Section:
			out = append(out, "section="+node.Token.Value)
		case *PeriodStatement:
			out = append(out, "period="+node.Token.Value)
		case *EventStatement:
			out = append(out, "event="+node.Token.Value)
		case *AccTitle:
			out = append(out, "accTitle="+node.Value.Value)
		case *AccDescr:
			out = append(out, "accDescr="+node.Value.Value)
		case *AccDescrBlock:
			out = append(out, "block="+node.Value.Value)
		}
	}
	return out
}

func body(t *testing.T, src string) []string {
	t.Helper()
	start, ds := parse(src)
	require.Empty(t, ds, src)
	return statements(start)
}

func TestHeaderForms(t *testing.T) {
	for _, tc := range []struct {
		src       string
		direction string
		header    string
	}{
		{"timeline\n", "", "timeline"},
		{"timeline LR\n", "LR", "timeline LR"},
		{"timeline TD\n", "TD", "timeline TD"},
		{"TIMELINE \t td\n", "TD", "TIMELINE \t td"},
		{"timeline   lr", "LR", "timeline   lr"},
	} {
		start, ds := parse(tc.src)
		require.Empty(t, ds, tc.src)
		require.Equal(t, tc.direction, start.Header.Direction, tc.src)
		require.Equal(t, tc.header, start.Header.Token.Text, tc.src)
	}
}

func TestDirectionNeedsAWordBoundary(t *testing.T) {
	start, ds := parse("timeline LRx")
	require.Empty(t, ds)
	require.Equal(t, "", start.Header.Direction)
	require.Equal(t, []string{"period=LRx"}, statements(start))
	start, ds = parse("timeline TDé")
	require.Empty(t, ds)
	require.Equal(t, "TD", start.Header.Direction)
	require.Equal(t, []string{"period=é"}, statements(start))
}

func TestHeaderWithoutBoundaryIsRejected(t *testing.T) {
	_, ds := parse("timelinex\n")
	require.Equal(t, []string{"timeline/unexpected-token: unexpected timelinex, expected one of: timeline, timeline_lr, timeline_td"}, messages(ds))
	require.Equal(t, source.Span{Start: 0, End: 9}, ds[0].Span)
	_, ds = parse("")
	require.Equal(t, []string{"timeline/unexpected-token: unexpected end of input, expected one of: timeline, timeline_lr, timeline_td"}, messages(ds))
}

func TestStatementForms(t *testing.T) {
	require.Equal(t, []string{
		"title= History of X",
		"accTitle=A title ",
		"accDescr=A description",
		"block=multi\n   line\n  ",
		"section=Early Era",
		"period=2002 ",
		"event=LinkedIn",
		"event=Second event",
		"period=Plain period",
	}, body(t, "timeline TD\n"+
		"  title  History of X\n"+
		"  accTitle: A title \n"+
		"  accDescr: A description\n"+
		"  accDescr {\n   multi\n   line\n  }\n"+
		"  section Early Era\n"+
		"  2002 : LinkedIn\n"+
		"       : Second event\n"+
		"  Plain period\n"))
}

func TestColonRules(t *testing.T) {
	require.Equal(t, []string{"period=a ", "event=b ", "event=c"}, body(t, "timeline\na : b : c"))
	require.Equal(t, []string{"period=a ", "event=http://x.y/z?q=1"}, body(t, "timeline\na : http://x.y/z?q=1"))
	require.Equal(t, []string{"period=a ", "event=b :c"}, body(t, "timeline\na : b :c"))
	require.Equal(t, []string{"period=a", "event=  x"}, body(t, "timeline\na:\n  x"))
	require.Equal(t, []string{"period=a", "event=;x;"}, body(t, "timeline\na: ;x;"))
}

func TestHashAndCommentRules(t *testing.T) {
	require.Equal(t, []string{"period=a ", "event=#35; b"}, body(t, "timeline\na # comment\n: #35; b"))
	require.Equal(t, []string{"period=a #35; b"}, body(t, "timeline\na #35; b"))
	require.Equal(t, []string{"period=a"}, body(t, "timeline\n# only a comment\na\n%% another\n"))
	require.Equal(t, []string{"period=a b %% c"}, body(t, "timeline\na b %% c"))
}

func TestKeywordsNeedTheirWhitespaceAndPayload(t *testing.T) {
	require.Equal(t, []string{"period=title"}, body(t, "timeline\ntitle"))
	require.Equal(t, []string{"period=title ", "period=x"}, body(t, "timeline\ntitle \n x"))
	require.Equal(t, []string{"period=section"}, body(t, "timeline\nsection"))
	require.Equal(t, []string{"period=titles x"}, body(t, "timeline\ntitles x"))
	require.Equal(t, []string{"section=a ", "event=b"}, body(t, "timeline\nsection a : b"))
	require.Equal(t, []string{"title=  next line"}, body(t, "timeline\ntitle\n  next line"))
}

func TestKeywordsFoldASCIIOnly(t *testing.T) {
	require.Equal(t, []string{"title=x", "section=y", "accTitle=z"}, body(t, "timeline\nTITLE x\nSeCtIoN y\nACCTITLE: z"))
}

func TestAccessibilityBlocks(t *testing.T) {
	src := "timeline\naccDescr {a}\naccDescr {  }\naccDescr{\n}\n"
	start, ds := parse(src)
	require.Empty(t, ds)
	require.Equal(t, []string{"block=a"}, statements(start))
	block := start.Document.Lines[1].Statement
	require.Equal(t, source.Span{Start: 9, End: 21}, block.Span)
	value := block.Kind.(*AccDescrBlock).Value
	require.Equal(t, source.Span{Start: 9, End: 19}, value.Open)
	require.Equal(t, source.Span{Start: 19, End: 20}, value.Payload)
	require.Equal(t, source.Span{Start: 20, End: 21}, value.Close)
}

func TestUnterminatedBlockSpansToTheEnd(t *testing.T) {
	src := "timeline\n2002 : a\naccDescr {\nnever closed\n"
	start, ds := parse(src)
	require.Equal(t, []string{"timeline/unterminated: unterminated {"}, messages(ds))
	require.Equal(t, source.Span{Start: 27, End: len(src)}, ds[0].Span)
	require.Equal(t, []string{"period=2002 ", "event=a"}, statements(start))
}

func TestEmptyAccessibilityValueAtTheEndIsRejected(t *testing.T) {
	for _, src := range []string{"timeline\naccTitle:", "timeline\naccDescr:\n", "timeline\naccTitle:\n  \n"} {
		_, ds := parse(src)
		require.Len(t, ds, 1, src)
		require.Contains(t, ds[0].Message, "unexpected end of input, expected one of: acc_", src)
		require.Equal(t, len(src), ds[0].Span.Start, src)
	}
}

func TestAccessibilityOpenerSwallowsFollowingWhitespace(t *testing.T) {
	require.Equal(t, []string{"accTitle=next"}, body(t, "timeline\naccTitle:\n\n   next\n"))
}

func TestInvalidColonStartsAnUnknownStatementThatEndsWithItsLine(t *testing.T) {
	src := "timeline\n: \nfoo\n#c\n:"
	start, ds := parse(src)
	require.Equal(t, []string{"timeline/unknown-statement: unknown statement :", "timeline/unknown-statement: unknown statement :"}, messages(ds))
	require.Equal(t, source.Span{Start: 9, End: 10}, ds[0].Span)
	require.Equal(t, source.Span{Start: 19, End: 20}, ds[1].Span)
	require.Equal(t, []string{"period=foo"}, statements(start))
}

func TestStrayHeaderTokenSkipsTheRestOfItsLine(t *testing.T) {
	src := "timeline\ntimeline foo : bar\nbaz"
	start, ds := parse(src)
	require.Equal(t, []string{"timeline/unknown-statement: unknown statement timeline"}, messages(ds))
	require.Equal(t, source.Span{Start: 9, End: 27}, ds[0].Span)
	require.Equal(t, []string{"period=baz"}, statements(start))
}

func TestRemovedSpansAreSkippedAndSpansStayInHostCoordinates(t *testing.T) {
	front := "---\na: b\n---\n"
	directive := "%%{init}%%"
	src := front + "timeline\ntitle X " + directive + " Y\n2002 : e\n"
	at := strings.Index(src, directive)
	removed := []source.Span{{Start: 0, End: len(front)}, {Start: at, End: at + len(directive)}}
	start, ds := Parse([]byte(src), removed)
	require.Empty(t, ds)
	require.Equal(t, source.Span{Start: len(front), End: len(front) + len("timeline")}, start.Header.Token.Span)
	title := start.Document.Lines[1].Statement.Kind.(*Title).Token
	require.Equal(t, "X  Y", title.Value)
	require.Equal(t, source.Span{Start: strings.Index(src, "title"), End: at + len(directive) + len(" Y")}, title.Span)
}

func TestLineEndingsNormaliseAndSpansKeepTheHostBytes(t *testing.T) {
	src := "timeline\r\n2002 : a\r\n: b\rc\r\n"
	start, ds := parse(src)
	require.Empty(t, ds)
	require.Equal(t, []string{"period=2002 ", "event=a", "event=b", "period=c"}, statements(start))
	require.Equal(t, []source.Span{{Start: 10, End: 15}, {Start: 15, End: 18}, {Start: 20, End: 23}, {Start: 24, End: 25}}, statementSpans(start))
}

func TestDocumentSpansCoverHeaderThroughLastLine(t *testing.T) {
	src := "timeline\na\n"
	start, _ := parse(src)
	require.Equal(t, source.Span{Start: 0, End: len(src)}, start.Span)
	empty, _ := parse("timeline")
	require.Equal(t, source.Span{Start: 0, End: 8}, empty.Span)
	require.Equal(t, source.Span{Start: 8, End: 8}, empty.Document.Span)
}
