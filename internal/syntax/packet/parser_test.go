package packet

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
	for _, tc := range []struct{ src, header string }{
		{"packet\n0: \"a\"", "packet"},
		{"packet-beta\n0: \"a\"", "packet-beta"},
		{"\n\npacket %% comment\n0: \"a\"", "packet"},
		{"packet 0: \"a\"", "packet"},
	} {
		start, ds := parse(tc.src)
		require.Empty(t, ds, tc.src)
		require.Equal(t, tc.header, start.Header.Kind, tc.src)
		require.Len(t, start.Statements, 1, tc.src)
	}
}

func TestBlockForms(t *testing.T) {
	start, ds := parse("packet\n0-15: \"range\"\n16: 'single'\n+8: \"relative\"\n 24 - 31 : \"spaced\"\n")
	require.Empty(t, ds)
	require.Len(t, start.Statements, 4)
	first := start.Statements[0].Kind.(*PacketBlock)
	require.Equal(t, int64(0), first.Start.Value)
	require.Equal(t, int64(15), first.End.Value)
	require.Nil(t, first.Bits)
	require.Equal(t, "range", first.Label.Text)
	require.Equal(t, source.Span{Start: 7, End: 20}, start.Statements[0].Span)
	single := start.Statements[1].Kind.(*PacketBlock)
	require.Equal(t, int64(16), single.Start.Value)
	require.Nil(t, single.End)
	relative := start.Statements[2].Kind.(*PacketBlock)
	require.Nil(t, relative.Start)
	require.Equal(t, int64(8), relative.Bits.Value)
	require.Equal(t, source.Span{Start: 34, End: 48}, start.Statements[2].Span)
	spaced := start.Statements[3].Kind.(*PacketBlock)
	require.Equal(t, int64(24), spaced.Start.Value)
	require.Equal(t, int64(31), spaced.End.Value)
}

func TestMetadataStatements(t *testing.T) {
	start, ds := parse("packet\ntitle  Hi   there %% c\naccTitle: T  U\naccDescr: d\naccDescr {\n a  b\n\n c\n}\n  title x\ntitle\n0: \"x\"")
	require.Empty(t, ds)
	var got []Metadata
	for _, s := range start.Statements {
		if m, ok := s.Kind.(*Metadata); ok {
			got = append(got, *m)
		}
	}
	require.Equal(t, []Metadata{
		{"title", "Hi there"}, {"accTitle", "T U"}, {"accDescr", "d"}, {"accDescr", "a b\nc"}, {"title", "x"}, {"title", ""},
	}, got)
}

func TestStringConversion(t *testing.T) {
	start, ds := parse("packet\n0-3: \"a\\nb\\qc\\\\d\\0e\\\"f\"\n4: 'it\\'s'\n5: \"x\ny\"")
	require.Empty(t, ds)
	require.Equal(t, "a\nbqc\\d\x00e\"f", start.Statements[0].Kind.(*PacketBlock).Label.Text)
	require.Equal(t, "it's", start.Statements[1].Kind.(*PacketBlock).Label.Text)
	require.Equal(t, "x\ny", start.Statements[2].Kind.(*PacketBlock).Label.Text)
}

func TestIntegerRules(t *testing.T) {
	_, ds := parse("packet\n01-3: \"a\"")
	require.Equal(t, []string{"packet/unexpected-token: unexpected 1, expected one of: -, :"}, messages(ds))
	_, ds = parse("packet\n0.5: \"a\"")
	require.Equal(t, []string{"packet/unexpected-token: unexpected ., expected one of: -, :"}, messages(ds))
	start, ds := parse("packet\n99999999999999999999: \"a\"")
	require.Empty(t, ds)
	require.Equal(t, int64(2147483647), start.Statements[0].Kind.(*PacketBlock).Start.Value)
}

func TestUnexpectedTokens(t *testing.T) {
	for _, tc := range []struct{ src, want string }{
		{"packet\n0-3 \"x\"", "packet/unexpected-token: unexpected \"x\", expected one of: :"},
		{"packet\n0 \"x\"", "packet/unexpected-token: unexpected \"x\", expected one of: -, :"},
		{"packet\n0-: \"x\"", "packet/unexpected-token: unexpected :, expected one of: INT"},
		{"packet\n+: \"x\"", "packet/unexpected-token: unexpected :, expected one of: INT"},
		{"packet\n0-3: 4", "packet/unexpected-token: unexpected 4, expected one of: STRING"},
		{"packet\n0-3: \"a\" 4-7: \"b\"", "packet/unexpected-token: unexpected 4, expected one of: EOF, NEWLINE"},
		{"packet\n0-3: \"a\"title", "packet/unexpected-token: unexpected title, expected one of: EOF, NEWLINE"},
		{"packet\ntitle x 0: \"a\"\n", ""},
	} {
		start, ds := parse(tc.src)
		if tc.want == "" {
			require.Empty(t, ds, tc.src)
			require.Empty(t, start.Statements[1:], tc.src)
			continue
		}
		require.Equal(t, []string{tc.want}, messages(ds), tc.src)
	}
}

func TestUnknownStatements(t *testing.T) {
	start, ds := parse("packet\nfoo bar\n-3: \"x\"\n0: \"ok\"")
	require.Equal(t, []string{
		"packet/unknown-statement: unknown statement f",
		"packet/unknown-statement: unknown statement -",
	}, messages(ds))
	require.Equal(t, source.Span{Start: 7, End: 14}, ds[0].Span)
	require.Equal(t, source.Span{Start: 15, End: 22}, ds[1].Span)
	require.Len(t, start.Statements, 1)
}

func TestUnterminated(t *testing.T) {
	for _, tc := range []struct {
		src  string
		span source.Span
		text string
	}{
		{"packet\n0: \"never", source.Span{Start: 10, End: 16}, "unterminated \""},
		{"packet\n0: 'never\n1: 'x'", source.Span{Start: 22, End: 23}, "unterminated '"},
		{"packet\naccDescr {\n a", source.Span{Start: 16, End: 20}, "unterminated {"},
		{"packet\n0-3: \"a\\", source.Span{Start: 12, End: 15}, "unterminated \""},
	} {
		_, ds := parse(tc.src)
		require.NotEmpty(t, ds, tc.src)
		last := ds[len(ds)-1]
		require.Equal(t, "packet/unterminated", last.Code, tc.src)
		require.Equal(t, tc.span, last.Span, tc.src)
		require.Equal(t, tc.text, last.Message, tc.src)
	}
}

func TestBackslashBeforeLineEndIsNotAString(t *testing.T) {
	_, ds := parse("packet\n0-3: \"a\\\nb\"")
	require.NotEmpty(t, ds)
	require.Equal(t, "packet/unexpected-token", ds[0].Code)
}

func TestRemovedSpansAreSkipped(t *testing.T) {
	src := "---\ntitle: x\n---\npacket\n0: \"a\""
	start, ds := Parse([]byte(src), []source.Span{{Start: 0, End: 17}})
	require.Empty(t, ds)
	require.Len(t, start.Statements, 1)
}

func TestLoneCarriageReturnEndsLines(t *testing.T) {
	start, ds := parse("packet\r0: \"a\"\r\n1: \"b\"")
	require.Empty(t, ds)
	require.Len(t, start.Statements, 2)
}
