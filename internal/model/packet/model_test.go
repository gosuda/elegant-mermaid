package packet

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/packet"
)

func resolve(src string) (*Model, []diag.Diagnostic) {
	pre := syntax.Preprocess([]byte(src))
	document, _ := syn.Parse([]byte(src), pre.Removed)
	return Resolve([]byte(src), document)
}

func messages(ds []diag.Diagnostic) []string {
	out := make([]string, len(ds))
	for i, d := range ds {
		out[i] = d.Code + ": " + d.Message
	}
	return out
}

func spans(m *Model) [][3]int64 {
	out := make([][3]int64, len(m.Pieces))
	for i, p := range m.Pieces {
		out[i] = [3]int64{int64(p.Row), p.Start, p.End}
	}
	return out
}

func TestDefaultBitsPerRowMatchesTheConstant(t *testing.T) {
	var found int
	for _, c := range gen.LayoutConst {
		if c.Name == "vector.packet.bits_per_row" || c.Name == "cell.packet.bits_per_row" {
			require.Equal(t, int32(DefaultBitsPerRow), c.Value, c.Name)
			found++
		}
	}
	require.Equal(t, 2, found)
}

func TestFieldForms(t *testing.T) {
	m, ds := resolve("packet\n0-3: \"a\"\n4: \"b\"\n+4: \"c\"\n9-15: \"d\"\n")
	require.Empty(t, ds)
	require.Len(t, m.Fields, 4)
	want := []struct{ start, end, bits int64 }{{0, 3, 4}, {4, 4, 1}, {5, 8, 4}, {9, 15, 7}}
	for i, w := range want {
		f := m.Fields[i]
		require.Equal(t, i, f.Index)
		require.Equal(t, w.start, f.Start, i)
		require.Equal(t, w.end, f.End, i)
		require.Equal(t, w.bits, f.Bits, i)
	}
	require.True(t, m.Fields[0].HasStart && m.Fields[0].HasEnd && !m.Fields[0].HasBits)
	require.True(t, !m.Fields[2].HasStart && m.Fields[2].HasBits)
	require.Equal(t, "c", m.Fields[2].Label)
	require.Equal(t, source.Span{Start: 23, End: 30}, m.Fields[2].Span)
	require.Equal(t, source.Span{Start: 24, End: 25}, m.Fields[2].BitsSpan)
}

func TestEqualEndpointsAreAccepted(t *testing.T) {
	m, ds := resolve("packet\n0-0: \"a\"\n1-1: \"b\"")
	require.Empty(t, ds)
	require.Equal(t, int64(1), m.Fields[0].Bits)
}

func TestRejections(t *testing.T) {
	for _, tc := range []struct {
		src  string
		want string
		span source.Span
	}{
		{"packet\n0-3: \"a\"\n8-4: \"b\"", "packet/range-reversed: Packet block 8 - 4 is invalid. End must be greater than start.", source.Span{Start: 16, End: 19}},
		{"packet\n0-3: \"a\"\n5-6: \"b\"", "packet/non-contiguous: Packet block 5 - 6 is not contiguous. It should start from 4.", source.Span{Start: 16, End: 17}},
		{"packet\n0-3: \"a\"\n5: \"b\"", "packet/non-contiguous: Packet block 5 - 5 is not contiguous. It should start from 4.", source.Span{Start: 16, End: 17}},
		{"packet\n1-3: \"a\"", "packet/non-contiguous: Packet block 1 - 3 is not contiguous. It should start from 0.", source.Span{Start: 7, End: 8}},
		{"packet\n0-3: \"a\"\n+0: \"b\"", "packet/zero-bit-field: Packet block 4 is invalid. Cannot have a zero bit field.", source.Span{Start: 17, End: 18}},
		{"packet\n3-1: \"a\"", "packet/range-reversed: Packet block 3 - 1 is invalid. End must be greater than start.", source.Span{Start: 7, End: 10}},
	} {
		m, ds := resolve(tc.src)
		require.Equal(t, []string{tc.want}, messages(ds), tc.src)
		require.Equal(t, tc.span, ds[0].Span, tc.src)
		require.Empty(t, m.Pieces, tc.src)
	}
}

func TestOnlyTheFirstFailureIsReported(t *testing.T) {
	_, ds := resolve("packet\n0-3: \"a\"\n9-4: \"b\"\n20: \"c\"\n+0: \"d\"")
	require.Len(t, ds, 1)
	require.Equal(t, "packet/range-reversed", ds[0].Code)
}

func TestSplitRows(t *testing.T) {
	m, ds := resolve("packet\n0-15: \"a\"\n16-47: \"b\"\n48-63: \"c\"\n64: \"d\"")
	require.Empty(t, ds)
	require.Equal(t, [][3]int64{{0, 0, 15}, {0, 16, 31}, {1, 32, 47}, {1, 48, 63}, {2, 64, 64}}, spans(m))
	require.Equal(t, 3, m.Rows)
	require.Equal(t, []string{"a", "b", "b", "c", "d"}, []string{m.Pieces[0].Label, m.Pieces[1].Label, m.Pieces[2].Label, m.Pieces[3].Label, m.Pieces[4].Label})
	require.Equal(t, 1, m.Pieces[1].Field)
	require.Equal(t, 1, m.Pieces[2].Field)
}

func TestSplitStoresTheAdapterBitCounts(t *testing.T) {
	m, ds := resolve("packet\n0-63: \"wide\"\n64-71: \"tail\"")
	require.Empty(t, ds)
	require.Equal(t, []int64{31, 31, 8}, []int64{m.Pieces[0].Bits, m.Pieces[1].Bits, m.Pieces[2].Bits})
	require.Equal(t, int64(64), m.Fields[0].Bits)
	require.Equal(t, int64(63), m.Fields[0].End)
}

func TestSplitAcrossManyRows(t *testing.T) {
	_, ds := resolve("---\nconfig:\n  packet:\n    bitsPerRow: 8\n---\npacket\n3-26: \"x\"")
	require.NotEmpty(t, ds)
	m, ds := resolve("---\nconfig:\n  packet:\n    bitsPerRow: 8\n---\npacket\n0-26: \"x\"")
	require.Empty(t, ds)
	require.Equal(t, [][3]int64{{0, 0, 7}, {1, 8, 15}, {2, 16, 23}, {3, 24, 26}}, spans(m))
}

func TestWordCapStopsSilently(t *testing.T) {
	m, ds := resolve("---\nconfig:\n  packet:\n    bitsPerRow: 1\n---\npacket\n0-20000: \"x\"\n20001: \"y\"")
	require.Empty(t, ds)
	require.Equal(t, MaxWords, m.Rows)
	require.Len(t, m.Pieces, MaxWords)
	require.Equal(t, int64(MaxWords-1), m.Pieces[MaxWords-1].End)
}

func TestMetadataLastValueWins(t *testing.T) {
	m, ds := resolve("packet\ntitle first\naccTitle: a\naccDescr: d\ntitle second\naccTitle:\ntitle\n0: \"x\"")
	require.Empty(t, ds)
	require.Equal(t, "", m.Title)
	require.Equal(t, "", m.AccTitle)
	require.Equal(t, "d", m.AccDescr)
}

func TestConfigSources(t *testing.T) {
	m, ds := resolve("---\nconfig:\n  packet:\n    showBits: false\n    bitOrder: descending\n    bitsPerRow: 16\n    bitWidth: 20\n    paddingX: 0\n    rowHeight: 40\n    paddingY: 2\n---\n%%{init: {'packet': {'bitsPerRow': 8, 'showBits': true}}}%%\npacket\n0-3: \"x\"")
	require.Empty(t, ds)
	require.Equal(t, int64(8), m.BitsPerRow)
	require.True(t, m.ShowBits)
	require.True(t, m.Descending)
	keys := make([]string, len(m.Config))
	for i, e := range m.Config {
		keys[i] = e.Key
	}
	require.Equal(t, []string{"bitOrder", "bitWidth", "bitsPerRow", "paddingX", "paddingY", "rowHeight", "showBits"}, keys)
	require.Equal(t, ConfigEntry{Key: "bitsPerRow", Kind: ConfigInteger, Int: 8}, m.Config[2])
	require.Equal(t, ConfigEntry{Key: "showBits", Kind: ConfigBool, Bool: true}, m.Config[6])
	require.Equal(t, ConfigEntry{Key: "bitOrder", Kind: ConfigString, Text: "descending"}, m.Config[0])
}

func TestConfigRangesAndTypes(t *testing.T) {
	m, ds := resolve("---\nconfig:\n  packet:\n    bitsPerRow: 0\n    bitWidth: 2000\n    rowHeight: 1.5\n    paddingX: -1\n    showBits: yes\n    bitOrder: sideways\n    paddingY: 1024\n---\npacket\n0: \"x\"")
	require.Empty(t, ds)
	require.Equal(t, []ConfigEntry{{Key: "paddingY", Kind: ConfigInteger, Int: 1024}}, m.Config)
	require.Equal(t, int64(DefaultBitsPerRow), m.BitsPerRow)
}

func TestEmptyDocument(t *testing.T) {
	m, ds := resolve("packet")
	require.Empty(t, ds)
	require.Empty(t, m.Fields)
	require.Equal(t, 0, m.Rows)
	require.True(t, m.ShowBits)
}
