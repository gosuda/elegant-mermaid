package langium

import (
	"testing"

	"github.com/stretchr/testify/require"
)

func TestNumericTerminalsFollowTheCommonRegexes(t *testing.T) {
	floats := map[string]int{"3.5": 3, "3.55.2": 3, "3.5.2": 0, "3.": 0, "12.50": 5, "x1.5": 0, "007.5": 5}
	for src, want := range floats {
		require.Equal(t, want, floatLength(src), src)
	}
	ints := map[string]int{"0": 1, "0.5": 1, "7": 1, "42": 2, "12.5": 1, "1.5": 0, "007": 1, "x": 0}
	for src, want := range ints {
		require.Equal(t, want, integerLength(src), src)
	}
}

func TestIDTerminalDropsTrailingDashes(t *testing.T) {
	ids := map[string]int{"a": 1, "a-b": 3, "a--": 1, "-a": 0, "a_b-1-": 5, "1x": 2, "": 0}
	for src, want := range ids {
		require.Equal(t, want, IDLength(src), src)
	}
}

func kinds(src string, g Grammar) []string {
	var out []string
	for _, token := range Lex(src, nil, g) {
		out = append(out, token.Kind)
	}
	return out
}

func TestKeywordGuardAndOrder(t *testing.T) {
	g := Grammar{Keywords: []Keyword{{Text: "kw:"}, {Text: "kw", Guard: true}}}
	require.Equal(t, []string{"kw", "EOF"}, kinds("kw", g))
	require.Equal(t, []string{"kw", "NEWLINE", "EOF"}, kinds("kw\n", g))
	require.Equal(t, []string{"kw", "EOF"}, kinds("kw%%x", g))
	require.Equal(t, []string{"ID", "EOF"}, kinds("kwx", g))
	require.Equal(t, []string{"kw:", "ID", "EOF"}, kinds("kw:x", g))
	require.Equal(t, []string{"kw", "INVALID", "EOF"}, kinds("kw\u00a0", g))
}

func TestTerminalPrecedence(t *testing.T) {
	g := Grammar{}
	require.Equal(t, []string{"BOOLEAN", "ID", "EOF"}, kinds("trueish", g))
	require.Equal(t, []string{"FLOAT", "INT", "STRING", "ID", "EOF"}, kinds("1.5 7 \"s\" name", g))
	require.Equal(t, []string{"TITLE", "NEWLINE", "ACC_TITLE", "NEWLINE", "ACC_DESCR", "EOF"}, kinds("title a\naccTitle: b\naccDescr: c", g))
	require.Equal(t, []string{"TITLE", "ID", "EOF"}, kinds("titlex", g))
	require.Equal(t, []string{"ID", "EOF"}, kinds("accDescr", g))
	require.Equal(t, []string{"INVALID", "INVALID", "EOF"}, kinds("!?", g))
}
