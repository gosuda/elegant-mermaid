package main

import (
	"fmt"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"
)

func TestLeanLayoutConstDefsOnePerConstant(t *testing.T) {
	defs, err := leanLayoutConstDefs([]layoutConstInput{
		{Name: "sequence.actor_width", Vector: 9600, Cell: 12},
		{Name: "node_gap", Vector: 1536, Cell: 2},
		{Name: "arrow_half", Vector: -256, Cell: 0},
	})
	require.NoError(t, err)
	require.Contains(t, defs, "def node_gap : Pair := ⟨1536, 2⟩\n")
	require.Contains(t, defs, "def sequence_actor_width : Pair := ⟨9600, 12⟩\n")
	require.Contains(t, defs, "def arrow_half : Pair := ⟨-256, 0⟩\n")
	require.Less(t, strings.Index(defs, "def arrow_half"), strings.Index(defs, "def node_gap"))
	require.Less(t, strings.Index(defs, "def node_gap"), strings.Index(defs, "def sequence_actor_width"))
}

func TestLeanLayoutConstDefsRejectNameCollision(t *testing.T) {
	_, err := leanLayoutConstDefs([]layoutConstInput{{Name: "a.b_c"}, {Name: "a_b.c"}})
	require.ErrorContains(t, err, "share the Lean name a_b_c")
}

func TestLeanLayoutConstDefsRejectUnusableNames(t *testing.T) {
	for _, name := range []string{"", "Node.gap", "a..b", "1x", "a b", "a.", ".a", "a-b"} {
		_, err := leanLayoutConstDefs([]layoutConstInput{{Name: name}})
		require.Error(t, err, "name %q", name)
	}
}

func TestLeanLayoutConstIdentQuotesKeywords(t *testing.T) {
	id, err := leanConstIdent("class")
	require.NoError(t, err)
	require.Equal(t, "«class»", id)
	id, err = leanConstIdent("class.padding")
	require.NoError(t, err)
	require.Equal(t, "class_padding", id)
}

func TestLayoutConstLeanKeepsTableAndImportsModelFirst(t *testing.T) {
	consts := []layoutConstInput{{Name: "node_gap", Vector: 1536, Cell: 2}}
	tbl := buildLayoutConstTable(consts)
	src, err := tbl.renderLean()
	require.NoError(t, err)
	plain, err := tbl.table.renderLean()
	require.NoError(t, err)
	text := string(src)
	require.True(t, strings.HasPrefix(text, leanHeader+"import Elegant.Model\n\n"+leanLayoutConstNote+"structure Const where"))
	require.Contains(t, text, strings.TrimPrefix(string(plain), leanHeader))
	require.Less(t, strings.Index(text, "opaque layoutconst : Array Const"), strings.Index(text, "namespace LayoutConst"))
}

func TestLayoutConstLeanTableOpaqueWhenDecoded(t *testing.T) {
	consts := make([]layoutConstInput, 0, leanDecodeRows)
	for i := range leanDecodeRows {
		consts = append(consts, layoutConstInput{Name: fmt.Sprintf("kind.row_%d", i), Vector: int32(i), Cell: 1})
	}
	src, err := buildLayoutConstTable(consts).renderLean()
	require.NoError(t, err)
	text := string(src)
	require.Contains(t, text, "opaque layoutconst : Array Const := Array.mk (List.filterMap decodeRow")
	require.Contains(t, text, "def kind_row_1023 : Pair := ⟨1023, 1⟩\n")
}
