package mermaid_test

import (
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"slices"
	"testing"

	mermaid "github.com/gosuda/elegant-mermaid"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func kindIDsFromData(t *testing.T) []string {
	t.Helper()
	raw, err := os.ReadFile("spec/data/kinds.json")
	require.NoError(t, err)
	var rows []struct {
		ID string `json:"id"`
	}
	require.NoError(t, json.Unmarshal(raw, &rows))
	ids := make([]string, len(rows))
	for i, row := range rows {
		ids[i] = row.ID
	}
	return ids
}

func TestKindConstantsFollowKindsTable(t *testing.T) {
	want := kindIDsFromData(t)
	require.Len(t, want, 33)
	got := make([]string, mermaid.KindInfo+1)
	for i := range got {
		got[i] = mermaid.Kind(i).String()
	}
	assert.Equal(t, want, got)
}

func TestKindSetMatchesGeneratedTable(t *testing.T) {
	want := kindIDsFromData(t)
	generated := make([]string, len(gen.Kinds))
	for i, kind := range gen.Kinds {
		generated[i] = kind.ID
	}
	slices.Sort(generated)
	sortedWant := slices.Clone(want)
	slices.Sort(sortedWant)
	assert.Equal(t, sortedWant, generated)
}

func TestFixSafetyOrder(t *testing.T) {
	assert.Less(t, mermaid.FixSafe, mermaid.FixUnsafe)
}

func TestWireNames(t *testing.T) {
	assert.Equal(t, "error", mermaid.SeverityError.String())
	assert.Equal(t, "warning", mermaid.SeverityWarning.String())
	assert.Equal(t, "info", mermaid.SeverityInfo.String())
	assert.Equal(t, "safe", mermaid.FixSafe.String())
	assert.Equal(t, "unsafe", mermaid.FixUnsafe.String())
}

func TestErrorsAreDistinctAndWrappable(t *testing.T) {
	sentinels := []error{
		mermaid.ErrInvalidDocument,
		mermaid.ErrTooLarge,
		mermaid.ErrOverflow,
		mermaid.ErrBadConfig,
		mermaid.ErrBadIconPack,
	}
	for i, a := range sentinels {
		for j, b := range sentinels {
			if i != j {
				assert.False(t, errors.Is(a, b), "distinct sentinels %s and %s must not satisfy errors.Is", a, b)
			}
		}
		wrapped := fmt.Errorf("layout failed: %w", a)
		assert.True(t, errors.Is(wrapped, a), "%v must satisfy errors.Is against its own sentinel %s", wrapped, a)
		assert.Equal(t, "layout failed: "+a.Error(), wrapped.Error())
	}
}

func TestBlockHostOffset(t *testing.T) {
	block := mermaid.Block{
		Source: []byte("ab\r\nc\n"),
		Span:   mermaid.Span{Start: 10, End: 24},
		Lines: []mermaid.BlockLine{
			{HostOffset: 10, BlockOffset: 0, Len: 2},
			{HostOffset: 20, BlockOffset: 4, Len: 1},
		},
	}
	for _, test := range []struct{ offset, want int }{
		{-1, 10},
		{0, 10},
		{1, 11},
		{2, 12},
		{3, 12},
		{4, 20},
		{5, 21},
		{6, 21},
		{100, 21},
	} {
		assert.Equal(t, test.want, block.HostOffset(test.offset))
	}
	empty := mermaid.Block{Span: mermaid.Span{Start: 42}}
	for _, offset := range []int{-1, 0, 1, 100} {
		assert.Equal(t, 42, empty.HostOffset(offset))
	}
}

func TestOptionZeroValues(t *testing.T) {
	var layout mermaid.LayoutOptions
	assert.Equal(t, mermaid.ProfileVector, layout.Profile)
	assert.Empty(t, layout.Theme)
	assert.Zero(t, layout.Thoroughness)
	assert.Zero(t, layout.MaxWidth)
	assert.Equal(t, mermaid.Limits{}, layout.Limits)
	assert.Nil(t, layout.IconPacks)
	assert.Nil(t, layout.Config)
	var svg mermaid.SVGOptions
	assert.Equal(t, layout, svg.LayoutOptions)
	assert.Empty(t, svg.Background)
	assert.Equal(t, mermaid.TextFont, svg.Text)
	assert.Nil(t, svg.Outlines)
	assert.Empty(t, svg.IDPrefix)
	var text mermaid.TextOptions
	assert.Equal(t, layout, text.LayoutOptions)
	assert.Equal(t, mermaid.CharsetUnicode, text.Charset)
	assert.Equal(t, mermaid.ColorNone, text.Color)
	var lint mermaid.LintConfig
	assert.Nil(t, lint.Select)
	assert.Nil(t, lint.Ignore)
	assert.Nil(t, lint.Severity)
	assert.Nil(t, lint.Off)
}
