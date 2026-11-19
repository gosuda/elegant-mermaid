package sequence

import (
	"testing"

	"github.com/stretchr/testify/require"
)

func TestAccessibilityBlockDropsRemovedCommentLines(t *testing.T) {
	const withComment = "sequenceDiagram\naccDescr {\nfirst\n%% c\nsecond\n}\nA->>B: x\n"
	const withoutComment = "sequenceDiagram\naccDescr {\nfirst\nsecond\n}\nA->>B: x\n"
	got, diags := resolveSource(withComment)
	require.Empty(t, diags)
	want, _ := resolveSource(withoutComment)
	require.Equal(t, "first\nsecond", want.AccDescr)
	require.Equal(t, want.AccDescr, got.AccDescr)
}
