package syntax

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/stretchr/testify/require"
)

func TestCommentLineAbsorbsBlankLinesBeforeIt(t *testing.T) {
	src := "flowchart TD\nA-->B\n\n  \n  %% c\nC-->D\n"
	require.Equal(t, []source.Span{{Start: 19, End: 30}}, Preprocess([]byte(src)).Removed)
}

func TestBlankLinesWithoutCommentAreKept(t *testing.T) {
	src := "flowchart TD\nA-->B\n\n  \nC-->D\n"
	require.Empty(t, Preprocess([]byte(src)).Removed)
}

func TestAdjacentCommentLinesShareOneRemovedSpan(t *testing.T) {
	src := "flowchart TD\n%% a\n%% b\nA\n"
	require.Equal(t, []source.Span{{Start: 13, End: 23}}, Preprocess([]byte(src)).Removed)
}

func TestCommentLineAbsorbsDirectiveLinesAmongBlankLines(t *testing.T) {
	src := "flowchart TD\n%%{x: 1}%%\n\n%%{y: 2}%%\n%% c\nA-->B\n"
	require.Equal(t, []source.Span{{Start: 13, End: 41}}, Preprocess([]byte(src)).Removed)
}

func TestBarePercentCommentBoundaries(t *testing.T) {
	for _, ending := range []string{"", "\n", "\r\n", "\r"} {
		for _, comment := range []string{"%%", " \t%%", "%% text", "%% {not a directive}"} {
			src := "info\n" + comment + ending
			require.Equal(t, []source.Span{{Start: 5, End: len(src)}}, Preprocess([]byte(src)).Removed, "%q", src)
		}
	}
}

func TestPercentInsideStatementIsLabelContent(t *testing.T) {
	for _, line := range []string{`A["%%"]`, `A["text %% label"]`, "A --> B %% trailing", "%", " \t%"} {
		src := []byte("flowchart TD\n" + line + "\r\n")
		require.Empty(t, Preprocess(src).Removed, "%q", src)
	}
}

func TestPercentDirectiveTakesPrecedenceOverComment(t *testing.T) {
	for _, ending := range []string{"", "\n", "\r\n", "\r"} {
		src := "%%{wrap}%%" + ending + "info"
		got := Preprocess([]byte(src))
		require.True(t, got.Wrap)
		require.Equal(t, []source.Span{{Start: 0, End: 10}}, got.Removed)
	}
}
