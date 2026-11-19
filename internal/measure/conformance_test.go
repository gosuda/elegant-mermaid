package measure

import (
	"bufio"
	"os"
	"strconv"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"
)

type breakCase struct {
	line     int
	input    string
	clusters []string
}

func parseBreakCase(t *testing.T, line int, text string) (breakCase, bool) {
	t.Helper()
	fields := strings.Fields(strings.SplitN(text, "#", 2)[0])
	c := breakCase{line: line}
	var current strings.Builder
	for _, field := range fields {
		switch field {
		case "÷":
			if current.Len() > 0 {
				c.clusters = append(c.clusters, current.String())
				current.Reset()
			}
		case "×":
		default:
			cp, err := strconv.ParseUint(field, 16, 32)
			require.NoError(t, err, "line %d", line)
			if cp >= 0xD800 && cp <= 0xDFFF {
				return breakCase{}, false
			}
			current.WriteRune(rune(cp))
		}
	}
	require.Zero(t, current.Len(), "line %d does not end with a break", line)
	c.input = strings.Join(c.clusters, "")
	return c, true
}

func TestSegmentMatchesUnicodeBreakTest(t *testing.T) {
	file, err := os.Open("../../spec/data/unicode/GraphemeBreakTest.txt")
	require.NoError(t, err)
	defer func() { require.NoError(t, file.Close()) }()
	scanner := bufio.NewScanner(file)
	checked, surrogate := 0, 0
	for line := 1; scanner.Scan(); line++ {
		text := scanner.Text()
		if text == "" || strings.HasPrefix(text, "#") {
			continue
		}
		c, ok := parseBreakCase(t, line, text)
		if !ok {
			surrogate++
			continue
		}
		got := make([]string, 0, len(c.clusters))
		for _, cluster := range Segment(c.input) {
			got = append(got, cluster.Text)
		}
		require.Equal(t, c.clusters, got, "GraphemeBreakTest.txt line %d: %s", line, text)
		checked++
	}
	require.NoError(t, scanner.Err())
	require.Greater(t, checked, 800)
	require.Less(t, surrogate, 60)
}
