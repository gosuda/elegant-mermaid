package gantt

import (
	"encoding/json"
	"os"
	"testing"

	"github.com/stretchr/testify/require"
)

func TestStrictParseMatchesDayjs(t *testing.T) {
	data, err := os.ReadFile("testdata/dayjs_cases.json")
	require.NoError(t, err)
	var cases [][3]any
	require.NoError(t, json.Unmarshal(data, &cases))
	require.NotEmpty(t, cases)
	valid := 0
	for _, c := range cases {
		format, input := c[0].(string), c[1].(string)
		got, ok := parseStrict(input, format)
		if c[2] == nil {
			require.False(t, ok, "%q %q parsed to %d", format, input, got)
			continue
		}
		valid++
		require.True(t, ok, "%q %q", format, input)
		require.Equal(t, int64(c[2].(float64)), got, "%q %q", format, input)
	}
	require.Greater(t, valid, 100)
}
