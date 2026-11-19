package civil

import (
	"testing"
	"time"

	"github.com/stretchr/testify/require"
)

func TestCivilMatchesTime(t *testing.T) {
	for days := int64(-800000); days <= 800000; days += 37 {
		at := time.Unix(days*SecondsPerDay, 0).UTC()
		y, m, d := CivilFromDays(days)
		require.Equal(t, int64(at.Year()), y, days)
		require.Equal(t, int64(at.Month()), m, days)
		require.Equal(t, int64(at.Day()), d, days)
		require.Equal(t, days, DaysFromCivil(y, m, d))
		iso := int64(at.Weekday())
		if iso == 0 {
			iso = 7
		}
		require.Equal(t, iso, ISOWeekday(days))
		year, week := at.ISOWeek()
		gotWeek, gotYear := ISOWeek(days)
		require.Equal(t, int64(week), gotWeek, days)
		require.Equal(t, int64(year), gotYear, days)
	}
}

func TestSplitJoinRoundTrip(t *testing.T) {
	for _, seconds := range []int64{0, -1, 86399, 86400, -86400, 1705314600, -62135596800, 253402300799} {
		f := Split(seconds)
		require.Equal(t, seconds, Join(f.Year, f.Month, f.Day, f.Hour, f.Minute, f.Second))
		at := time.Unix(seconds, 0).UTC()
		require.Equal(t, int64(at.Hour()), f.Hour)
		require.Equal(t, int64(at.Minute()), f.Minute)
		require.Equal(t, int64(at.Second()), f.Second)
	}
}

func TestClampedMonthAdd(t *testing.T) {
	jan31 := Join(2024, 1, 31, 10, 20, 30)
	require.Equal(t, Join(2024, 2, 29, 10, 20, 30), ClampedMonthAdd(jan31, 1))
	require.Equal(t, Join(2025, 2, 28, 10, 20, 30), ClampedMonthAdd(jan31, 13))
	require.Equal(t, Join(2025, 1, 31, 10, 20, 30), ClampedMonthAdd(jan31, 12))
	require.Equal(t, Join(2023, 12, 31, 10, 20, 30), ClampedMonthAdd(jan31, -1))
}

func TestFloorHelpers(t *testing.T) {
	require.Equal(t, int64(-2), FloorDiv(-3, 2))
	require.Equal(t, int64(1), FloorMod(-3, 2))
	require.Equal(t, int64(3), FloorDiv(7, 2))
	require.Equal(t, int64(-4), FloorDiv(7, -2))
}
