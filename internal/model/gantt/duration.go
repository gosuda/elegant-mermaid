package gantt

import (
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/civil"
)

const (
	fracDigits = 15
	fracScale  = int64(1_000_000_000_000_000)
	wholeSat   = int64(100_000_000_000_000_000)
	maxDays    = int64(200_000_000)
	maxSeconds = int64(10_000_000_000_000)
	maxCount   = int64(1_000_000_000)
)

type decimal struct {
	whole int64
	frac  int64
}

func validSeconds(s int64) bool { return s <= civil.MaxAbsSeconds && s >= -civil.MaxAbsSeconds }

var durationUnits = []string{"M", "d", "h", "m", "s", "w", "y", "ms"}

func isDigitByte(c byte) bool { return c >= '0' && c <= '9' }

func scanWhole(text string, d *decimal) int {
	i := 0
	for i < len(text) && isDigitByte(text[i]) {
		d.whole = min(d.whole*10+int64(text[i]-'0'), wholeSat)
		i++
	}
	return i
}

func scanFraction(text string, i int, d *decimal) (int, bool) {
	if i >= len(text) || text[i] != '.' {
		return i, true
	}
	i++
	start := i
	for i < len(text) && isDigitByte(text[i]) {
		if i-start < fracDigits {
			d.frac = d.frac*10 + int64(text[i]-'0')
		}
		i++
	}
	for n := i - start; n < fracDigits; n++ {
		d.frac *= 10
	}
	return i, i > start
}

func parseDuration(text string) (decimal, string, bool) {
	var d decimal
	i := scanWhole(text, &d)
	if i == 0 {
		return decimal{}, "", false
	}
	i, ok := scanFraction(text, i, &d)
	unit := text[i:]
	if !ok || !slices.Contains(durationUnits, unit) {
		return decimal{}, "", false
	}
	return d, unit, true
}

func (d decimal) scaled(n int64) int64 { return d.whole*n + (d.frac*n+fracScale/2)/fracScale }

func (d decimal) seconds(factor int64) (int64, bool) {
	if d.whole > maxSeconds {
		return 0, false
	}
	return d.whole*factor + d.frac*factor/fracScale, true
}

func addDuration(prev int64, d decimal, unit string) (int64, bool) {
	var delta int64
	ok := true
	switch unit {
	case "d":
		delta, ok = daysToSeconds(d.scaled(1))
	case "w":
		delta, ok = daysToSeconds(d.scaled(7))
	case "h":
		delta, ok = d.seconds(3600)
	case "m":
		delta, ok = d.seconds(60)
	case "s":
		delta, ok = d.seconds(1)
	case "ms":
		delta = d.whole / 1000
	case "M":
		return calendarAdd(prev, d.whole, 1)
	default:
		return calendarAdd(prev, yearDelta(prev, d), 12)
	}
	end := prev + delta
	return end, ok && validSeconds(end)
}

func daysToSeconds(days int64) (int64, bool) {
	if days > maxDays {
		return 0, false
	}
	return days * civil.SecondsPerDay, true
}

func yearDelta(prev int64, d decimal) int64 {
	base := civil.Split(prev).Year + d.whole
	if base < 0 && d.frac > 0 {
		base++
	}
	return base - civil.Split(prev).Year
}

func calendarAdd(prev, count, monthsEach int64) (int64, bool) {
	if count > maxCount || count < -maxCount {
		return 0, false
	}
	end := civil.ClampedMonthAdd(prev, count*monthsEach)
	return end, validSeconds(end)
}
