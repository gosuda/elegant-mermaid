package wardley

import "strings"

const (
	percentPlaces    = 5
	thousandthPlaces = 3
	saturation       = int64(1) << 40
	digitsLimit      = 12
)

type decimal struct{ whole, fraction string }

func parseDecimal(text string) decimal {
	whole, fraction, _ := strings.Cut(text, ".")
	return decimal{whole: strings.TrimLeft(whole, "0"), fraction: strings.TrimRight(fraction, "0")}
}

func (d decimal) atMostOne() bool {
	return d.whole == "" || d.whole == "1" && d.fraction == ""
}

func (d decimal) exceedsHundred() bool {
	switch {
	case len(d.whole) != len("100"):
		return len(d.whole) > len("100")
	case d.whole != "100":
		return d.whole > "100"
	}
	return d.fraction != ""
}

func (d decimal) scaled(places int) int64 {
	if len(d.whole)+places > digitsLimit {
		return saturation
	}
	digits := d.whole
	for i := range places {
		digits += string(fractionDigit(d.fraction, i))
	}
	var value int64
	for i := range len(digits) {
		value = value*10 + int64(digits[i]-'0')
	}
	if fractionDigit(d.fraction, places) >= '5' {
		value++
	}
	return value
}

func fractionDigit(fraction string, at int) byte {
	if at < len(fraction) {
		return fraction[at]
	}
	return '0'
}

func (d decimal) String() string {
	whole := d.whole
	if whole == "" {
		whole = "0"
	}
	if d.fraction == "" {
		return whole
	}
	return whole + "." + d.fraction
}

func toPercent(d decimal) (int64, bool) {
	switch {
	case d.atMostOne():
		return d.scaled(percentPlaces), true
	case d.exceedsHundred():
		return 0, false
	}
	return d.scaled(thousandthPlaces), true
}

func integer(text string, limit int64) int64 {
	var value int64
	for i := range len(text) {
		value = min(value*10+int64(text[i]-'0'), limit)
	}
	return value
}
