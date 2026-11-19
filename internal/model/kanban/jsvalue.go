package kanban

import (
	"errors"
	"math"
	"slices"
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/syntax"
)

const objectText = "[object Object]"

func number(text string) float64 {
	value, err := strconv.ParseFloat(text, 64)
	if err != nil && !errors.Is(err, strconv.ErrRange) {
		return math.NaN()
	}
	return value
}

func truthy(value syntax.ConfigValue) bool {
	switch value.Kind {
	case syntax.ValueNull:
		return false
	case syntax.ValueBool:
		return value.Bool
	case syntax.ValueInteger, syntax.ValueDecimal:
		parsed := number(value.Text)
		return parsed != 0 && !math.IsNaN(parsed)
	case syntax.ValueString:
		return value.Text != ""
	}
	return true
}

func jsString(value syntax.ConfigValue) string {
	switch value.Kind {
	case syntax.ValueBool:
		return strconv.FormatBool(value.Bool)
	case syntax.ValueInteger, syntax.ValueDecimal:
		return jsNumber(number(value.Text))
	case syntax.ValueString:
		return value.Text
	case syntax.ValueSequence:
		parts := make([]string, len(value.Items))
		for i, item := range value.Items {
			parts[i] = jsString(item)
		}
		return strings.Join(parts, ",")
	case syntax.ValueMapping:
		return objectText
	}
	return ""
}

func convertible(value syntax.ConfigValue) bool {
	switch value.Kind {
	case syntax.ValueSequence:
		return !slices.ContainsFunc(value.Items, func(item syntax.ConfigValue) bool { return !convertible(item) })
	case syntax.ValueMapping:
		return !slices.ContainsFunc(value.Entries, func(entry syntax.ConfigEntry) bool { return entry.Key == "toString" })
	}
	return true
}

func jsNumber(value float64) string {
	switch {
	case math.IsNaN(value):
		return "NaN"
	case math.IsInf(value, 1):
		return "Infinity"
	case math.IsInf(value, -1):
		return "-Infinity"
	case value == 0:
		return "0"
	}
	sign := ""
	if value < 0 {
		sign, value = "-", -value
	}
	mantissa, exponent, _ := strings.Cut(strconv.FormatFloat(value, 'e', -1, 64), "e")
	digits := strings.Replace(mantissa, ".", "", 1)
	return sign + layoutDigits(digits, exponentOf(exponent)+1)
}

func exponentOf(text string) int {
	power := 0
	for _, c := range []byte(strings.TrimLeft(text, "+-")) {
		power = power*10 + int(c-'0')
	}
	if strings.HasPrefix(text, "-") {
		return -power
	}
	return power
}

func layoutDigits(digits string, point int) string {
	k := len(digits)
	switch {
	case k <= point && point <= 21:
		return digits + strings.Repeat("0", point-k)
	case 0 < point && point <= 21:
		return digits[:point] + "." + digits[point:]
	case -6 < point && point <= 0:
		return "0." + strings.Repeat("0", -point) + digits
	}
	scale := point - 1
	sign := "+"
	if scale < 0 {
		sign, scale = "-", -scale
	}
	if k == 1 {
		return digits + "e" + sign + strconv.Itoa(scale)
	}
	return digits[:1] + "." + digits[1:] + "e" + sign + strconv.Itoa(scale)
}
