package civil

import (
	"strconv"
	"strings"
	"unicode/utf8"
)

var monthAbbrev = [...]string{"Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"}

var weekdayAbbrev = [...]string{"Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"}

func padSigned(n int64, width int) string {
	sign := ""
	if n < 0 {
		sign, n = "-", -n
	}
	digits := strconv.FormatInt(n, 10)
	if len(digits) < width {
		digits = strings.Repeat("0", width-len(digits)) + digits
	}
	return sign + digits
}

func directive(f Fields, code rune) (string, bool) {
	switch code {
	case 'Y':
		return padSigned(f.Year%10000, 4), true
	case 'm':
		return padSigned(f.Month, 2), true
	case 'd':
		return padSigned(f.Day, 2), true
	case 'H':
		return padSigned(f.Hour, 2), true
	case 'M':
		return padSigned(f.Minute, 2), true
	case 'S':
		return padSigned(f.Second, 2), true
	case 'a':
		return weekdayAbbrev[f.Weekday%7], true
	case 'b':
		return monthAbbrev[f.Month-1], true
	case '%':
		return "%", true
	}
	return "", false
}

func Format(seconds int64, format string) (text, unsupported string) {
	f := Split(seconds)
	var out strings.Builder
	for i := 0; i < len(format); {
		if format[i] != '%' {
			out.WriteByte(format[i])
			i++
			continue
		}
		code, n := utf8.DecodeRuneInString(format[i+1:])
		piece, ok := directive(f, code)
		if !ok && unsupported == "" {
			unsupported = format[i : i+1+n]
		}
		if ok {
			out.WriteString(piece)
		} else {
			out.WriteString(format[i : i+1+n])
		}
		i += 1 + n
	}
	return out.String(), unsupported
}
