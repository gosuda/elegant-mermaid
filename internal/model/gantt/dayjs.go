package gantt

import (
	"strconv"
	"strings"
	"unicode/utf16"

	"github.com/gosuda/elegant-mermaid/internal/civil"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/gantt"
)

const (
	maxMillis      = int64(8_640_000_000_000_000)
	yearGuard      = int64(1_000_000)
	componentGuard = int64(1_000_000_000)
	digitSat       = int64(1_000_000_000_000_000)
	millisPerSec   = int64(1000)
)

var monthNames = [...]string{"January", "February", "March", "April", "May", "June", "July", "August", "September", "October", "November", "December"}

var weekdayNames = [...]string{"Sunday", "Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday"}

type u16 = []uint16

func toU16(s string) u16 { return utf16.Encode([]rune(s)) }

func isDigit(c uint16) bool { return c >= '0' && c <= '9' }

func isSpace16(c uint16) bool { return syn.IsSpace(rune(c)) }

func digitsValue(part u16) int64 {
	var n int64
	for _, c := range part {
		if !isDigit(c) {
			continue
		}
		n = min(n*10+int64(c-'0'), digitSat)
	}
	return n
}

func sameAt(in u16, at int, word string) bool {
	if at+len(word) > len(in) {
		return false
	}
	for i := range len(word) {
		if in[at+i] != uint16(word[i]) {
			return false
		}
	}
	return true
}

type span16 struct{ from, to int }

type matcher func(part u16) (span16, bool)

func firstRun(part u16, width int) (span16, bool) {
	for i := 0; i+width <= len(part); i++ {
		ok := true
		for j := range width {
			ok = ok && isDigit(part[i+j])
		}
		if ok {
			return span16{i, i + width}, true
		}
	}
	return span16{}, false
}

func matchDigits(width int) matcher {
	return func(part u16) (span16, bool) { return firstRun(part, width) }
}

func matchOneOrTwo(part u16) (span16, bool) {
	at, ok := firstRun(part, 1)
	if ok && at.to < len(part) && isDigit(part[at.to]) {
		at.to++
	}
	return at, ok
}

func matchSigned(part u16) (span16, bool) {
	for i := range part {
		from := i
		if part[i] == '+' || part[i] == '-' {
			i++
		}
		if i >= len(part) || !isDigit(part[i]) {
			continue
		}
		end := i
		for end < len(part) && isDigit(part[end]) {
			end++
		}
		return span16{from, end}, true
	}
	return span16{}, false
}

func digitsAt(part u16, i, n int) bool {
	if i < 0 || i+n > len(part) {
		return false
	}
	for k := range n {
		if !isDigit(part[i+k]) {
			return false
		}
	}
	return true
}

func signedOffsetEnd(part u16, i int) (int, bool) {
	if (part[i] != '+' && part[i] != '-') || !digitsAt(part, i+1, 2) {
		return 0, false
	}
	end := i + 3
	if end < len(part) && part[end] == ':' {
		end++
	}
	if digitsAt(part, end, 2) {
		end += 2
	}
	return end, true
}

func matchOffset(part u16) (span16, bool) {
	for i := range part {
		if part[i] == 'Z' {
			return span16{i, i + 1}, true
		}
		if end, ok := signedOffsetEnd(part, i); ok {
			return span16{i, end}, true
		}
	}
	return span16{}, false
}

func wordSeparator(c uint16) bool {
	switch c {
	case '-', '_', ':', '/', ',', '(', ')':
		return true
	}
	return isSpace16(c)
}

func matchWord(part u16) (span16, bool) {
	for i := 0; i < len(part); i++ {
		j := i
		for j < len(part) && isDigit(part[j]) {
			j++
		}
		if j >= len(part) || wordSeparator(part[j]) || isDigit(part[j]) {
			continue
		}
		end := j
		for end < len(part) && !wordSeparator(part[end]) && !isDigit(part[end]) {
			end++
		}
		return span16{i, end}, true
	}
	return span16{}, false
}

type civilParts struct {
	year, month, day, hours, minutes, seconds, millis int64
}

type parsed struct {
	civilParts
	afternoon  int8
	hoursSet   bool
	week, zone bool
	offset     int64
}

type expression struct {
	match matcher
	set   func(p *parsed, value u16) bool
}

func numeric(field func(p *parsed) *int64) func(p *parsed, value u16) bool {
	return func(p *parsed, value u16) bool {
		*field(p) = digitsValue(value)
		return true
	}
}

func signedValue(value u16) int64 {
	n := digitsValue(value)
	if len(value) > 0 && value[0] == '-' {
		return -n
	}
	return n
}

func zoneOffset(value u16) int64 {
	text := string(utf16.Decode(value))
	if text == "Z" {
		return 0
	}
	sign := text[0]
	minutes := int64(0)
	hh, _ := strconv.Atoi(text[1:3])
	minutes = int64(hh) * 60
	rest := strings.TrimPrefix(text[3:], ":")
	if len(rest) == 2 {
		mm, _ := strconv.Atoi(rest)
		minutes += int64(mm)
	}
	switch {
	case minutes == 0:
		return 0
	case sign == '+':
		return -minutes
	}
	return minutes
}

func setMeridiem(pm string) func(p *parsed, v u16) bool {
	return func(p *parsed, v u16) bool {
		p.afternoon = 2
		if string(utf16.Decode(v)) == pm {
			p.afternoon = 1
		}
		return true
	}
}

func scaledMillis(scale int64) func(p *parsed, v u16) bool {
	return func(p *parsed, v u16) bool { p.millis = digitsValue(v) * scale; return true }
}

func setQuarter(p *parsed, v u16) bool { p.month = (digitsValue(v)-1)*3 + 1; return true }

func setHours(p *parsed, v u16) bool { p.hours, p.hoursSet = digitsValue(v), true; return true }

func setShortMonth(p *parsed, v u16) bool { return setMonthName(p, v, 3) }

func setLongMonth(p *parsed, v u16) bool { return setMonthName(p, v, 0) }

func setSignedYear(p *parsed, v u16) bool { p.year = signedValue(v); return true }

func setTwoDigitYear(p *parsed, v u16) bool {
	n := digitsValue(v)
	p.year = n + 2000
	if n > 68 {
		p.year = n + 1900
	}
	return true
}

func setZone(p *parsed, v u16) bool { p.zone, p.offset = true, zoneOffset(v); return true }

func fieldSeconds(p *parsed) *int64 { return &p.seconds }
func fieldMinutes(p *parsed) *int64 { return &p.minutes }
func fieldMillis(p *parsed) *int64  { return &p.millis }
func fieldDays(p *parsed) *int64    { return &p.day }
func fieldMonths(p *parsed) *int64  { return &p.month }
func fieldYears(p *parsed) *int64   { return &p.year }

var expressions = map[string]expression{
	"A": {matchWord, setMeridiem("PM")}, "a": {matchWord, setMeridiem("pm")},
	"Q": {matchDigits(1), setQuarter},
	"S": {matchDigits(1), scaledMillis(100)}, "SS": {matchDigits(2), scaledMillis(10)}, "SSS": {matchDigits(3), numeric(fieldMillis)},
	"s": {matchOneOrTwo, numeric(fieldSeconds)}, "ss": {matchOneOrTwo, numeric(fieldSeconds)},
	"m": {matchOneOrTwo, numeric(fieldMinutes)}, "mm": {matchOneOrTwo, numeric(fieldMinutes)},
	"H": {matchOneOrTwo, setHours}, "h": {matchOneOrTwo, setHours}, "HH": {matchOneOrTwo, setHours}, "hh": {matchOneOrTwo, setHours},
	"D": {matchOneOrTwo, numeric(fieldDays)}, "DD": {matchDigits(2), numeric(fieldDays)}, "Do": {matchWord, setOrdinalDay},
	"w": {matchOneOrTwo, setWeek}, "ww": {matchDigits(2), setWeek},
	"M": {matchOneOrTwo, numeric(fieldMonths)}, "MM": {matchDigits(2), numeric(fieldMonths)},
	"MMM": {matchWord, setShortMonth}, "MMMM": {matchWord, setLongMonth},
	"Y": {matchSigned, setSignedYear}, "YY": {matchDigits(2), setTwoDigitYear}, "YYYY": {matchDigits(4), numeric(fieldYears)},
	"Z": {matchOffset, setZone}, "ZZ": {matchOffset, setZone},
}

func expressionFor(token string) (expression, bool) {
	e, ok := expressions[token]
	return e, ok
}

func setWeek(p *parsed, value u16) bool {
	p.week = digitsValue(value) != 0
	return true
}

func setMonthName(p *parsed, value u16, width int) bool {
	text := string(utf16.Decode(value))
	for i, name := range monthNames {
		candidate := name
		if width == 3 {
			candidate = name[:3]
		}
		if candidate == text {
			p.month = int64(i + 1)
			return true
		}
	}
	return false
}

func ordinalSuffix(day int64) string {
	switch day % 100 {
	case 1, 21, 31:
		return "st"
	case 2, 22:
		return "nd"
	case 3, 23:
		return "rd"
	}
	return "th"
}

func setOrdinalDay(p *parsed, value u16) bool {
	at, ok := firstRun(value, 1)
	if !ok {
		return false
	}
	end := at.to
	for end < len(value) && isDigit(value[end]) {
		end++
	}
	p.day = digitsValue(value[at.from:end])
	text := string(utf16.Decode(value))
	for d := int64(1); d <= 31; d++ {
		if strconv.FormatInt(d, 10)+ordinalSuffix(d) == text {
			p.day = d
		}
	}
	return true
}

type formatToken struct {
	literal int
	name    string
}

func bracketEnd(f u16, at int) int {
	if f[at] != '[' {
		return -1
	}
	last := -1
	for k := at + 1; k < len(f) && f[k] != '['; k++ {
		if f[k] == ']' {
			last = k
		}
	}
	return last
}

func separatorRun(f u16, at int) int {
	end := at
	for end < len(f) && wordSeparator16(f[end]) {
		end++
	}
	return end
}

func wordSeparator16(c uint16) bool {
	switch c {
	case '-', '_', ':', '/', '.', ',', '(', ')':
		return true
	}
	return isSpace16(c)
}

func repeated(f u16, at int, c byte, limit int) int {
	n := 0
	for at+n < len(f) && f[at+n] == uint16(c) && n < limit {
		n++
	}
	return n
}

func tokenAt(f u16, at int) (string, bool) {
	c := byte(0)
	if f[at] < 128 {
		c = byte(f[at])
	}
	switch c {
	case 'A', 'a', 'Q', 'z':
		return string(c), true
	case 'Y':
		if repeated(f, at, 'Y', 4) == 4 {
			return "YYYY", true
		}
		return strings.Repeat("Y", repeated(f, at, 'Y', 2)), true
	case 'w', 'h', 'H', 'm', 's', 'Z':
		return strings.Repeat(string(c), repeated(f, at, c, 2)), true
	case 'M':
		return strings.Repeat("M", repeated(f, at, 'M', 4)), true
	case 'D':
		if sameAt(f, at, "Do") {
			return "Do", true
		}
		return strings.Repeat("D", repeated(f, at, 'D', 2)), true
	case 'S':
		return strings.Repeat("S", repeated(f, at, 'S', 3)), true
	}
	return "", false
}

func formatTokens(f u16) []formatToken {
	var out []formatToken
	for i := 0; i < len(f); {
		if end := bracketEnd(f, i); end >= 0 {
			out = append(out, formatToken{literal: end - i - 1})
			i = end + 1
			continue
		}
		if run := separatorRun(f, i); run > i {
			out = append(out, formatToken{literal: run - i})
			i = run
			continue
		}
		if name, ok := tokenAt(f, i); ok {
			if _, parses := expressionFor(name); parses {
				out = append(out, formatToken{literal: -1, name: name})
			} else {
				out = append(out, formatToken{literal: len(name)})
			}
			i += len(name)
			continue
		}
		i++
	}
	return out
}

func hasLocalized(format string) bool {
	f := toU16(format)
	for i := 0; i < len(f); i++ {
		if end := innerBracket(f, i); end >= 0 {
			i = end
			continue
		}
		if f[i] == 'L' || f[i] == 'l' {
			return true
		}
	}
	return false
}

func innerBracket(f u16, at int) int {
	if f[at] != '[' {
		return -1
	}
	for k := at + 1; k < len(f); k++ {
		if f[k] == ']' {
			if k == at+1 {
				return -1
			}
			return k
		}
	}
	return -1
}

func indexOf16(in, value u16) int {
	for i := 0; i+len(value) <= len(in); i++ {
		match := true
		for j := range value {
			if in[i+j] != value[j] {
				match = false
				break
			}
		}
		if match {
			return i
		}
	}
	return -1
}

func parseFormatted(input, format string) (int64, bool) {
	if hasLocalized(format) {
		return 0, false
	}
	tokens := formatTokens(toU16(format))
	if len(tokens) == 0 {
		return 0, false
	}
	in := toU16(input)
	var p parsed
	start := 0
	for _, token := range tokens {
		if token.literal >= 0 {
			start += token.literal
			continue
		}
		expr, _ := expressionFor(token.name)
		part := in
		if start < len(in) {
			part = in[start:]
		} else {
			part = nil
		}
		at, ok := expr.match(part)
		if !ok {
			return 0, false
		}
		value := part[at.from:at.to]
		if !expr.set(&p, value) {
			return 0, false
		}
		if i := indexOf16(in, value); i >= 0 {
			in = append(append(u16{}, in[:i]...), in[i+len(value):]...)
		}
	}
	return p.instant()
}

func (p *parsed) correctHours() {
	if p.afternoon == 0 || !p.hoursSet {
		return
	}
	if p.afternoon == 1 && p.hours < 12 {
		p.hours += 12
	} else if p.afternoon == 2 && p.hours == 12 {
		p.hours = 0
	}
}

func (p *parsed) instant() (int64, bool) {
	p.correctHours()
	if p.week {
		return 0, false
	}
	parts := p.civilParts
	if parts.day == 0 {
		parts.day = 1
	}
	if parts.year == 0 {
		parts.year = 1970
	}
	parts.month = max(parts.month-1, 0)
	if p.zone {
		parts.millis += p.offset * 60 * 1000
	}
	return parts.instant()
}

func (c civilParts) instant() (int64, bool) {
	year := c.year
	if year >= 0 && year <= 99 {
		year += 1900
	}
	for _, v := range [...]int64{c.month, c.day, c.hours, c.minutes, c.seconds} {
		if v > componentGuard || v < -componentGuard {
			return 0, false
		}
	}
	if year > yearGuard || year < -yearGuard {
		return 0, false
	}
	y := year + civil.FloorDiv(c.month, 12)
	m := civil.FloorMod(c.month, 12) + 1
	days := civil.DaysFromCivil(y, m, 1) + c.day - 1
	total := days*86400*millisPerSec + c.hours*3600*millisPerSec + c.minutes*60*millisPerSec + c.seconds*millisPerSec + c.millis
	return total, total <= maxMillis && total >= -maxMillis
}

func padNumber(n int64, width int) string {
	s := strconv.FormatInt(n, 10)
	if len(s) >= width {
		return s
	}
	return strings.Repeat("0", width-len(s)) + s
}

type formatContext struct {
	fields civil.Fields
	millis int64
	total  int64
}

func newFormatContext(total int64) formatContext {
	secs := civil.FloorDiv(total, millisPerSec)
	return formatContext{fields: civil.Split(secs), millis: civil.FloorMod(total, millisPerSec), total: total}
}

func scanAlternatives(text string, alternatives []string) (string, bool) {
	for _, alt := range alternatives {
		if strings.HasPrefix(text, alt) {
			return alt, true
		}
	}
	return "", false
}

func bracketSpan(text string) (int, bool) {
	if text == "" || text[0] != '[' {
		return 0, false
	}
	end := strings.IndexByte(text[1:], ']')
	if end <= 0 {
		return 0, false
	}
	return end + 2, true
}

var advancedTokens = []string{"wo", "ww", "w", "WW", "W", "zzz", "z", "gggg", "GGGG", "Do", "X", "x", "kk", "k", "S", "Q"}

func isoWeekOf(c formatContext) (week, weekYear int64) { return civil.ISOWeek(c.fields.Days) }

func clockHour24(c formatContext) int64 {
	if c.fields.Hour == 0 {
		return 24
	}
	return c.fields.Hour
}

var advancedRenderers = map[string]func(formatContext) string{
	"Q": func(c formatContext) string { return strconv.FormatInt((c.fields.Month-1)/3+1, 10) },
	"Do": func(c formatContext) string {
		return "[" + strconv.FormatInt(c.fields.Day, 10) + ordinalSuffix(c.fields.Day) + "]"
	},
	"GGGG": func(c formatContext) string {
		_, weekYear := isoWeekOf(c)
		return strconv.FormatInt(weekYear, 10)
	},
	"W": func(c formatContext) string {
		week, _ := isoWeekOf(c)
		return padNumber(week, 1)
	},
	"WW": func(c formatContext) string {
		week, _ := isoWeekOf(c)
		return padNumber(week, 2)
	},
	"k":  padText(clockHour24, 1),
	"kk": padText(clockHour24, 2),
	"X":  func(c formatContext) string { return strconv.FormatInt(civil.FloorDiv(c.total, millisPerSec), 10) },
	"x":  func(c formatContext) string { return strconv.FormatInt(c.total, 10) },
	"S":  func(formatContext) string { return "S" },
}

func (c formatContext) advanced(token string) (string, bool) {
	render, ok := advancedRenderers[token]
	if !ok {
		return "", false
	}
	return render(c), true
}

func (c formatContext) advancedPass(format string) (string, bool) {
	var out strings.Builder
	for i := 0; i < len(format); {
		if n, ok := bracketSpan(format[i:]); ok {
			out.WriteString(format[i : i+n])
			i += n
			continue
		}
		token, ok := scanAlternatives(format[i:], advancedTokens)
		if !ok {
			out.WriteByte(format[i])
			i++
			continue
		}
		text, supported := c.advanced(token)
		if !supported {
			return "", false
		}
		out.WriteString(text)
		i += len(token)
	}
	return out.String(), true
}

func meridiemOf(c formatContext) string {
	if c.fields.Hour >= 12 {
		return "PM"
	}
	return "AM"
}

func hour12Of(c formatContext) int64 {
	if h := c.fields.Hour % 12; h != 0 {
		return h
	}
	return 12
}

func intText(read func(c formatContext) int64) func(formatContext) string {
	return func(c formatContext) string { return strconv.FormatInt(read(c), 10) }
}

func padText(read func(c formatContext) int64, width int) func(formatContext) string {
	return func(c formatContext) string { return padNumber(read(c), width) }
}

func nameText(names *[12]string, width int) func(formatContext) string {
	return func(c formatContext) string {
		name := names[c.fields.Month-1]
		return name[:min(width, len(name))]
	}
}

func weekdayText(width int) func(formatContext) string {
	return func(c formatContext) string {
		name := weekdayNames[c.fields.Weekday%7]
		return name[:min(width, len(name))]
	}
}

func fieldYear(c formatContext) int64    { return c.fields.Year }
func fieldMonth(c formatContext) int64   { return c.fields.Month }
func fieldDay(c formatContext) int64     { return c.fields.Day }
func fieldHour(c formatContext) int64    { return c.fields.Hour }
func fieldMinute(c formatContext) int64  { return c.fields.Minute }
func fieldSecond(c formatContext) int64  { return c.fields.Second }
func fieldWeekday(c formatContext) int64 { return c.fields.Weekday % 7 }

var coreRenderers = map[string]func(formatContext) string{
	"YYYY": padText(fieldYear, 4),
	"YY": func(c formatContext) string {
		s := strconv.FormatInt(c.fields.Year, 10)
		return s[max(len(s)-2, 0):]
	},
	"M":    intText(fieldMonth),
	"MM":   padText(fieldMonth, 2),
	"MMM":  nameText(&monthNames, 3),
	"MMMM": nameText(&monthNames, len("September")),
	"D":    intText(fieldDay),
	"DD":   padText(fieldDay, 2),
	"d":    intText(fieldWeekday),
	"dd":   weekdayText(2),
	"ddd":  weekdayText(3),
	"dddd": weekdayText(len("Wednesday")),
	"H":    intText(fieldHour),
	"HH":   padText(fieldHour, 2),
	"h":    intText(hour12Of),
	"hh":   padText(hour12Of, 2),
	"a":    func(c formatContext) string { return strings.ToLower(meridiemOf(c)) },
	"A":    meridiemOf,
	"m":    intText(fieldMinute),
	"mm":   padText(fieldMinute, 2),
	"s":    intText(fieldSecond),
	"ss":   padText(fieldSecond, 2),
	"SSS":  padText(func(c formatContext) int64 { return c.millis }, 3),
	"Z":    func(formatContext) string { return "+00:00" },
}

func (c formatContext) core(token string) string {
	if render, ok := coreRenderers[token]; ok {
		return render(c)
	}
	return "+0000"
}

var coreTokens = []string{
	"YYYY", "YY", "MMMM", "MMM", "MM", "M", "DD", "D", "dddd", "ddd", "dd", "d", "HH", "H", "hh", "h",
	"a", "A", "mm", "m", "ss", "s", "ZZ", "Z", "SSS",
}

func (c formatContext) corePass(format string) string {
	var out strings.Builder
	for i := 0; i < len(format); {
		if n, ok := bracketSpan(format[i:]); ok {
			out.WriteString(format[i+1 : i+n-1])
			i += n
			continue
		}
		token, ok := scanAlternatives(format[i:], coreTokens)
		if !ok {
			out.WriteByte(format[i])
			i++
			continue
		}
		out.WriteString(c.core(token))
		i += len(token)
	}
	return out.String()
}

func formatMillis(total int64, format string) (string, bool) {
	c := newFormatContext(total)
	mid, ok := c.advancedPass(format)
	if !ok {
		return "", false
	}
	return c.corePass(mid), true
}

func canonicalInteger(text string) (int64, bool) {
	body := strings.TrimPrefix(text, "-")
	if body == "" || (len(body) > 1 && body[0] == '0') || len(body) > 17 {
		return 0, false
	}
	for i := range len(body) {
		if body[i] < '0' || body[i] > '9' {
			return 0, false
		}
	}
	if text == "-0" {
		return 0, false
	}
	n, err := strconv.ParseInt(text, 10, 64)
	return n, err == nil
}

func parseTimestamp(input, format string) (int64, bool) {
	n, ok := canonicalInteger(input)
	if !ok {
		return 0, false
	}
	if format == "X" {
		if n < -maxMillis/millisPerSec || n > maxMillis/millisPerSec {
			return 0, false
		}
		n *= millisPerSec
	}
	return n, n <= maxMillis && n >= -maxMillis
}

func parseStrict(input, format string) (int64, bool) {
	if format == "x" || format == "X" {
		return parseTimestamp(input, format)
	}
	total, ok := parseFormatted(input, format)
	if !ok {
		return 0, false
	}
	text, ok := formatMillis(total, format)
	return total, ok && text == input
}
