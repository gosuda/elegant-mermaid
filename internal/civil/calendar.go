package civil

const weekdayCount = 7

var weekdayIDs = [weekdayCount + 1]string{"", "monday", "tuesday", "wednesday", "thursday", "friday", "saturday", "sunday"}

type Calendar struct {
	weekends     bool
	weekendStart int64
	named        [weekdayCount + 1]bool
	excludedDays map[int64]struct{}
	includedDays map[int64]struct{}
}

func WeekdayID(isoWeekday int64) string { return weekdayIDs[isoWeekday] }

func WeekdayIndex(id string) (int64, bool) {
	for i := 1; i <= weekdayCount; i++ {
		if weekdayIDs[i] == id {
			return int64(i), true
		}
	}
	return 0, false
}

func decimalField(text string) (int64, bool) {
	var n int64
	for i := range len(text) {
		c := text[i]
		if c < '0' || c > '9' {
			return 0, false
		}
		n = n*10 + int64(c-'0')
	}
	return n, true
}

func validDate(y, m, d int64) bool {
	return m >= 1 && m <= 12 && d >= 1 && d <= DaysInMonth(y, m)
}

func isoDayToken(token string) (int64, bool) {
	if len(token) != len("0000-00-00") || token[4] != '-' || token[7] != '-' {
		return 0, false
	}
	y, okYear := decimalField(token[0:4])
	m, okMonth := decimalField(token[5:7])
	d, okDay := decimalField(token[8:10])
	if !okYear || !okMonth || !okDay || !validDate(y, m, d) {
		return 0, false
	}
	return DaysFromCivil(y, m, d), true
}

func NewCalendar(excludes, includes []string, weekend string) *Calendar {
	c := &Calendar{weekendStart: 6, excludedDays: map[int64]struct{}{}, includedDays: map[int64]struct{}{}}
	if weekend == "friday" {
		c.weekendStart = 5
	}
	for _, token := range excludes {
		if token == "weekends" {
			c.weekends = true
		}
		if wd, ok := WeekdayIndex(token); ok {
			c.named[wd] = true
		}
		if day, ok := isoDayToken(token); ok {
			c.excludedDays[day] = struct{}{}
		}
	}
	for _, token := range includes {
		if day, ok := isoDayToken(token); ok {
			c.includedDays[day] = struct{}{}
		}
	}
	return c
}

func (c *Calendar) Excluded(day int64) bool {
	if _, ok := c.includedDays[day]; ok {
		return false
	}
	wd := ISOWeekday(day)
	if c.weekends && (wd == c.weekendStart || wd == c.weekendStart+1) {
		return true
	}
	if c.named[wd] {
		return true
	}
	_, ok := c.excludedDays[day]
	return ok
}
