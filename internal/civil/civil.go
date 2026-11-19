package civil

const (
	SecondsPerDay  = 86400
	MaxAbsSeconds  = 8_640_000_000_000
	monthsPerYear  = 12
	daysPerEra     = 146097
	epochShiftDays = 719468
)

func FloorDiv(a, b int64) int64 {
	q := a / b
	if a%b != 0 && (a < 0) != (b < 0) {
		q--
	}
	return q
}

func FloorMod(a, b int64) int64 { return a - FloorDiv(a, b)*b }

func DaysFromCivil(y, m, d int64) int64 {
	if m <= 2 {
		y--
	}
	era := FloorDiv(y, 400)
	yoe := y - era*400
	shifted := m + 9
	if m > 2 {
		shifted = m - 3
	}
	doy := (153*shifted+2)/5 + d - 1
	doe := yoe*365 + yoe/4 - yoe/100 + doy
	return era*daysPerEra + doe - epochShiftDays
}

func CivilFromDays(z int64) (y, m, d int64) {
	z += epochShiftDays
	era := FloorDiv(z, daysPerEra)
	doe := z - era*daysPerEra
	yoe := (doe - doe/1460 + doe/36524 - doe/146096) / 365
	y = yoe + era*400
	doy := doe - (365*yoe + yoe/4 - yoe/100)
	mp := (5*doy + 2) / 153
	d = doy - (153*mp+2)/5 + 1
	m = mp + 3
	if mp >= 10 {
		m = mp - 9
	}
	if m <= 2 {
		y++
	}
	return y, m, d
}

func IsLeap(y int64) bool {
	return FloorMod(y, 4) == 0 && (FloorMod(y, 100) != 0 || FloorMod(y, 400) == 0)
}

func DaysInMonth(y, m int64) int64 {
	switch m {
	case 2:
		if IsLeap(y) {
			return 29
		}
		return 28
	case 4, 6, 9, 11:
		return 30
	}
	return 31
}

func ISOWeekday(days int64) int64 { return FloorMod(days+3, 7) + 1 }

type Fields struct {
	Year, Month, Day         int64
	Hour, Minute, Second     int64
	Days, Weekday, SecondDay int64
}

func Split(seconds int64) Fields {
	days := FloorDiv(seconds, SecondsPerDay)
	rest := seconds - days*SecondsPerDay
	y, m, d := CivilFromDays(days)
	return Fields{
		Year: y, Month: m, Day: d,
		Hour: rest / 3600, Minute: rest % 3600 / 60, Second: rest % 60,
		Days: days, Weekday: ISOWeekday(days), SecondDay: rest,
	}
}

func Join(y, m, d, hh, mm, ss int64) int64 {
	return DaysFromCivil(y, m, d)*SecondsPerDay + hh*3600 + mm*60 + ss
}

func ClampedMonthAdd(seconds, months int64) int64 {
	f := Split(seconds)
	index := f.Year*monthsPerYear + (f.Month - 1) + months
	y := FloorDiv(index, monthsPerYear)
	m := FloorMod(index, monthsPerYear) + 1
	return Join(y, m, min(f.Day, DaysInMonth(y, m)), f.Hour, f.Minute, f.Second)
}

func ISOWeek(days int64) (week, weekYear int64) {
	thursday := days + 4 - ISOWeekday(days)
	y, _, _ := CivilFromDays(thursday)
	return (thursday-DaysFromCivil(y, 1, 1))/7 + 1, y
}
