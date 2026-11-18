package gantt

import (
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/civil"
	"github.com/gosuda/elegant-mermaid/internal/source"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/gantt"
)

const (
	maxScans           = 11
	exclusionLimitDays = int64(10000)
	exclusionStepCap   = 5_000_000
	codeInvalidDate    = "gantt/invalid-date"
	codeInvalidEnd     = "gantt/invalid-end"
	codePredecessor    = "gantt/predecessor-missing"
	codeUnknownRef     = "gantt/unknown-task-reference"
	codeExclusion      = "gantt/exclusion-limit"
	codeUnresolved     = "gantt/unresolved-task"
	dateOnlyFormat     = "YYYY-MM-DD"
)

type reportKey struct {
	task    int
	keyword string
	id      int
}

type scanState struct {
	seen     map[reportKey]struct{}
	steps    int
	calendar *civil.Calendar
}

func (s *scanState) first(k reportKey) bool {
	if s.seen == nil {
		s.seen = map[reportKey]struct{}{}
	}
	if _, dup := s.seen[k]; dup {
		return false
	}
	s.seen[k] = struct{}{}
	return true
}

func (t *Task) settled() bool { return t.Resolved || t.Failed }

func (t *Task) complete() bool { return t.Resolved && t.HasStart && t.HasEnd }

func (r *resolver) compile() {
	m := r.model
	r.scans.calendar = civil.NewCalendar(m.Excludes, m.Includes, m.Weekend)
	for range maxScans {
		if r.scan() {
			break
		}
	}
	for i := range m.Tasks {
		if t := &m.Tasks[i]; !t.Failed && !t.complete() {
			r.report(codeUnresolved, "task dates remain unresolved after eleven passes", t.DataSpan)
		}
	}
}

func (r *resolver) scan() bool {
	done := true
	for i := range r.model.Tasks {
		r.compileTask(i)
		done = done && r.model.Tasks[i].settled()
	}
	return done
}

func (r *resolver) compileTask(i int) {
	t := &r.model.Tasks[i]
	if t.Failed || !r.compileStart(i) || !t.HasStart {
		return
	}
	end, defined, ok := r.endDate(i)
	if !ok {
		return
	}
	t.EndSeconds, t.HasEnd = end, defined
	if !defined {
		return
	}
	t.Resolved = true
	_, t.ManualEnd = parseStrict(t.End.Text, dateOnlyFormat)
	r.checkDates(i)
}

func (r *resolver) compileStart(i int) bool {
	t := &r.model.Tasks[i]
	if t.StartKind == startPrevEnd {
		at, found := r.ids[t.PrevID]
		if !t.HasPrev || !found {
			r.report(codePredecessor, "task has no preceding task", t.End.Span)
			t.Failed = true
			return false
		}
		prev := &r.model.Tasks[at]
		t.StartSeconds, t.HasStart = prev.EndSeconds, prev.HasEnd
		return true
	}
	sec, defined, ok := r.startDate(i)
	if defined {
		t.StartSeconds, t.HasStart = sec, true
	}
	return ok
}

func allDigits(text string) bool {
	for i := range len(text) {
		if text[i] < '0' || text[i] > '9' {
			return false
		}
	}
	return text != ""
}

func (r *resolver) invalidDate(i int) (int64, bool, bool) {
	t := &r.model.Tasks[i]
	r.report(codeInvalidDate, "invalid date "+t.Start.Text, t.Start.Span)
	t.Failed = true
	return 0, false, false
}

func (r *resolver) startDate(i int) (sec int64, defined, ok bool) {
	t := &r.model.Tasks[i]
	format := trim(r.model.DateFormat)
	if (format == "x" || format == "X") && allDigits(t.Start.Text) {
		ms := digitsValue(toU16(t.Start.Text))
		if ms > maxMillis {
			return r.invalidDate(i)
		}
		return civil.FloorDiv(ms, millisPerSec), true, true
	}
	if refs, matched := referenceIDs(t.Start.Text, "after", t.Start.Span); matched {
		sec, defined := r.latestEnd(i, refs)
		return sec, defined, true
	}
	if ms, valid := parseStrict(t.Start.Text, format); valid {
		return civil.FloorDiv(ms, millisPerSec), true, true
	}
	if sec, valid := fallbackSeconds(t.Start.Text); valid {
		return sec, true, true
	}
	return r.invalidDate(i)
}

func (r *resolver) endDate(i int) (int64, bool, bool) {
	t := &r.model.Tasks[i]
	if refs, matched := referenceIDs(t.End.Text, "until", t.End.Span); matched {
		sec, defined := r.earliestStart(i, refs)
		return sec, defined, true
	}
	if ms, valid := parseStrict(t.End.Text, trim(r.model.DateFormat)); valid {
		sec := civil.FloorDiv(ms, millisPerSec)
		if next := sec + civil.SecondsPerDay; r.model.InclusiveEnd && validSeconds(next) {
			sec = next
		}
		return sec, true, true
	}
	d, unit, valid := parseDuration(t.End.Text)
	if !valid {
		if r.scans.first(reportKey{i, "end", 0}) {
			r.report(codeInvalidEnd, t.End.Text+" is neither a date nor a duration; task has zero duration", t.End.Span)
		}
		return t.StartSeconds, true, true
	}
	if end, ok := addDuration(t.StartSeconds, d, unit); ok {
		return end, true, true
	}
	return t.StartSeconds, true, true
}

type reference struct {
	id   string
	span source.Span
}

func idClass(c byte) bool {
	return c >= '0' && c <= '9' || c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c == '_' || c == '-' || c == ' '
}

func referenceIDs(text, keyword string, operand source.Span) ([]reference, bool) {
	rest, found := strings.CutPrefix(text, keyword)
	if !found {
		return nil, false
	}
	lead := len(rest) - len(strings.TrimLeftFunc(rest, syn.IsSpace))
	if lead == 0 {
		return nil, false
	}
	body := rest[lead:]
	run := 0
	for run < len(body) && idClass(body[run]) {
		run++
	}
	if run == 0 {
		_, first := utf8.DecodeRuneInString(rest)
		return nil, strings.IndexByte(rest[first:lead], ' ') >= 0
	}
	base := operand.Start + len(keyword) + lead
	var out []reference
	for at := 0; at < run; {
		if body[at] == ' ' {
			at++
			continue
		}
		end := at
		for end < run && body[end] != ' ' {
			end++
		}
		out = append(out, reference{id: body[at:end], span: source.Span{Start: base + at, End: base + end}})
		at = end
	}
	return out, true
}

func (r *resolver) unknownReference(i int, keyword string, k int, ref reference) {
	if r.scans.first(reportKey{i, keyword, k + 1}) {
		r.report(codeUnknownRef, keyword+" references unknown task id "+ref.id, ref.span)
	}
}

func (r *resolver) latestEnd(i int, refs []reference) (int64, bool) {
	var latest *Task
	for k, ref := range refs {
		at, found := r.ids[ref.id]
		if !found {
			r.unknownReference(i, "after", k, ref)
			continue
		}
		task := &r.model.Tasks[at]
		if latest == nil || (task.HasEnd && latest.HasEnd && task.EndSeconds > latest.EndSeconds) {
			latest = task
		}
	}
	if latest == nil {
		return 0, true
	}
	return latest.EndSeconds, latest.HasEnd
}

func (r *resolver) earliestStart(i int, refs []reference) (int64, bool) {
	var earliest *Task
	for k, ref := range refs {
		at, found := r.ids[ref.id]
		if !found {
			r.unknownReference(i, "until", k, ref)
			continue
		}
		task := &r.model.Tasks[at]
		if earliest == nil || (task.HasStart && earliest.HasStart && task.StartSeconds < earliest.StartSeconds) {
			earliest = task
		}
	}
	if earliest == nil {
		return 0, true
	}
	return earliest.StartSeconds, earliest.HasStart
}

func (r *resolver) checkDates(i int) {
	t := &r.model.Tasks[i]
	if len(r.model.Excludes) == 0 || t.ManualEnd {
		return
	}
	cal := r.scans.calendar
	start := t.StartSeconds + civil.SecondsPerDay
	end := t.EndSeconds
	limit := end + exclusionLimitDays*civil.SecondsPerDay
	invalid, hasRender := false, false
	var render int64
	for start <= end {
		if !invalid {
			render, hasRender = end, true
		}
		invalid = cal.Excluded(civil.FloorDiv(start, civil.SecondsPerDay))
		if invalid {
			end += civil.SecondsPerDay
		}
		r.scans.steps++
		if end > limit || r.scans.steps > exclusionStepCap {
			r.report(codeExclusion, "cannot find a non-excluded end within 10000 days", t.End.Span)
			t.Failed = true
			return
		}
		start += civil.SecondsPerDay
	}
	t.EndSeconds, t.RenderEnd, t.HasRenderEnd = end, render, hasRender
}
