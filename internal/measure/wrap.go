package measure

import (
	"sort"
	"strings"
)

type Line struct {
	Text      string
	Separator string
	Width     int32
}

func Wrap(s string, target int32, m Metric) ([]Line, error) {
	lines := make([]Line, 0, len(s)/8+1)
	for _, part := range splitForced(s) {
		partLines, err := wrapPart(part.text, target, m)
		if err != nil {
			return nil, err
		}
		lines = appendForced(lines, partLines, part.forced)
	}
	return lines, nil
}

type part struct {
	text   string
	forced string
}

var forcedBreaks = [...]string{"<br>", "<br/>", "<br />"}

func splitForced(s string) []part {
	parts := make([]part, 0, 4)
	rest := s
	for {
		index, token, ok := findForced(rest)
		if !ok {
			return append(parts, part{text: rest})
		}
		parts = append(parts, part{text: rest[:index], forced: token})
		rest = rest[index+len(token):]
	}
}

func findForced(s string) (int, string, bool) {
	best, token := -1, ""
	for _, candidate := range forcedBreaks {
		at := indexFoldASCII(s, candidate)
		if at >= 0 && (best < 0 || at < best) {
			best, token = at, candidate
		}
	}
	return best, token, best >= 0
}

func indexFoldASCII(s, needle string) int {
	for at := 0; at+len(needle) <= len(s); at++ {
		if strings.EqualFold(s[at:at+len(needle)], needle) {
			return at
		}
	}
	return -1
}

func appendForced(lines, partLines []Line, forced string) []Line {
	if forced == "" {
		return append(lines, partLines...)
	}
	if len(partLines) == 0 {
		return append(lines, Line{Separator: forced})
	}
	last := len(partLines) - 1
	partLines[last].Separator += forced
	return append(lines, partLines...)
}

type opportunity struct {
	at        int
	next      int
	separator string
}

type wrapper struct {
	clusters []Cluster
	metric   Metric
	upem     int64
	prefix   []int64
}

func wrapPart(s string, target int32, m Metric) ([]Line, error) {
	w, err := newWrapper(s, m)
	if err != nil {
		return nil, err
	}
	return w.run(target)
}

func newWrapper(s string, m Metric) (*wrapper, error) {
	w := &wrapper{clusters: Segment(s), metric: m}
	if m.Profile == ProfileVector {
		upem, err := Upem(m.Weight)
		if err != nil {
			return nil, err
		}
		w.upem = int64(upem)
	}
	w.prefix = make([]int64, len(w.clusters)+1)
	for i, c := range w.clusters {
		span, err := w.clusterSpan(c)
		if err != nil {
			return nil, err
		}
		w.prefix[i+1] = w.prefix[i] + span
	}
	return w, nil
}

func (w *wrapper) clusterSpan(c Cluster) (int64, error) {
	if w.metric.Profile == ProfileCell {
		return int64(ClusterWidth(c)), nil
	}
	return AdvanceSum(c.Text, w.metric.Weight)
}

func (w *wrapper) width(from, to int) (int32, error) {
	span := w.prefix[to] - w.prefix[from]
	if w.metric.Profile == ProfileCell {
		return checkedI32(span)
	}
	product, err := mul64(span, int64(w.metric.SizePx)*64)
	if err != nil {
		return 0, err
	}
	width, err := checkedI32(CeilDiv(product, w.upem))
	if err != nil {
		return 0, err
	}
	if w.metric.FontFamily {
		return FontFamilyFactor(width)
	}
	return width, nil
}

func (w *wrapper) run(target int32) ([]Line, error) {
	n := len(w.clusters)
	opts := w.opportunities()
	lines := make([]Line, 0, n)
	for start := 0; start < n; {
		end, err := w.lineEnd(start, target)
		if err != nil {
			return nil, err
		}
		if end == n {
			line, err := w.finalLine(start)
			if err != nil {
				return nil, err
			}
			return append(lines, line), nil
		}
		line, next, err := w.breakLine(opts, start, end)
		if err != nil {
			return nil, err
		}
		lines = append(lines, line)
		start = next
	}
	return lines, nil
}

func (w *wrapper) lineEnd(start int, target int32) (int, error) {
	n := len(w.clusters)
	fits, err := w.fits(start, start+1, target)
	if err != nil {
		return 0, err
	}
	if !fits {
		return start + 1, nil
	}
	lo, hi := start+1, n
	for lo < hi {
		mid := (lo + hi + 1) / 2
		fits, err := w.fits(start, mid, target)
		if err != nil {
			return 0, err
		}
		if fits {
			lo = mid
		} else {
			hi = mid - 1
		}
	}
	return lo, nil
}

func (w *wrapper) fits(start, end int, target int32) (bool, error) {
	width, err := w.width(start, end)
	if err != nil {
		return false, err
	}
	return width <= target, nil
}

func (w *wrapper) finalLine(start int) (Line, error) {
	end := len(w.clusters)
	runStart := end
	for runStart > start && w.isSpace(runStart-1) {
		runStart--
	}
	if runStart > start {
		return w.line(start, runStart, runStart, end)
	}
	return w.line(start, end, end, end)
}

func (w *wrapper) breakLine(opts []opportunity, start, end int) (Line, int, error) {
	opt, ok := lastOpportunity(opts, start, end)
	if !ok {
		line, err := w.line(start, end, end, end)
		return line, end, err
	}
	line, err := w.line(start, opt.at, opt.at, opt.next)
	return line, opt.next, err
}

func lastOpportunity(opts []opportunity, start, end int) (opportunity, bool) {
	index := sort.Search(len(opts), func(i int) bool { return opts[i].at > end })
	for index--; index >= 0; index-- {
		if opts[index].at > start {
			return opts[index], true
		}
	}
	return opportunity{}, false
}

func (w *wrapper) line(textFrom, textTo, sepFrom, sepTo int) (Line, error) {
	text := w.slice(textFrom, textTo)
	width, err := w.metric.TextWidth(text)
	if err != nil {
		return Line{}, err
	}
	return Line{Text: text, Separator: w.slice(sepFrom, sepTo), Width: width}, nil
}

func (w *wrapper) slice(from, to int) string {
	if from >= to {
		return ""
	}
	var b strings.Builder
	for _, c := range w.clusters[from:to] {
		b.WriteString(c.Text)
	}
	return b.String()
}

func (w *wrapper) isSpace(i int) bool {
	return i >= 0 && i < len(w.clusters) && w.clusters[i].Text == " "
}

func (w *wrapper) opportunities() []opportunity {
	opts := make([]opportunity, 0, len(w.clusters))
	for i := 1; i < len(w.clusters); i++ {
		switch {
		case w.isSpace(i) && !w.isSpace(i-1):
			opts = w.appendSpaceRun(opts, i)
		case !w.isSpace(i):
			if opt, ok := w.boundaryOpportunity(i); ok {
				opts = append(opts, opt)
			}
		}
	}
	return opts
}

func (w *wrapper) appendSpaceRun(opts []opportunity, start int) []opportunity {
	end := start
	for end < len(w.clusters) && w.isSpace(end) {
		end++
	}
	if end == len(w.clusters) {
		return opts
	}
	return append(opts, opportunity{at: start, next: end, separator: w.slice(start, end)})
}

func (w *wrapper) boundaryOpportunity(at int) (opportunity, bool) {
	previous, next := LastScalar(w.clusters[at-1]), FirstScalar(w.clusters[at])
	hyphen := previous == '-' && isASCIIAlnum(next)
	ideograph := isIdeographic(previous) && isIdeographic(next)
	if !hyphen && !ideograph {
		return opportunity{}, false
	}
	return opportunity{at: at, next: at}, true
}

func isASCIIAlnum(cp rune) bool {
	switch {
	case cp >= '0' && cp <= '9':
		return true
	case cp >= 'a' && cp <= 'z':
		return true
	case cp >= 'A' && cp <= 'Z':
		return true
	default:
		return false
	}
}
