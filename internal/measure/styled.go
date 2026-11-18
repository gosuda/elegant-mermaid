package measure

import (
	"math"
	"sort"
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	emath "github.com/gosuda/elegant-mermaid/internal/math"
)

type StyledRun struct {
	Text   string
	Bold   bool
	Italic bool
	Width  int32
	Math   *emath.Box
}

type StyledLine struct {
	Runs  []StyledRun
	Text  string
	Width int32
}

type styledToken struct {
	text         string
	bold, italic bool
	start, end   int
	formula      string
	isMath       bool
	box          *emath.Box
}

func styledEscape(s string, at int) bool {
	if at+1 >= len(s) || s[at] != '\\' {
		return false
	}
	c := s[at+1]
	return c >= 33 && c <= 126 && !isASCIIAlnum(rune(c))
}

func styledBreak(s string, at int) int {
	for _, tag := range []string{"<br>", "<br/>", "<br />"} {
		if at+len(tag) <= len(s) && strings.EqualFold(s[at:at+len(tag)], tag) {
			return len(tag)
		}
	}
	return 0
}

func styledIntraword(s string, at int) bool {
	before, _ := utf8.DecodeLastRuneInString(s[:at])
	after, _ := utf8.DecodeRuneInString(s[at+1:])
	return styledAlphanumeric(before) && styledAlphanumeric(after)
}

func styledAlphanumeric(cp rune) bool {
	if cp < utf8.RuneSelf {
		return isASCIIAlnum(cp)
	}
	index := sort.Search(len(gen.Alphanumeric), func(i int) bool {
		return gen.Alphanumeric[i].Hi >= uint32(cp)
	})
	return index < len(gen.Alphanumeric) && gen.Alphanumeric[index].Lo <= uint32(cp)
}

func styledDelimiter(s string, at int) string {
	if strings.HasPrefix(s[at:], "**") {
		return "**"
	}
	if s[at] == '*' {
		return "*"
	}
	if s[at] == '_' && !styledIntraword(s, at) {
		return "_"
	}
	return ""
}

func styledMathEnd(s string, at int) int {
	for at < len(s) {
		if styledEscape(s, at) {
			at += 2
		} else if strings.HasPrefix(s[at:], "$$") {
			return at
		} else {
			_, n := utf8.DecodeRuneInString(s[at:])
			at += n
		}
	}
	return -1
}

func styledOpaqueEnd(s string, at int) int {
	if styledEscape(s, at) {
		return at + 2
	}
	if !strings.HasPrefix(s[at:], "$$") {
		return at
	}
	close := styledMathEnd(s, at+2)
	if close < 0 {
		return at + 2
	}
	return close + 2
}

func styledEmphasisBoundary(s string, at int) bool {
	return s[at] == '\r' || s[at] == '\n' || styledBreak(s, at) != 0
}

func styledEmphasisClose(s string, at int, delimiter string) bool {
	return strings.HasPrefix(s[at:], delimiter) && (delimiter != "_" || !styledIntraword(s, at))
}

func styledEmphasisEnd(s string, at int, delimiter string) int {
	for at < len(s) {
		if styledEmphasisBoundary(s, at) {
			return -1
		}
		if next := styledOpaqueEnd(s, at); next != at {
			at = next
			continue
		}
		if styledEmphasisClose(s, at, delimiter) {
			return at
		}
		_, size := utf8.DecodeRuneInString(s[at:])
		at += size
	}
	return -1
}

type styledScanner struct {
	regions [][]styledToken
}

func (p *styledScanner) appendText(text string, style styledToken) {
	if text == "" {
		return
	}
	style.text = text
	i := len(p.regions) - 1
	p.regions[i] = append(p.regions[i], style)
}

type styledConstruct struct {
	end, start, stop          int
	style                     styledToken
	breakLine, emphasis, math bool
}

func styledConstructAt(text string, at int) styledConstruct {
	if styledEscape(text, at) {
		return styledConstruct{end: at + 2, start: at + 1, stop: at + 2}
	}
	if size := styledBreak(text, at); size != 0 {
		return styledConstruct{end: at + size, breakLine: true}
	}
	if !strings.HasPrefix(text[at:], "$$") {
		return styledConstruct{}
	}
	close := styledMathEnd(text, at+2)
	if close < 0 {
		return styledConstruct{}
	}
	return styledConstruct{end: close + 2, start: at, stop: close + 2, math: true}
}

func styledEmphasisAt(text string, at int) styledConstruct {
	delimiter := styledDelimiter(text, at)
	if delimiter == "" {
		return styledConstruct{}
	}
	close := styledEmphasisEnd(text, at+len(delimiter), delimiter)
	if close < 0 {
		return styledConstruct{}
	}
	return styledConstruct{
		end: close + len(delimiter), start: at + len(delimiter), stop: close,
		style:    styledToken{bold: delimiter == "**", italic: delimiter != "**"},
		emphasis: true,
	}
}

func (p *styledScanner) emit(text string, construct styledConstruct) {
	if construct.breakLine {
		p.regions = append(p.regions, nil)
		return
	}
	if construct.emphasis {
		p.scan(text[construct.start:construct.stop], construct.style)
		return
	}
	if construct.math {
		p.appendMath(text[construct.start:construct.stop])
		return
	}
	p.appendText(text[construct.start:construct.stop], construct.style)
}

func styledNext(text string, at int, style styledToken) styledConstruct {
	construct := styledConstructAt(text, at)
	if construct.end != 0 {
		if styledEscape(text, at) {
			construct.style = style
		}
		return construct
	}
	if style.bold || style.italic {
		return construct
	}
	return styledEmphasisAt(text, at)
}

func styledStep(text string, at int, style styledToken) int {
	delimiter := styledDelimiter(text, at)
	if delimiter != "" && !style.bold && !style.italic {
		return len(delimiter)
	}
	_, size := utf8.DecodeRuneInString(text[at:])
	return size
}

func (p *styledScanner) scan(text string, style styledToken) {
	plain := 0
	for at := 0; at < len(text); {
		construct := styledNext(text, at, style)
		if construct.end == 0 {
			at += styledStep(text, at, style)
			continue
		}
		p.appendText(text[plain:at], style)
		p.emit(text, construct)
		at, plain = construct.end, construct.end
	}
	p.appendText(text[plain:], style)
}

func styledRegions(s string) [][]styledToken {
	p := styledScanner{regions: [][]styledToken{nil}}
	p.scan(s, styledToken{})
	return p.regions
}

func styledMetric(m Metric, token styledToken) Metric {
	if token.italic {
		m.Weight = WeightRegular
	} else if token.bold {
		m.Weight = WeightSemiBold
	}
	return m
}

func styledAdd(a, b int64) (int64, error) {
	if b > math.MaxInt64-a {
		return 0, geom.ErrOverflow
	}
	return a + b, nil
}

func styledGCD(a, b int64) int64 {
	for b != 0 {
		a, b = b, a%b
	}
	return a
}

func styledAdvance(text string, token styledToken, m Metric, denominator int64) (int64, error) {
	weight := styledMetric(m, token).Weight
	advance, err := AdvanceSum(text, weight)
	if err != nil {
		return 0, err
	}
	upem, err := Upem(weight)
	if err != nil {
		return 0, err
	}
	return mul64(advance, denominator/int64(upem))
}

type styledMeasurement struct {
	tokens      []styledToken
	text        string
	metric      Metric
	denominator int64
	prefix      []int64
	mathPrefix  []int64
}

func styledDenominator(m Metric) (int64, error) {
	if m.Profile == ProfileCell {
		return 1, nil
	}
	if m.SizePx < 0 {
		return 0, geom.ErrDomain
	}
	if _, err := Upem(m.Weight); err != nil {
		return 0, err
	}
	denominator := int64(1)
	for _, weight := range []Weight{WeightRegular, WeightSemiBold} {
		upem, err := Upem(weight)
		if err != nil {
			return 0, err
		}
		denominator = denominator / styledGCD(denominator, int64(upem)) * int64(upem)
	}
	return denominator, nil
}

func renderStyledTokens(tokens []styledToken) string {
	var rendered strings.Builder
	for i := range tokens {
		tokens[i].start = rendered.Len()
		rendered.WriteString(tokens[i].rendered())
		tokens[i].end = rendered.Len()
	}
	return rendered.String()
}

func (m *styledMeasurement) clusterUnits(cluster Cluster, at, first int) (int64, int64, error) {
	if m.metric.Profile == ProfileCell {
		return int64(ClusterWidth(cluster)), 0, nil
	}
	stop := at + len(cluster.Text)
	var units, formulas int64
	for j := first; j < len(m.tokens) && m.tokens[j].start < stop; j++ {
		token := m.tokens[j]
		lo, hi := max(at, token.start), min(stop, token.end)
		part, err := styledAdvance(token.advanceText(m.text[lo:hi]), token, m.metric, m.denominator)
		if err != nil {
			return 0, 0, err
		}
		if units, err = styledAdd(units, part); err != nil {
			return 0, 0, err
		}
		if formulas, err = styledAdd(formulas, token.formulaWidth()); err != nil {
			return 0, 0, err
		}
	}
	return units, formulas, nil
}

func (m *styledMeasurement) advanceToken(first, at int) int {
	for first < len(m.tokens) && m.tokens[first].end <= at {
		first++
	}
	return first
}

func (m *styledMeasurement) buildPrefix(clusters []Cluster) error {
	m.prefix = make([]int64, len(clusters)+1)
	m.mathPrefix = make([]int64, len(clusters)+1)
	at, first := 0, 0
	for i, cluster := range clusters {
		first = m.advanceToken(first, at)
		units, formulas, err := m.clusterUnits(cluster, at, first)
		if err != nil {
			return err
		}
		if m.prefix[i+1], err = styledAdd(m.prefix[i], units); err != nil {
			return err
		}
		if m.mathPrefix[i+1], err = styledAdd(m.mathPrefix[i], formulas); err != nil {
			return err
		}
		at += len(cluster.Text)
	}
	return nil
}

func (m *styledMeasurement) width(from, to int) (int32, error) {
	units := m.prefix[to] - m.prefix[from]
	if m.metric.Profile == ProfileCell {
		return checkedI32(units)
	}
	product, err := mul64(units, int64(m.metric.SizePx)*64)
	if err != nil {
		return 0, err
	}
	value := product / m.denominator
	if product%m.denominator != 0 {
		value++
	}
	value, err = styledAdd(value, m.mathPrefix[to]-m.mathPrefix[from])
	if err != nil {
		return 0, err
	}
	result, err := checkedI32(value)
	if err != nil {
		return 0, err
	}
	if m.metric.FontFamily {
		return FontFamilyFactor(result)
	}
	return result, nil
}

func (m *styledMeasurement) lineRuns(first, at, stop int) ([]StyledRun, error) {
	var runs []StyledRun
	for j := first; j < len(m.tokens) && m.tokens[j].start < stop; j++ {
		token := m.tokens[j]
		lo, hi := max(at, token.start)-token.start, min(stop, token.end)-token.start
		run, err := token.run(m.metric, lo, hi)
		if err != nil {
			return nil, err
		}
		runs = append(runs, run)
	}
	return runs, nil
}

func (m *styledMeasurement) styledLines(lines []Line) ([]StyledLine, error) {
	result := make([]StyledLine, 0, len(lines))
	at, first := 0, 0
	for _, line := range lines {
		stop := at + len(line.Text)
		first = m.advanceToken(first, at)
		runs, err := m.lineRuns(first, at, stop)
		if err != nil {
			return nil, err
		}
		result = append(result, StyledLine{Text: runsText(runs), Width: line.Width, Runs: runs})
		at = stop + len(line.Separator)
	}
	return result, nil
}

func styledRegion(tokens []styledToken, target int32, metric Metric) ([]StyledLine, error) {
	denominator, err := styledDenominator(metric)
	if err != nil {
		return nil, err
	}
	if err := layoutFormulas(tokens, metric); err != nil {
		return nil, err
	}
	m := styledMeasurement{tokens: tokens, text: renderStyledTokens(tokens), metric: metric, denominator: denominator}
	clusters := Segment(m.text)
	if err := m.buildPrefix(clusters); err != nil {
		return nil, err
	}
	w := wrapper{clusters: clusters, metric: metric, styledWidth: m.width}
	lines, err := w.run(target)
	if err != nil {
		return nil, err
	}
	return m.styledLines(lines)
}

func normalizeCellTokens(tokens []styledToken) {
	for i := range tokens {
		tokens[i].text = strings.Map(func(r rune) rune {
			if r <= '\x1f' || r >= '\x7f' && r <= '\u009f' {
				return '\ufffd'
			}
			return r
		}, tokens[i].text)
	}
}

func StyledLines(text string, target int32, metric Metric) ([]StyledLine, error) {
	regions := styledRegions(text)
	var result []StyledLine
	for i, tokens := range regions {
		if len(tokens) == 0 {
			if i < len(regions)-1 {
				result = append(result, StyledLine{})
			}
			continue
		}
		if metric.Profile == ProfileCell {
			normalizeCellTokens(tokens)
		}
		lines, err := styledRegion(tokens, target, metric)
		if err != nil {
			return nil, err
		}
		result = append(result, lines...)
	}
	return result, nil
}

func StyledWidth(text string, metric Metric) (int32, error) {
	lines, err := StyledLines(text, math.MaxInt32, metric)
	if err != nil {
		return 0, err
	}
	var width int32
	for _, line := range lines {
		width = max(width, line.Width)
	}
	return width, nil
}
