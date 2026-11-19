package treeview

import (
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

const (
	codeEmptyBox = "treeview/empty-box-node"
	codeMixed    = "treeview/mixed-indentation"
	msgEmptyBox  = "expected a filename or directory name after the box-drawing prefix"
	msgMixed     = "unexpected indentation without box-drawing characters"
	indentUnit   = 4
	defaultWidth = 4
)

type lineSpan struct {
	start, end int
}

func isBoxRune(r rune) bool { return strings.ContainsRune("─━│┃└┗├┣", r) }

func isBranchRune(r rune) bool { return strings.ContainsRune("└┗├┣", r) }

func isDashRune(r rune) bool { return r == '─' || r == '━' }

func isDecorationRune(r rune) bool { return jsSpace(r) || r == '│' || r == '┃' }

func isBoxOrSpace(r rune) bool { return jsSpace(r) || isBoxRune(r) }

func allRunes(s string, keep func(rune) bool) bool {
	return s != "" && strings.IndexFunc(s, func(r rune) bool { return !keep(r) }) < 0
}

func commentLine(line string) bool {
	return strings.HasPrefix(strings.TrimLeftFunc(line, jsSpace), "%%")
}

func metadataLine(line string) bool {
	rest := strings.TrimLeftFunc(line, jsSpace)
	if after, ok := strings.CutPrefix(rest, "title"); ok {
		return after != "" && blank(after[0])
	}
	if after, ok := strings.CutPrefix(rest, "accTitle"); ok {
		return strings.HasPrefix(strings.TrimLeft(after, " \t"), ":")
	}
	if after, ok := strings.CutPrefix(rest, "accDescr"); ok {
		after = strings.TrimLeft(after, " \t")
		return strings.HasPrefix(after, ":") || strings.HasPrefix(after, "{")
	}
	return false
}

func splitLines(text string) []lineSpan {
	var lines []lineSpan
	start := 0
	for {
		end := strings.IndexByte(text[start:], '\n')
		if end < 0 {
			return append(lines, lineSpan{start, len(text)})
		}
		lines = append(lines, lineSpan{start, start + end})
		start += end + 1
	}
}

type view struct {
	text string
	orig []int
}

func (v view) line(l lineSpan) string { return v.text[l.start:l.end] }

func expandTabs(line string) string { return strings.ReplaceAll(line, "\t", "    ") }

func (v view) normalized(l lineSpan) ([]byte, []int) {
	norm := make([]byte, 0, l.end-l.start)
	origin := make([]int, 0, l.end-l.start)
	for i := l.start; i < l.end; i++ {
		repeat := 1
		if v.text[i] == '\t' {
			repeat = indentUnit
		}
		for range repeat {
			if v.text[i] == '\t' {
				norm = append(norm, ' ')
			} else {
				norm = append(norm, v.text[i])
			}
			origin = append(origin, v.orig[i])
		}
	}
	return norm, origin
}

func headerLine(v view, lines []lineSpan) int {
	for i, l := range lines {
		if trimJS(v.line(l)) == headerWord {
			return i
		}
	}
	return -1
}

func branchColumn(line string) (index, column int) {
	index = strings.IndexFunc(line, isBranchRune)
	if index < 0 {
		return -1, 0
	}
	return index, utf16Len(line[:index])
}

func contentLines(v view, lines []lineSpan) []string {
	var out []string
	for _, l := range lines {
		raw := v.line(l)
		if trimJS(raw) == "" || commentLine(raw) || metadataLine(raw) || allRunes(raw, isDecorationRune) {
			continue
		}
		out = append(out, expandTabs(raw))
	}
	return out
}

func segmentWidth(content []string) int {
	for _, line := range content {
		if _, column := branchColumn(line); column > 0 {
			return column
		}
	}
	return defaultWidth
}

type boxWriter struct {
	v      view
	end    int
	out    []byte
	origin []int
	emit   bool
	prevNL int
	diags  []diag.Diagnostic
}

func (w *boxWriter) lineBreakAfter(l lineSpan) int {
	if l.end < len(w.v.orig) {
		return w.v.orig[l.end]
	}
	return w.end
}

func (w *boxWriter) separator(l lineSpan) {
	if w.emit {
		w.out = append(w.out, '\n')
		w.origin = append(w.origin, w.prevNL)
	}
	w.emit = true
	w.prevNL = w.lineBreakAfter(l)
}

func (w *boxWriter) raw(l lineSpan) {
	w.separator(l)
	w.out = append(w.out, w.v.text[l.start:l.end]...)
	w.origin = append(w.origin, w.v.orig[l.start:l.end]...)
}

func (w *boxWriter) diagnostic(code, message string, span source.Span) {
	w.diags = append(w.diags, Diagnostic(code, message, span))
}

func (w *boxWriter) finish(i int) int {
	if i <= 0 || i > len(w.v.orig) {
		return w.end
	}
	return w.v.orig[i-1] + 1
}

func contentStart(norm []byte, index int) int {
	_, size := utf8.DecodeRune(norm[index:])
	pos := index + size
	for pos < len(norm) {
		r, n := utf8.DecodeRune(norm[pos:])
		if !isDashRune(r) {
			break
		}
		pos += n
	}
	for pos < len(norm) && norm[pos] == ' ' {
		pos++
	}
	return pos
}

func (w *boxWriter) indent(depth, first, last int) {
	for range depth*indentUnit - 1 {
		w.out = append(w.out, ' ')
		w.origin = append(w.origin, first)
	}
	w.out = append(w.out, ' ')
	w.origin = append(w.origin, last-1)
}

type branchAt struct {
	index, column, content int
}

func (w *boxWriter) branch(l lineSpan, norm []byte, origin []int, at branchAt, segment int) {
	content := trimEndJS(string(norm[at.content:]))
	if content == "" {
		w.diagnostic(codeEmptyBox, msgEmptyBox, source.Span{Start: origin[at.index], End: w.finish(l.end)})
		return
	}
	w.separator(l)
	w.indent((2*at.column+segment)/(2*segment)+1, origin[0], origin[at.content])
	w.out = append(w.out, content...)
	w.origin = append(w.origin, origin[at.content:at.content+len(content)]...)
}

func (w *boxWriter) body(l lineSpan, segment int) {
	raw := w.v.line(l)
	if trimJS(raw) == "" || commentLine(raw) || metadataLine(raw) {
		w.raw(l)
		return
	}
	if allRunes(raw, isDecorationRune) {
		return
	}
	norm, origin := w.v.normalized(l)
	text := string(norm)
	if index, column := branchColumn(text); index >= 0 {
		w.branch(l, norm, origin, branchAt{index, column, contentStart(norm, index)}, segment)
		return
	}
	w.plain(l, text, origin)
}

func (w *boxWriter) plain(l lineSpan, text string, origin []int) {
	switch {
	case allRunes(text, isBoxOrSpace):
	case strings.IndexFunc(text, isBoxRune) >= 0:
		w.raw(l)
	case jsSpace(firstRune(text)):
		lead := len(text) - len(strings.TrimLeftFunc(text, jsSpace))
		w.diagnostic(codeMixed, msgMixed, source.Span{Start: origin[0], End: origin[lead-1] + 1})
	default:
		w.raw(l)
	}
}

func firstRune(s string) rune {
	r, _ := utf8.DecodeRuneInString(s)
	return r
}

func convertBox(text string, orig []int, end int) (string, []int, []diag.Diagnostic) {
	v := view{text: text, orig: orig}
	lines := splitLines(text)
	keyword := headerLine(v, lines)
	if keyword < 0 {
		return text, orig, nil
	}
	content := contentLines(v, lines[keyword+1:])
	if !anyBox(content) {
		return text, orig, nil
	}
	segment := segmentWidth(content)
	w := &boxWriter{v: v, end: end}
	for _, l := range lines[:keyword+1] {
		w.raw(l)
	}
	for _, l := range lines[keyword+1:] {
		w.body(l, segment)
	}
	return string(w.out), w.origin, w.diags
}

func anyBox(content []string) bool {
	for _, line := range content {
		if strings.IndexFunc(line, isBoxRune) >= 0 {
			return true
		}
	}
	return false
}
