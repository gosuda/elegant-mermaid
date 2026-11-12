package flowchart

import (
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

func attachFixes(src []byte, diagnostics []diag.Diagnostic) {
	for i := range diagnostics {
		d := &diagnostics[i]
		d.Fixes = nil
		if fix, ok := diagnosticFix(src, *d); ok {
			d.Fixes = []diag.Fix{fix}
		}
	}
}

func singleFix(title string, safety diag.FixSafety, span source.Span, text string) (diag.Fix, bool) {
	return diag.Fix{Title: title, Safety: safety, Edits: []diag.Edit{{Span: span, NewText: text}}}, true
}

func diagnosticFix(src []byte, d diag.Diagnostic) (diag.Fix, bool) {
	switch d.Code {
	case codeArrowInvalid:
		return singleFix("Replace -> with -->", diag.FixSafe, d.Span, "-->")
	case codeLinkMissing:
		return singleFix("Insert --> between the two nodes", diag.FixUnsafe, source.Span{Start: d.Span.Start, End: d.Span.Start}, "--> ")
	case codeEndWithoutSubgraph, codeMetaUnsupported:
		return lineRemovalFix(src, d)
	case codeUnclosedNodeBracket, codeNodeMixedBrackets, codeNodeEmpty:
		return bracketFix(src, d)
	default:
		return textFix(src, d)
	}
}

func lineRemovalFix(src []byte, d diag.Diagnostic) (diag.Fix, bool) {
	start, end := lineBounds(src, d.Span.Start)
	if end < len(src) {
		if src[end] == '\r' && end+1 < len(src) && src[end+1] == '\n' {
			end++
		}
		end++
	}
	title := "Remove the unsupported meta line"
	if d.Code == codeEndWithoutSubgraph {
		title = "Remove the stray end line"
	}
	return singleFix(title, diag.FixUnsafe, source.Span{Start: start, End: end}, "")
}

func textFix(src []byte, d diag.Diagnostic) (diag.Fix, bool) {
	switch d.Code {
	case codeLabelEscapedQuote, codeLabelDoubleInSingle:
		return singleFix("Replace the quote with &quot;", diag.FixSafe, d.Span, "&quot;")
	case "flowchart/label-backtick":
		return singleFix("Remove the backtick", diag.FixSafe, d.Span, "")
	case codeDirKeywordInvalid:
		return singleFix("Replace the keyword with direction", diag.FixSafe, d.Span, "direction")
	case "flowchart/dir-missing":
		return singleFix("Insert the default direction TD", diag.FixSafe, source.Span{Start: d.Span.End, End: d.Span.End}, " TD")
	case codeLinkUnsupportedMark:
		text := string(src[d.Span.Start:d.Span.End])
		text = strings.Map(func(r rune) rune {
			if r == 'x' || r == 'o' {
				return -1
			}
			return r
		}, text)
		return singleFix("Remove the unsupported one-sided marker", diag.FixUnsafe, d.Span, text)
	case codeQuoteUnclosed:
		return quoteClosingFix(src, d)
	case codeLabelQuoteInUnquoted:
		return quoteWrappingFix(src, d)
	}
	return diag.Fix{}, false
}

func lineBounds(src []byte, at int) (int, int) {
	start, end := at, at
	for start > 0 && src[start-1] != '\n' && src[start-1] != '\r' {
		start--
	}
	for end < len(src) && src[end] != '\n' && src[end] != '\r' {
		end++
	}
	return start, end
}

func bracketOpening(src []byte, at int) (int, string, string, bool) {
	start, end := lineBounds(src, at)
	for i := start; i <= at && i < end; i++ {
		if src[i] == '>' && i > 0 && strings.ContainsRune("-=.", rune(src[i-1])) {
			continue
		}
		open, close, ok := bracketPair(string(src[i:]))
		if !ok {
			continue
		}
		offset := strings.Index(string(src[i+len(open):end]), close)
		finish := i + len(open) + offset + len(close)
		if offset >= 0 && finish <= at {
			i = finish - 1
			continue
		}
		return i, open, close, true
	}
	return 0, "", "", false
}

func bracketPair(text string) (string, string, bool) {
	for _, pair := range [][2]string{{"(((", ")))"}, {"((", "))"}, {"([", "])"}, {"[[", "]]"}, {"[(", ")]"}, {"{{", "}}"}, {"[/", "/]"}, {"[\\", "\\]"}, {"(-", "-)"}, {"[", "]"}, {"(", ")"}, {"{", "}"}, {">", "]"}, {"|", "|"}} {
		if strings.HasPrefix(text, pair[0]) {
			return pair[0], pair[1], true
		}
	}
	return "", "", false
}

func bracketFix(src []byte, d diag.Diagnostic) (diag.Fix, bool) {
	at, open, close, ok := bracketOpening(src, d.Span.Start)
	if !ok {
		return diag.Fix{}, false
	}
	switch d.Code {
	case codeUnclosedNodeBracket:
		return singleFix("Add the closing bracket", diag.FixUnsafe, source.Span{Start: d.Span.End, End: d.Span.End}, close)
	case codeNodeMixedBrackets:
		return singleFix("Close with the matching bracket", diag.FixSafe, d.Span, close)
	case codeNodeEmpty:
		_, end := lineBounds(src, at)
		if offset := strings.Index(string(src[at+len(open):end]), close); offset >= 0 {
			return singleFix("Remove the empty bracket pair", diag.FixSafe, source.Span{Start: at, End: at + len(open) + offset + len(close)}, "")
		}
	}
	return diag.Fix{}, false
}

func quoteClosingFix(src []byte, d diag.Diagnostic) (diag.Fix, bool) {
	_, end := lineBounds(src, d.Span.Start)
	for i := d.Span.Start + 1; i < end; i++ {
		if strings.ContainsRune("])}", rune(src[i])) {
			end = i
			break
		}
	}
	return singleFix("Insert the closing quote", diag.FixUnsafe, source.Span{Start: end, End: end}, "\"")
}

func quoteWrappingFix(src []byte, d diag.Diagnostic) (diag.Fix, bool) {
	at, open, close, ok := bracketOpening(src, d.Span.Start)
	if !ok {
		return diag.Fix{}, false
	}
	start := at + len(open)
	_, end := lineBounds(src, start)
	if offset := strings.Index(string(src[start:end]), close); offset >= 0 {
		end = start + offset
		text := "\"" + strings.ReplaceAll(string(src[start:end]), "\"", "&quot;") + "\""
		return singleFix("Wrap the label in quotes", diag.FixSafe, source.Span{Start: start, End: end}, text)
	}
	return diag.Fix{}, false
}
