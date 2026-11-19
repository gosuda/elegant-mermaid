package lint

import (
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
)

const (
	betaSuffix      = "-beta"
	titleWord       = "accTitle"
	descrWord       = "accDescr"
	kindPlaceholder = "KIND"
)

func commonRules() map[string]ruleFunc {
	return map[string]ruleFunc{
		"common/no-experimental":   common(noExperimental),
		"common/acc-title-missing": common(accTitleMissing),
		"common/acc-descr-missing": common(accDescrMissing),
	}
}

func common(rule func(b *Block, row Row) []diag.Diagnostic) ruleFunc {
	return func(a *Analysis, row Row) []diag.Diagnostic {
		if !a.Block.Found {
			return nil
		}
		return rule(&a.Block, row)
	}
}

func noExperimental(b *Block, row Row) []diag.Diagnostic {
	if !hasSuffixFold(b.Token, betaSuffix) {
		return nil
	}
	message := strings.Replace(row.Summary, kindPlaceholder, b.Token, 1)
	return []diag.Diagnostic{diagnostic(row, message, b.Header)}
}

func accTitleMissing(b *Block, row Row) []diag.Diagnostic {
	if declaresAccessibility(b, titleWord, ':') {
		return nil
	}
	return []diag.Diagnostic{diagnostic(row, row.Summary, b.Header)}
}

func accDescrMissing(b *Block, row Row) []diag.Diagnostic {
	if declaresAccessibility(b, descrWord, ':') || declaresAccessibility(b, descrWord, '{') {
		return nil
	}
	return []diag.Diagnostic{diagnostic(row, row.Summary, b.Header)}
}

func declaresAccessibility(b *Block, word string, delimiter byte) bool {
	for pos := b.Header.End; pos < len(b.Source); {
		ln := lineAt(b.Source, pos)
		pos = ln.next
		start := skipBlanks(b.Source, ln.start, ln.end)
		if containsOffset(b.Removed, start) || !hasPrefixAt(b.Source, start, ln.end, word) {
			continue
		}
		at := skipBlanks(b.Source, start+len(word), ln.end)
		if at < ln.end && b.Source[at] == delimiter {
			return true
		}
	}
	return false
}
