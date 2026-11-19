package lint

import (
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/model/venn"
)

func vennRules(m *venn.Model, row Row) []diag.Diagnostic {
	var out []diag.Diagnostic
	sets := map[string]bool{}
	unions := map[string]bool{}
	for _, declaration := range m.Declarations {
		ids := declaration.RejectedIDs
		if declaration.SubsetIndex >= 0 {
			ids = m.Subsets[declaration.SubsetIndex].Sets
		}
		span := declaration.Span
		hit := vennDeclarationMatch(ids, declaration.Union, sets, unions, row.Code)
		if row.Code == "venn/non-positive-size" && declaration.HasSize {
			hit, span = declaration.NonPositive, declaration.SizeSpan
		}
		if hit {
			out = append(out, diagnostic(row, row.Summary, span))
		}
	}
	if row.Code == "venn/single-set" && len(sets) == 1 {
		out = append(out, diagnostic(row, row.Summary, m.HeaderSpan))
	}
	return out
}

func vennDeclarationMatch(ids []string, union bool, sets, unions map[string]bool, code string) bool {
	if !union {
		hit := code == "venn/duplicate-set" && sets[ids[0]]
		sets[ids[0]] = true
		return hit
	}
	key := strings.Join(ids, "\x00")
	hit := code == "venn/duplicate-union" && unions[key]
	unions[key] = true
	return hit || code == "venn/self-union" && vennRepeatedMember(ids)
}

func vennRepeatedMember(ids []string) bool {
	for i := 1; i < len(ids); i++ {
		if ids[i] == ids[i-1] {
			return true
		}
	}
	return false
}
