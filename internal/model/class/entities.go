package class

import (
	"regexp"
	"slices"
	"strconv"
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/gen"
)

var entityPattern = regexp.MustCompile(`#[A-Za-z0-9_]+;`)

func decodeEntities(text string) string {
	return entityPattern.ReplaceAllStringFunc(text, entityValue)
}

func entityValue(text string) string {
	name := text[1 : len(text)-1]
	if value, err := strconv.ParseUint(name, 10, 32); err == nil {
		cp := rune(value)
		if cp != 0 && utf8.ValidRune(cp) {
			return string(cp)
		}
		return text
	}
	key := "&" + name + ";"
	i, found := slices.BinarySearchFunc(gen.Entities, key, func(row gen.Entity, key string) int { return strings.Compare(row.Name, key) })
	if !found {
		return text
	}
	var out strings.Builder
	for _, cp := range gen.Entities[i].CPS {
		out.WriteRune(rune(cp))
	}
	return out.String()
}
