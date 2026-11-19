package syntax

import (
	"strconv"
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/gen"
)

func DecodeEntities(text string) string {
	var out strings.Builder
	for i := 0; i < len(text); {
		if text[i] != '#' {
			out.WriteByte(text[i])
			i++
			continue
		}
		decoded, size := entityAt(text[i+1:])
		if size == 0 {
			out.WriteByte(text[i])
			i++
			continue
		}
		out.WriteString(decoded)
		i += 1 + size
	}
	return out.String()
}

func entityAt(tail string) (string, int) {
	name, _, found := strings.Cut(tail, ";")
	if !found || name == "" || !validEntityName(name) {
		return "", 0
	}
	if code, err := strconv.ParseUint(name, 10, 32); err == nil {
		if r := rune(code); r != 0 && utf8.ValidRune(r) {
			return string(r), len(name) + 1
		}
	}
	text, ok := lookupEntity("&" + name + ";")
	if !ok {
		return "", 0
	}
	return text, len(name) + 1
}

func validEntityName(name string) bool {
	for i := range len(name) {
		b := name[i]
		if b >= 'a' && b <= 'z' || b >= 'A' && b <= 'Z' || b >= '0' && b <= '9' || b == '_' {
			continue
		}
		return false
	}
	return true
}

func lookupEntity(key string) (string, bool) {
	row, found := entityRow(key)
	if !found {
		return "", false
	}
	var out strings.Builder
	for _, cp := range row.CPS {
		out.WriteRune(rune(cp))
	}
	return out.String(), true
}

func entityRow(key string) (gen.Entity, bool) {
	lo, hi := 0, len(gen.Entities)
	for lo < hi {
		mid := int(uint(lo+hi) >> 1)
		switch strings.Compare(gen.Entities[mid].Name, key) {
		case 0:
			return gen.Entities[mid], true
		case -1:
			lo = mid + 1
		default:
			hi = mid
		}
	}
	return gen.Entity{}, false
}
