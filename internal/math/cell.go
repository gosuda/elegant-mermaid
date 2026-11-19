package math

import (
	"sort"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/gen"
)

type Charset uint8

const (
	CharsetUnicode Charset = iota
	CharsetASCII
)

func Linear(expression *Expr, charset Charset) string {
	var out strings.Builder
	writeLinear(&out, expression, charset)
	return out.String()
}

func writeLinear(out *strings.Builder, e *Expr, charset Charset) {
	switch e.Kind {
	case KindRow:
		for _, child := range e.Children {
			writeLinear(out, child, charset)
		}
	case KindGroup, KindStyled, KindText:
		writeLinear(out, e.Body, charset)
	case KindFraction:
		writeFraction(out, e, charset)
	case KindScripts:
		writeScripts(out, e, charset)
	case KindRadical:
		writeRadical(out, e, charset)
	case KindDelimited:
		writeDelimited(out, e, charset)
	default:
		writeAtom(out, e, charset)
	}
}

func writeAtom(out *strings.Builder, e *Expr, charset Charset) {
	switch e.Kind {
	case KindLiteral:
		out.WriteString(e.Literal)
	case KindGlyph:
		out.WriteRune(e.Char)
	case KindLimit:
		out.WriteString("lim")
	case KindSymbol:
		writeSymbol(out, e, charset)
	case KindSpace:
		writeSpace(out, e.Space)
	}
}

func writeFraction(out *strings.Builder, e *Expr, charset Charset) {
	out.WriteByte('(')
	writeLinear(out, e.Numerator, charset)
	out.WriteString(")/(")
	writeLinear(out, e.Denominator, charset)
	out.WriteByte(')')
}

func writeDelimited(out *strings.Builder, e *Expr, charset Charset) {
	writeDelimiter(out, e.Left)
	writeLinear(out, e.Body, charset)
	writeDelimiter(out, e.Right)
}

func writeSymbol(out *strings.Builder, e *Expr, charset Charset) {
	if charset == CharsetUnicode {
		out.WriteRune(e.Char)
		return
	}
	out.WriteString(asciiSymbol(e.Command, e.Class))
}

func writeSpace(out *strings.Builder, space Space) {
	switch space {
	case SpaceMedium:
		out.WriteByte(' ')
	case SpaceQuad:
		out.WriteString("  ")
	}
}

func writeScripts(out *strings.Builder, e *Expr, charset Charset) {
	writeLinear(out, e.Base, charset)
	if e.Superscript != nil {
		writeScript(out, e.Superscript, charset, '^', func(row gen.Script) uint32 { return row.Sup })
	}
	if e.Subscript != nil {
		writeScript(out, e.Subscript, charset, '_', func(row gen.Script) uint32 { return row.Sub })
	}
}

func writeScript(out *strings.Builder, content *Expr, charset Charset, marker byte, field func(gen.Script) uint32) {
	rendered := Linear(content, charset)
	if charset == CharsetUnicode {
		if converted, ok := convertScript(rendered, field); ok {
			out.WriteString(converted)
			return
		}
	}
	out.WriteByte(marker)
	out.WriteByte('(')
	out.WriteString(rendered)
	out.WriteByte(')')
}

func writeRadical(out *strings.Builder, e *Expr, charset Charset) {
	if e.Index != nil {
		writeRadicalIndex(out, Linear(e.Index, charset), charset)
	}
	if charset == CharsetUnicode {
		out.WriteString("√(")
	} else {
		out.WriteString("sqrt(")
	}
	writeLinear(out, e.Radicand, charset)
	out.WriteByte(')')
}

func writeRadicalIndex(out *strings.Builder, rendered string, charset Charset) {
	if charset == CharsetUnicode {
		if converted, ok := convertScript(rendered, func(row gen.Script) uint32 { return row.Sup }); ok {
			out.WriteString(converted)
			return
		}
	}
	out.WriteByte('[')
	out.WriteString(rendered)
	out.WriteByte(']')
}

func asciiSymbol(command string, class SymbolClass) string {
	switch class {
	case ClassGreek:
		return command
	case ClassSum:
		return "sum"
	case ClassProduct:
		return "prod"
	case ClassIntegral:
		return "int"
	case ClassOrdinary:
		return "inf"
	case ClassBinary:
		return asciiBinary(command)
	}
	return asciiRelation(command)
}

func asciiBinary(command string) string {
	switch command {
	case "pm":
		return "+-"
	case "times":
		return "x"
	case "div":
		return "/"
	}
	return "."
}

func asciiRelation(command string) string {
	switch command {
	case "le":
		return "<="
	case "ge":
		return ">="
	case "ne":
		return "!="
	case "approx":
		return "~="
	case "to":
		return "->"
	case "leftarrow":
		return "<-"
	case "Rightarrow":
		return "=>"
	case "Leftrightarrow":
		return "<=>"
	}
	return "="
}

func convertScript(rendered string, field func(gen.Script) uint32) (string, bool) {
	var out strings.Builder
	for _, character := range rendered {
		index := sort.Search(len(gen.Scripts), func(i int) bool { return gen.Scripts[i].Base >= uint32(character) })
		if index >= len(gen.Scripts) || gen.Scripts[index].Base != uint32(character) {
			return "", false
		}
		mapped := field(gen.Scripts[index])
		if mapped == 0 {
			return "", false
		}
		out.WriteRune(rune(mapped))
	}
	return out.String(), true
}

func writeDelimiter(out *strings.Builder, delimiter Delimiter) {
	switch delimiter {
	case DelimLeftParen:
		out.WriteByte('(')
	case DelimRightParen:
		out.WriteByte(')')
	case DelimLeftBracket:
		out.WriteByte('[')
	case DelimRightBracket:
		out.WriteByte(']')
	case DelimLeftBrace:
		out.WriteByte('{')
	case DelimRightBrace:
		out.WriteByte('}')
	case DelimBar:
		out.WriteByte('|')
	}
}
