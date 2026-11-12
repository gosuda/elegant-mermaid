package diag

import (
	"strconv"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

func AppendDiagnosticJSON(dst []byte, ix *source.Index, d Diagnostic) []byte {
	start := ix.Position(d.Span.Start)
	end := ix.Position(d.Span.End)
	dst = append(dst, `{"code":`...)
	dst = AppendString(dst, d.Code)
	dst = append(dst, `,"severity":`...)
	dst = AppendString(dst, d.Severity.String())
	dst = append(dst, `,"message":`...)
	dst = AppendString(dst, d.Message)
	dst = append(dst, `,"span":`...)
	dst = appendSpan(dst, d.Span)
	dst = append(dst, `,"line":`...)
	dst = strconv.AppendInt(dst, int64(start.Line), 10)
	dst = append(dst, `,"column":`...)
	dst = strconv.AppendInt(dst, int64(start.Column), 10)
	dst = append(dst, `,"end_line":`...)
	dst = strconv.AppendInt(dst, int64(end.Line), 10)
	dst = append(dst, `,"end_column":`...)
	dst = strconv.AppendInt(dst, int64(end.Column), 10)
	dst = append(dst, `,"related":`...)
	dst = appendRelatedList(dst, ix, d.Related)
	dst = append(dst, `,"help":`...)
	dst = AppendString(dst, d.Help)
	dst = append(dst, `,"fixes":`...)
	dst = appendFixList(dst, d.Fixes)
	return append(dst, '}')
}

func AppendString(dst []byte, s string) []byte {
	dst = append(dst, '"')
	for i := range len(s) {
		dst = appendEscaped(dst, s[i])
	}
	return append(dst, '"')
}

func appendEscaped(dst []byte, b byte) []byte {
	switch b {
	case '"':
		return append(dst, '\\', '"')
	case '\\':
		return append(dst, '\\', '\\')
	case '\b':
		return append(dst, '\\', 'b')
	case '\t':
		return append(dst, '\\', 't')
	case '\n':
		return append(dst, '\\', 'n')
	case '\f':
		return append(dst, '\\', 'f')
	case '\r':
		return append(dst, '\\', 'r')
	}
	if b < 0x20 {
		return append(dst, '\\', 'u', '0', '0', hexDigit(b>>4), hexDigit(b&0x0F))
	}
	return append(dst, b)
}

func hexDigit(v byte) byte {
	if v < 10 {
		return '0' + v
	}
	return 'a' + v - 10
}

func appendSpan(dst []byte, sp source.Span) []byte {
	dst = append(dst, `{"start":`...)
	dst = strconv.AppendInt(dst, int64(sp.Start), 10)
	dst = append(dst, `,"end":`...)
	dst = strconv.AppendInt(dst, int64(sp.End), 10)
	return append(dst, '}')
}

func appendRelatedList(dst []byte, ix *source.Index, rs []Related) []byte {
	dst = append(dst, '[')
	for i := range rs {
		if i > 0 {
			dst = append(dst, ',')
		}
		dst = appendRelated(dst, ix, rs[i])
	}
	return append(dst, ']')
}

func appendRelated(dst []byte, ix *source.Index, r Related) []byte {
	pos := ix.Position(r.Span.Start)
	dst = append(dst, `{"span":`...)
	dst = appendSpan(dst, r.Span)
	dst = append(dst, `,"line":`...)
	dst = strconv.AppendInt(dst, int64(pos.Line), 10)
	dst = append(dst, `,"column":`...)
	dst = strconv.AppendInt(dst, int64(pos.Column), 10)
	dst = append(dst, `,"message":`...)
	dst = AppendString(dst, r.Message)
	return append(dst, '}')
}

func appendFixList(dst []byte, fs []Fix) []byte {
	dst = append(dst, '[')
	for i := range fs {
		if i > 0 {
			dst = append(dst, ',')
		}
		dst = appendFix(dst, fs[i])
	}
	return append(dst, ']')
}

func appendFix(dst []byte, f Fix) []byte {
	dst = append(dst, `{"title":`...)
	dst = AppendString(dst, f.Title)
	dst = append(dst, `,"safety":`...)
	dst = AppendString(dst, f.Safety.String())
	dst = append(dst, `,"edits":`...)
	dst = appendEditList(dst, f.Edits)
	return append(dst, '}')
}

func appendEditList(dst []byte, es []Edit) []byte {
	dst = append(dst, '[')
	for i := range es {
		if i > 0 {
			dst = append(dst, ',')
		}
		dst = appendEdit(dst, es[i])
	}
	return append(dst, ']')
}

func appendEdit(dst []byte, e Edit) []byte {
	dst = append(dst, `{"span":`...)
	dst = appendSpan(dst, e.Span)
	dst = append(dst, `,"new_text":`...)
	dst = AppendString(dst, e.NewText)
	return append(dst, '}')
}
