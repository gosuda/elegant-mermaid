package diag

import (
	"strconv"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

func AppendGitHub(dst []byte, files []FileDiagnostics) []byte {
	ordered := orderedFiles(files)
	for i := range ordered {
		f := &ordered[i]
		ix := source.NewIndex(f.Source)
		for j := range f.Diagnostics {
			dst = appendCommand(dst, ix, f.Path, &f.Diagnostics[j])
		}
	}
	return dst
}

func appendCommand(dst []byte, ix *source.Index, path string, d *Diagnostic) []byte {
	start := ix.Position(d.Span.Start)
	end := ix.Position(d.Span.End)
	dst = append(dst, "::"...)
	dst = append(dst, githubCommand(d.Severity)...)
	dst = append(dst, " file="...)
	dst = appendProperty(dst, path)
	dst = append(dst, ",line="...)
	dst = strconv.AppendInt(dst, int64(start.Line), 10)
	dst = append(dst, ",col="...)
	dst = strconv.AppendInt(dst, int64(start.Column), 10)
	dst = append(dst, ",endLine="...)
	dst = strconv.AppendInt(dst, int64(end.Line), 10)
	dst = append(dst, ",endColumn="...)
	dst = strconv.AppendInt(dst, int64(end.Column), 10)
	dst = append(dst, ",title="...)
	dst = appendProperty(dst, d.Code)
	dst = append(dst, "::"...)
	dst = appendMessage(dst, d.Message)
	return append(dst, '\n')
}

func githubCommand(s Severity) string {
	switch s {
	case SeverityError:
		return "error"
	case SeverityWarning:
		return "warning"
	}
	return "notice"
}

func appendProperty(dst []byte, s string) []byte {
	return appendEscapedData(dst, s, escapePropertyByte)
}

func appendMessage(dst []byte, s string) []byte {
	return appendEscapedData(dst, s, escapeMessageByte)
}

func appendEscapedData(dst []byte, s string, escape func(dst []byte, b byte) ([]byte, bool)) []byte {
	for i := range len(s) {
		var ok bool
		if dst, ok = escape(dst, s[i]); !ok {
			dst = append(dst, s[i])
		}
	}
	return dst
}

func escapePropertyByte(dst []byte, b byte) ([]byte, bool) {
	switch b {
	case ':':
		return append(dst, "%3A"...), true
	case ',':
		return append(dst, "%2C"...), true
	}
	return escapeMessageByte(dst, b)
}

func escapeMessageByte(dst []byte, b byte) ([]byte, bool) {
	switch b {
	case '%':
		return append(dst, "%25"...), true
	case '\r':
		return append(dst, "%0D"...), true
	case '\n':
		return append(dst, "%0A"...), true
	}
	return dst, false
}
