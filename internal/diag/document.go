package diag

import (
	"slices"
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

type FileDiagnostics struct {
	Path        string
	Kind        string
	Source      []byte
	Diagnostics []Diagnostic
}

func AppendDocument(dst []byte, files []FileDiagnostics) []byte {
	ordered := orderedFiles(files)
	var sum summary
	dst = append(dst, `{"version":1,"files":[`...)
	for i := range ordered {
		if i > 0 {
			dst = append(dst, ',')
		}
		dst = appendReportFile(dst, &ordered[i])
		sum.count(ordered[i].Diagnostics)
	}
	dst = append(dst, `],"summary":`...)
	dst = sum.appendJSON(dst)
	return append(dst, '}', '\n')
}

type summary struct {
	files    int
	errors   int
	warnings int
	infos    int
}

func (s *summary) count(ds []Diagnostic) {
	s.files++
	for i := range ds {
		switch ds[i].Severity {
		case SeverityError:
			s.errors++
		case SeverityWarning:
			s.warnings++
		default:
			s.infos++
		}
	}
}

func (s *summary) appendJSON(dst []byte) []byte {
	dst = append(dst, `{"files":`...)
	dst = strconv.AppendInt(dst, int64(s.files), 10)
	dst = append(dst, `,"errors":`...)
	dst = strconv.AppendInt(dst, int64(s.errors), 10)
	dst = append(dst, `,"warnings":`...)
	dst = strconv.AppendInt(dst, int64(s.warnings), 10)
	dst = append(dst, `,"info":`...)
	dst = strconv.AppendInt(dst, int64(s.infos), 10)
	return append(dst, '}')
}

func appendReportFile(dst []byte, f *FileDiagnostics) []byte {
	ix := source.NewIndex(f.Source)
	dst = append(dst, `{"path":`...)
	dst = AppendString(dst, f.Path)
	dst = append(dst, `,"kind":`...)
	dst = appendKind(dst, f.Kind)
	dst = append(dst, `,"diagnostics":[`...)
	for i := range f.Diagnostics {
		if i > 0 {
			dst = append(dst, ',')
		}
		dst = AppendDiagnosticJSON(dst, ix, f.Diagnostics[i])
	}
	return append(dst, ']', '}')
}

func appendKind(dst []byte, kind string) []byte {
	if kind == "" {
		return append(dst, `null`...)
	}
	return AppendString(dst, kind)
}

func orderedFiles(files []FileDiagnostics) []FileDiagnostics {
	out := make([]FileDiagnostics, len(files))
	for i := range files {
		out[i] = files[i]
		out[i].Diagnostics = slices.Clone(files[i].Diagnostics)
		Sort(out[i].Diagnostics)
	}
	slices.SortStableFunc(out, func(a, b FileDiagnostics) int {
		return strings.Compare(a.Path, b.Path)
	})
	return out
}
