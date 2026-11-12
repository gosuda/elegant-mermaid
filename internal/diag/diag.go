package diag

import (
	"cmp"
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

type Severity uint8

const (
	SeverityError Severity = iota
	SeverityWarning
	SeverityInfo
)

func (s Severity) String() string {
	switch s {
	case SeverityError:
		return "error"
	case SeverityWarning:
		return "warning"
	}
	return "info"
}

type FixSafety uint8

const (
	FixSafe FixSafety = iota
	FixUnsafe
)

func (f FixSafety) String() string {
	if f == FixSafe {
		return "safe"
	}
	return "unsafe"
}

type Edit struct {
	Span    source.Span
	NewText string
}

type Fix struct {
	Title  string
	Safety FixSafety
	Edits  []Edit
}

type Related struct {
	Span    source.Span
	Message string
}

type Diagnostic struct {
	Code     string
	Severity Severity
	Message  string
	Span     source.Span
	Related  []Related
	Help     string
	Fixes    []Fix
}

func Sort(ds []Diagnostic) {
	slices.SortStableFunc(ds, func(a, b Diagnostic) int {
		return cmp.Or(cmp.Compare(a.Span.Start, b.Span.Start), strings.Compare(a.Code, b.Code))
	})
}
