package mermaid

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

type Span struct {
	Start int
	End   int
}

type Position struct {
	Line   int
	Column int
}

type Edit struct {
	Span    Span
	NewText string
}

type Fix struct {
	Title  string
	Safety FixSafety
	Edits  []Edit
}

type Related struct {
	Span    Span
	Message string
}

type Diagnostic struct {
	Code     string
	Severity Severity
	Message  string
	Span     Span
	Related  []Related
	Help     string
	Fixes    []Fix
}

type LintConfig struct {
	Select   []string
	Ignore   []string
	Severity map[string]Severity
	Off      []string
}

type Profile uint8

const (
	ProfileVector Profile = iota
	ProfileCell
)

type Limits struct {
	MaxNodes     int
	MaxEdges     int
	MaxTextBytes int
}

type LayoutOptions struct {
	Profile      Profile
	Theme        string
	Thoroughness int
	MaxWidth     int
	Limits       Limits
	IconPacks    []*IconPack
	Config       []byte
}

type TextMode uint8

const (
	TextFont TextMode = iota
	TextPaths
)

type SVGOptions struct {
	LayoutOptions
	Background string
	Text       TextMode
	Outlines   *GlyphOutlines
	IDPrefix   string
}

type Charset uint8

const (
	CharsetUnicode Charset = iota
	CharsetASCII
)

type ColorMode uint8

const (
	ColorNone ColorMode = iota
	ColorANSI16
	ColorANSI256
	ColorTruecolor
)

type TextOptions struct {
	LayoutOptions
	Charset Charset
	Color   ColorMode
}

type IconPack struct{}

type GlyphOutlines struct{}

type Block struct {
	Source []byte
	Span   Span
	Lines  []BlockLine
}

type BlockLine struct {
	HostOffset  int
	BlockOffset int
	Len         int
}

func (b Block) HostOffset(blockOffset int) int {
	if len(b.Lines) == 0 {
		return b.Span.Start
	}
	at := min(max(blockOffset, 0), len(b.Source))
	line := b.Lines[0]
	for _, candidate := range b.Lines[1:] {
		if candidate.BlockOffset > at {
			break
		}
		line = candidate
	}
	return line.HostOffset + min(at-line.BlockOffset, line.Len)
}
