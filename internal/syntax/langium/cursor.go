package langium

import (
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

type Cursor struct {
	Src    string
	Tokens []Token
	At     int
	End    int
	Diags  []diag.Diagnostic
	kind   string
}

func NewCursor(kind, src string, removed []source.Span, g Grammar) *Cursor {
	return &Cursor{Src: src, Tokens: Lex(src, removed, g), kind: kind}
}

func Diagnostic(code string, severity diag.Severity, message string, span source.Span) diag.Diagnostic {
	return diag.Diagnostic{Code: code, Severity: severity, Message: message, Span: span, Help: diagnosticHelp(code)}
}

func diagnosticHelp(code string) string {
	for i := range gen.Diagnostics {
		if gen.Diagnostics[i].Code == code {
			return gen.Diagnostics[i].Help
		}
	}
	return ""
}

func (c *Cursor) Token() Token {
	if c.At < len(c.Tokens) {
		return c.Tokens[c.At]
	}
	return Token{Kind: "EOF", Span: source.Span{Start: len(c.Src), End: len(c.Src)}}
}

func (c *Cursor) Ahead(n int) Token {
	if c.At+n < len(c.Tokens) {
		return c.Tokens[c.At+n]
	}
	return Token{Kind: "EOF", Span: source.Span{Start: len(c.Src), End: len(c.Src)}}
}

func (c *Cursor) Kind() string { return c.Token().Kind }

func (c *Cursor) Take() Token {
	t := c.Token()
	if c.At < len(c.Tokens) {
		c.At++
	}
	return t
}

func (c *Cursor) SkipNewlines() {
	for c.Kind() == "NEWLINE" {
		c.At++
	}
}

func (c *Cursor) ContentEnd() int {
	for i := min(c.At, len(c.Tokens)) - 1; i >= 0; i-- {
		if c.Tokens[i].Kind != "NEWLINE" {
			return c.Tokens[i].Span.End
		}
	}
	return 0
}

func (c *Cursor) Issue(name, message string, span source.Span) {
	c.Diags = append(c.Diags, Diagnostic(c.kind+"/"+name, diag.SeverityError, message, span))
}

func (c *Cursor) describe(token Token) string {
	if token.Span.Start == token.Span.End {
		return "end of input"
	}
	return c.Src[token.Span.Start:token.Span.End]
}

func (c *Cursor) Unexpected(expected ...string) {
	token := c.Token()
	if token.Kind == "UNTERMINATED" {
		return
	}
	names := slices.Clone(expected)
	slices.Sort(names)
	c.Issue("unexpected-token", "unexpected "+c.describe(token)+", expected one of: "+strings.Join(names, ", "), token.Span)
}

func (c *Cursor) LineEnd() int {
	for i := c.At; i < len(c.Tokens); i++ {
		switch c.Tokens[i].Kind {
		case "NEWLINE", "EOF", "UNTERMINATED":
			return c.Tokens[i].Span.Start
		}
	}
	return len(c.Src)
}

func (c *Cursor) SkipLine() {
	for {
		switch c.Kind() {
		case "EOF", "UNTERMINATED":
			return
		case "NEWLINE":
			c.Take()
			return
		}
		c.Take()
	}
}

func (c *Cursor) Unknown() {
	first := c.Token()
	c.Issue("unknown-statement", "unknown statement "+c.Src[first.Span.Start:first.Span.End], source.Span{Start: first.Span.Start, End: max(c.LineEnd(), first.Span.End)})
	c.SkipLine()
}

func (c *Cursor) Unterminated() {
	token := c.Token()
	c.Issue("unterminated", "unterminated "+token.Text, token.Span)
}

func (c *Cursor) Finish(expected ...string) bool {
	end := c.ContentEnd()
	switch c.Kind() {
	case "NEWLINE":
		c.Take()
	case "EOF":
	default:
		c.Unexpected(append(slices.Clone(expected), "EOF", "NEWLINE")...)
		c.SkipLine()
		return false
	}
	c.End = end
	return true
}

func (c *Cursor) Metadata() (field string, value Token, ok bool) {
	token := c.Take()
	if !c.Finish() {
		return "", Token{}, false
	}
	return MetadataField(token.Kind), token, true
}

func MetadataField(kind string) string {
	switch kind {
	case "ACC_DESCR":
		return "accDescr"
	case "ACC_TITLE":
		return "accTitle"
	}
	return "title"
}

func IsMetadata(kind string) bool {
	return kind == "ACC_DESCR" || kind == "ACC_TITLE" || kind == "TITLE"
}
