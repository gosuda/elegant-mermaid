package math

import (
	"sort"
	"strings"
	"unicode"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

const maxDepth = 64

const failureHelp = "The source text is shown as written."

type failureKind uint8

const (
	failureSyntax failureKind = iota
	failureUnsupported
	failureDepth
)

type failure struct {
	kind failureKind
	text string
	span source.Span
}

func (f *failure) diagnostic(formula string) diag.Diagnostic {
	whole := source.Span{Start: 0, End: len(formula)}
	switch f.kind {
	case failureSyntax:
		return diag.Diagnostic{Code: "math/syntax", Severity: diag.SeverityError, Message: "invalid math syntax: " + f.text, Span: whole, Help: failureHelp}
	case failureUnsupported:
		return diag.Diagnostic{Code: "math/unsupported-command", Severity: diag.SeverityWarning, Message: "unsupported math command \\" + f.text, Span: whole, Help: failureHelp}
	}
	return diag.Diagnostic{Code: "limit/nesting-depth", Severity: diag.SeverityError, Message: "nesting depth exceeds 64", Span: f.span, Help: "Reduce the nesting to 64 levels or fewer."}
}

func syntaxFailure(reason string) *failure {
	return &failure{kind: failureSyntax, text: reason}
}

func Parse(formula string) Parsed {
	p := &parser{src: formula}
	expression, fail := p.row(stopEnd, 0, fontChoice{}, modeMath)
	if fail != nil {
		return Parsed{
			Source:      formula,
			Expression:  &Expr{Span: source.Span{Start: 0, End: len(formula)}, Kind: KindLiteral, Literal: formula},
			Diagnostics: []diag.Diagnostic{fail.diagnostic(formula)},
		}
	}
	return Parsed{Source: formula, Expression: expression}
}

type stopKind uint8

const (
	stopEnd stopKind = iota
	stopBrace
	stopIndex
	stopRight
)

type mode uint8

const (
	modeMath mode = iota
	modeText
)

type binding uint8

const (
	bindAtom binding = iota
	bindGroup
)

type fontChoice struct {
	font Font
	set  bool
}

func chosen(font Font) fontChoice {
	return fontChoice{font: font, set: true}
}

func (c fontChoice) or(fallback Font) Font {
	if c.set {
		return c.font
	}
	return fallback
}

type parser struct {
	src string
	off int
}

func (p *parser) peek() (rune, bool) {
	if p.off >= len(p.src) {
		return 0, false
	}
	r, _ := utf8.DecodeRuneInString(p.src[p.off:])
	return r, true
}

func (p *parser) take() (rune, bool) {
	if p.off >= len(p.src) {
		return 0, false
	}
	r, size := utf8.DecodeRuneInString(p.src[p.off:])
	p.off += size
	return r, true
}

func (p *parser) peekIs(want rune) bool {
	r, ok := p.peek()
	return ok && r == want
}

func (p *parser) whitespace() {
	for {
		r, ok := p.peek()
		if !ok || !unicode.IsSpace(r) {
			return
		}
		p.take()
	}
}

func (p *parser) right() bool {
	tail, ok := strings.CutPrefix(p.src[p.off:], "\\right")
	return ok && (tail == "" || !isASCIIAlpha(rune(tail[0])))
}

func (p *parser) nested(depth int) (int, *failure) {
	if depth < maxDepth {
		return depth + 1, nil
	}
	end := p.off
	if p.off < len(p.src) {
		_, size := utf8.DecodeRuneInString(p.src[p.off:])
		end += size
	}
	return 0, &failure{kind: failureDepth, span: source.Span{Start: p.off, End: end}}
}

func isASCIIAlpha(r rune) bool {
	return r >= 'a' && r <= 'z' || r >= 'A' && r <= 'Z'
}

func isASCIIPunct(b byte) bool {
	return b >= '!' && b <= '/' || b >= ':' && b <= '@' || b >= '[' && b <= '`' || b >= '{' && b <= '~'
}

func (p *parser) closes(stop stopKind, r rune) bool {
	switch stop {
	case stopBrace:
		return r == '}'
	case stopIndex:
		return r == ']'
	case stopRight:
		return p.right()
	}
	return false
}

func (p *parser) row(stop stopKind, depth int, font fontChoice, m mode) (*Expr, *failure) {
	start := p.off
	var children []*Expr
	for {
		done, fail := p.rowEnd(stop, m)
		if fail != nil {
			return nil, fail
		}
		if done {
			break
		}
		child, fail := p.rowItem(depth, font, m)
		if fail != nil {
			return nil, fail
		}
		children = append(children, child)
	}
	return &Expr{Span: source.Span{Start: start, End: p.off}, Kind: KindRow, Children: children}, nil
}

func (p *parser) rowEnd(stop stopKind, m mode) (bool, *failure) {
	if m == modeMath {
		p.whitespace()
	}
	r, ok := p.peek()
	switch {
	case !ok && stop != stopEnd:
		return false, syntaxFailure("unclosed group or delimiter")
	case !ok, p.closes(stop, r):
		return true, nil
	case r == '}':
		return false, syntaxFailure("unmatched closing brace")
	case m == modeMath && (r == '^' || r == '_'):
		return false, syntaxFailure("script has no base")
	}
	return false, nil
}

func (p *parser) rowItem(depth int, font fontChoice, m mode) (*Expr, *failure) {
	atom, fail := p.atom(depth, font, m)
	if fail != nil || m == modeText {
		return atom, fail
	}
	return p.scripts(atom, depth, font)
}

func (p *parser) group(depth int, font fontChoice, m mode) (*Expr, *failure) {
	next, fail := p.nested(depth)
	if fail != nil {
		return nil, fail
	}
	start := p.off
	p.take()
	body, fail := p.row(stopBrace, next, font, m)
	if fail != nil {
		return nil, fail
	}
	p.take()
	return &Expr{Span: source.Span{Start: start, End: p.off}, Kind: KindGroup, Body: body}, nil
}

func (p *parser) argument(depth int, font fontChoice, m mode, bind binding) (*Expr, *failure) {
	p.whitespace()
	r, ok := p.peek()
	switch {
	case ok && r == '{':
		return p.group(depth, font, m)
	case !ok || r == '}' || r == '^' || r == '_':
		return nil, syntaxFailure("missing argument")
	case p.right() || bind == bindGroup:
		return nil, syntaxFailure("missing braced argument")
	}
	next, fail := p.nested(depth)
	if fail != nil {
		return nil, fail
	}
	return p.atom(next, font, m)
}

func (p *parser) scripts(base *Expr, depth int, font fontChoice) (*Expr, *failure) {
	var superscript, subscript *Expr
	for {
		p.whitespace()
		marker, ok := p.peek()
		if !ok || marker != '^' && marker != '_' {
			break
		}
		p.take()
		target := &subscript
		if marker == '^' {
			target = &superscript
		}
		if *target != nil {
			return nil, syntaxFailure("duplicate script")
		}
		arg, fail := p.argument(depth, font, modeMath, bindAtom)
		if fail != nil {
			return nil, fail
		}
		*target = arg
	}
	if superscript == nil && subscript == nil {
		return base, nil
	}
	return &Expr{
		Span:        source.Span{Start: base.Span.Start, End: p.off},
		Kind:        KindScripts,
		Base:        base,
		Superscript: superscript,
		Subscript:   subscript,
	}, nil
}

func (p *parser) atom(depth int, font fontChoice, m mode) (*Expr, *failure) {
	start := p.off
	if p.peekIs('{') {
		return p.group(depth, font, m)
	}
	r, ok := p.take()
	if !ok {
		return nil, syntaxFailure("missing argument")
	}
	var expr *Expr
	switch {
	case r == '\\':
		var fail *failure
		expr, fail = p.command(depth, font, m)
		if fail != nil {
			return nil, fail
		}
	case r == '=' && m == modeMath:
		expr = &Expr{Kind: KindSymbol, Command: p.src[start:p.off], Char: r, Class: ClassRelation, Font: font.or(FontRoman)}
	default:
		fallback := FontRoman
		if isASCIIAlpha(r) {
			fallback = FontItalic
		}
		expr = &Expr{Kind: KindGlyph, Char: r, Font: font.or(fallback)}
	}
	expr.Span = source.Span{Start: start, End: p.off}
	return expr, nil
}

func (p *parser) commandName() string {
	start := p.off
	if r, ok := p.peek(); ok && isASCIIAlpha(r) {
		for {
			r, ok := p.peek()
			if !ok || !isASCIIAlpha(r) {
				break
			}
			p.take()
		}
	} else {
		p.take()
	}
	return p.src[start:p.off]
}

func (p *parser) command(depth int, font fontChoice, m mode) (*Expr, *failure) {
	name := p.commandName()
	if name == "" {
		return nil, syntaxFailure("missing command")
	}
	if len(name) == 1 && isASCIIPunct(name[0]) && name != "," && name != ";" {
		return &Expr{Kind: KindGlyph, Char: rune(name[0]), Font: font.or(FontRoman)}, nil
	}
	if m == modeMath {
		if expr, fail, handled := p.mathCommand(name, depth, font); handled {
			return expr, fail
		}
	}
	return sharedCommand(name, font)
}

func (p *parser) mathCommand(name string, depth int, font fontChoice) (*Expr, *failure, bool) {
	var expr *Expr
	var fail *failure
	switch name {
	case "frac":
		expr, fail = p.fraction(depth, font)
	case "sqrt":
		expr, fail = p.radical(depth, font)
	case "left":
		expr, fail = p.delimited(depth, font)
	case "right":
		fail = syntaxFailure("right delimiter has no left delimiter")
	case "mathbf", "mathit", "mathrm":
		expr, fail = p.styled(depth, name)
	case "text":
		expr, fail = p.textBody(depth)
	default:
		return nil, nil, false
	}
	return expr, fail, true
}

func (p *parser) textBody(depth int) (*Expr, *failure) {
	body, fail := p.argument(depth, chosen(FontRoman), modeText, bindGroup)
	if fail != nil {
		return nil, fail
	}
	return &Expr{Kind: KindText, Body: body}, nil
}

func sharedCommand(name string, font fontChoice) (*Expr, *failure) {
	switch name {
	case ",":
		return &Expr{Kind: KindSpace, Space: SpaceThin}, nil
	case ";":
		return &Expr{Kind: KindSpace, Space: SpaceMedium}, nil
	case "quad":
		return &Expr{Kind: KindSpace, Space: SpaceQuad}, nil
	case "lim":
		return &Expr{Kind: KindLimit, Font: font.or(FontRoman)}, nil
	}
	if char, class, ok := symbol(name); ok {
		return &Expr{Kind: KindSymbol, Command: name, Char: char, Class: class, Font: font.or(FontRoman)}, nil
	}
	return nil, &failure{kind: failureUnsupported, text: name}
}

func (p *parser) fraction(depth int, font fontChoice) (*Expr, *failure) {
	numerator, fail := p.argument(depth, font, modeMath, bindGroup)
	if fail != nil {
		return nil, fail
	}
	denominator, fail := p.argument(depth, font, modeMath, bindGroup)
	if fail != nil {
		return nil, fail
	}
	return &Expr{Kind: KindFraction, Numerator: numerator, Denominator: denominator}, nil
}

func (p *parser) radical(depth int, font fontChoice) (*Expr, *failure) {
	p.whitespace()
	var index *Expr
	if p.peekIs('[') {
		next, fail := p.nested(depth)
		if fail != nil {
			return nil, fail
		}
		p.take()
		index, fail = p.row(stopIndex, next, font, modeMath)
		if fail != nil {
			return nil, fail
		}
		p.take()
	}
	radicand, fail := p.argument(depth, font, modeMath, bindGroup)
	if fail != nil {
		return nil, fail
	}
	return &Expr{Kind: KindRadical, Index: index, Radicand: radicand}, nil
}

func (p *parser) delimited(depth int, font fontChoice) (*Expr, *failure) {
	next, fail := p.nested(depth)
	if fail != nil {
		return nil, fail
	}
	left, fail := p.delimiter()
	if fail != nil {
		return nil, fail
	}
	body, fail := p.row(stopRight, next, font, modeMath)
	if fail != nil {
		return nil, fail
	}
	p.off += len("\\right")
	right, fail := p.delimiter()
	if fail != nil {
		return nil, fail
	}
	return &Expr{Kind: KindDelimited, Left: left, Body: body, Right: right}, nil
}

func (p *parser) styled(depth int, name string) (*Expr, *failure) {
	selected := FontRoman
	switch name {
	case "mathbf":
		selected = FontBold
	case "mathit":
		selected = FontItalic
	}
	body, fail := p.argument(depth, chosen(selected), modeMath, bindGroup)
	if fail != nil {
		return nil, fail
	}
	return &Expr{Kind: KindStyled, Font: selected, Body: body}, nil
}

var plainDelimiters = map[rune]Delimiter{
	'(': DelimLeftParen,
	')': DelimRightParen,
	'[': DelimLeftBracket,
	']': DelimRightBracket,
	'|': DelimBar,
	'.': DelimInvisible,
}

var escapedDelimiters = map[rune]Delimiter{
	'{': DelimLeftBrace,
	'}': DelimRightBrace,
}

func (p *parser) delimiter() (Delimiter, *failure) {
	p.whitespace()
	table := plainDelimiters
	if p.peekIs('\\') {
		p.take()
		table = escapedDelimiters
	}
	r, taken := p.take()
	if found, ok := table[r]; ok && taken {
		return found, nil
	}
	return 0, syntaxFailure("missing or invalid delimiter")
}

type symbolEntry struct {
	char  rune
	class SymbolClass
}

var symbolTable = map[string]symbolEntry{
	"sum":            {'∑', ClassSum},
	"prod":           {'∏', ClassProduct},
	"int":            {'∫', ClassIntegral},
	"infty":          {'∞', ClassOrdinary},
	"pm":             {'±', ClassBinary},
	"times":          {'×', ClassBinary},
	"div":            {'÷', ClassBinary},
	"cdot":           {'⋅', ClassBinary},
	"le":             {'≤', ClassRelation},
	"ge":             {'≥', ClassRelation},
	"ne":             {'≠', ClassRelation},
	"approx":         {'≈', ClassRelation},
	"to":             {'→', ClassRelation},
	"leftarrow":      {'←', ClassRelation},
	"Rightarrow":     {'⇒', ClassRelation},
	"Leftrightarrow": {'⇔', ClassRelation},
}

func symbol(name string) (rune, SymbolClass, bool) {
	if entry, ok := symbolTable[name]; ok {
		return entry.char, entry.class, true
	}
	return greekSymbol(name)
}

func greekSymbol(name string) (rune, SymbolClass, bool) {
	table := gen.MathGreekTable
	index := sort.Search(len(table), func(i int) bool { return table[i].Name >= name })
	if index < len(table) && table[index].Name == name && utf8.ValidRune(rune(table[index].Codepoint)) {
		return rune(table[index].Codepoint), ClassGreek, true
	}
	return 0, 0, false
}
