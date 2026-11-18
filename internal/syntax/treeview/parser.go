package treeview

import (
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

const (
	codeUnexpected   = "treeview/unexpected-token"
	codeUnknown      = "treeview/unknown-statement"
	codeUnterminated = "treeview/unterminated"
)

var (
	headerTokens = []string{kindHeader}
	metaTokens   = []string{kindAccDescr, kindAccTitle, kindBare, kindEOF, kindIndent, kindQuoted, kindTitle}
	nodeTokens   = []string{kindBare, kindClass, kindDesc, kindEOF, kindIcon, kindIndent, kindQuoted}
	nameTokens   = []string{kindBare, kindQuoted}
)

func Parse(src []byte, removed []source.Span) (*TreeView, []diag.Diagnostic) {
	text := string(src)
	scan, diags := newScanner(text, removed)
	p := &parser{src: text, scan: scan, diags: diags}
	p.advance()
	return p.treeView(), p.diags
}

type parser struct {
	src    string
	scan   *scanner
	tok    Token
	last   int
	diags  []diag.Diagnostic
	halted bool
}

func Diagnostic(code, message string, span source.Span) diag.Diagnostic {
	help := ""
	for i := range gen.Diagnostics {
		if gen.Diagnostics[i].Code == code {
			help = gen.Diagnostics[i].Help
		}
	}
	return diag.Diagnostic{Code: code, Severity: diag.SeverityError, Message: message, Span: span, Help: help}
}

func (p *parser) advance() {
	for {
		p.tok = p.scan.next()
		switch p.tok.Kind {
		case kindInvalid:
			p.skipInvalid()
		case kindUnterminated:
			p.diags = append(p.diags, Diagnostic(codeUnterminated, "unterminated "+p.tok.Text, p.tok.Span))
			p.halted = true
			p.tok = Token{Kind: kindEOF, Span: source.Span{Start: len(p.src), End: len(p.src)}, from: len(p.scan.text), to: len(p.scan.text)}
			return
		default:
			return
		}
	}
}

func (p *parser) skipInvalid() {
	end := p.scan.lineEnd(p.tok.to)
	span := source.Span{Start: p.tok.Span.Start, End: max(p.scan.finish(end), p.tok.Span.End)}
	p.diags = append(p.diags, Diagnostic(codeUnknown, "unknown statement "+p.tok.Text, span))
	p.scan.at = end
}

func (p *parser) take() Token {
	token := p.tok
	p.last = max(p.last, token.Span.End)
	p.advance()
	return token
}

func (p *parser) describe(token Token) string {
	if token.Span.Start == token.Span.End {
		return "end of input"
	}
	return p.src[token.Span.Start:token.Span.End]
}

func (p *parser) unexpected(expected []string) {
	if p.halted {
		return
	}
	names := slices.Clone(expected)
	slices.Sort(names)
	message := "unexpected " + p.describe(p.tok) + ", expected one of: " + strings.Join(names, ", ")
	p.diags = append(p.diags, Diagnostic(codeUnexpected, message, p.tok.Span))
}

func (p *parser) recover() {
	if p.tok.Kind != kindEOF {
		p.scan.at = max(p.scan.at, p.scan.lineEnd(p.tok.to))
	}
	p.advance()
}

func (p *parser) treeView() *TreeView {
	tv := &TreeView{}
	if p.tok.Kind != kindHeader {
		p.unexpected(headerTokens)
		tv.Span = source.Span{Start: p.tok.Span.Start, End: len(p.src)}
		return tv
	}
	tv.Header = p.take()
	p.metadata(tv)
	for p.tok.Kind != kindEOF {
		if node, ok := p.node(len(tv.Nodes)); ok {
			tv.Nodes = append(tv.Nodes, node)
		}
	}
	tv.Span = source.Span{Start: tv.Header.Span.Start, End: max(p.last, tv.Header.Span.End)}
	return tv
}

func (p *parser) metadata(tv *TreeView) {
	for {
		token := p.tok
		switch token.Kind {
		case kindAccDescr:
			tv.AccDescr = &token
		case kindAccTitle:
			tv.AccTitle = &token
		case kindTitle:
			tv.Title = &token
		default:
			return
		}
		p.take()
	}
}

func (p *parser) node(parsed int) (TreeNode, bool) {
	var node TreeNode
	if p.tok.Kind == kindIndent {
		indent := p.take()
		node.Indent, node.Span = &indent, indent.Span
	}
	if p.tok.Kind != kindQuoted && p.tok.Kind != kindBare {
		p.unexpected(p.nodeStartTokens(node.Indent, parsed))
		p.recover()
		return node, false
	}
	node.Name = p.take()
	if node.Indent == nil {
		node.Span = node.Name.Span
	}
	p.annotations(&node)
	node.Span.End = max(node.Span.End, p.last)
	return node, true
}

func (p *parser) nodeStartTokens(indent *Token, parsed int) []string {
	switch {
	case indent != nil:
		return nameTokens
	case parsed == 0:
		return metaTokens
	}
	return nodeTokens
}

func (p *parser) annotations(node *TreeNode) {
	for {
		token := p.tok
		switch token.Kind {
		case kindClass:
			node.Class = &token
		case kindIcon:
			node.Icon = &token
		case kindDesc:
			node.Desc = &token
		default:
			return
		}
		p.take()
	}
}
