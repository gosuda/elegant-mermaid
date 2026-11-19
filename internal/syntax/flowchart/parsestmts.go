package flowchart

import (
	"github.com/gosuda/elegant-mermaid/internal/source"
)

func (p *parser) parseSubgraph() Stmt {
	kw := p.next()
	sg := &Subgraph{Keyword: kw}
	sg.Span = kw.Span
	if header, ok := p.parseSubgraphHeader(); ok {
		sg.ID = header.id
		sg.Title = header.title
		sg.Span.End = header.end
	}
	if sg.ID == nil {
		p.report(unexpectedDiagnostic(p.peek().Span, p.peek().Text, []string{"NODE_STRING", "STR"}))
	}
	if p.atAny(TokNewline, TokSemi) {
		p.next()
	}
	body := p.parseSubgraphBody()
	sg.Body = body
	if end, ok := p.accept(TokEnd); ok {
		sg.End = end
		sg.Span.End = end.Span.End
	} else {
		p.report(tokenDiagnostic(codeUnterminated, sg.Span, "subgraph"))
	}
	for _, line := range body {
		if dir, ok := line.Stmt.(*DirectionStatement); ok {
			sg.Direction = dir
		}
	}
	return sg
}

type subgraphHeader struct {
	id    *TextNoTags
	title *Text
	end   int
}

func (p *parser) parseSubgraphHeader() (subgraphHeader, bool) {
	save := p.i
	p.skipSpaces()
	text, ok := p.parseTextNoTags()
	if !ok {
		p.i = save
		return subgraphHeader{}, false
	}
	for len(text.Tokens) > 0 && text.Tokens[len(text.Tokens)-1].Kind == TokSpace {
		text.Tokens = text.Tokens[:len(text.Tokens)-1]
	}
	header := subgraphHeader{id: &text, end: text.Span.End}
	if open, found := p.accept(TokSQS); found {
		title := p.parseText(TokSQE)
		header.title = &title
		if closer, closed := p.accept(TokSQE); closed {
			header.end = closer.Span.End
		} else {
			header.end = textEnd(title, open)
			p.report(plainDiagnostic(codeUnclosedNodeBracket, source.Span{Start: open.Span.Start, End: header.end}))
		}
	}
	return header, true
}

func (p *parser) parseSubgraphBody() []Line {
	var lines []Line
	for {
		p.skipTrivia()
		tok := p.peek()
		if tok.Kind == TokEOF || tok.Kind == TokEnd {
			return lines
		}
		if stmt, ok := p.parseStatement(); ok {
			lines = append(lines, Line{Stmt: stmt})
		}
	}
}

func (p *parser) parseTextNoTags() (TextNoTags, bool) {
	out := TextNoTags{Tokens: []Token{}}
	for isTextNoTagsToken(p.peek().Kind) || p.atAny(TokStr, TokMDStr) {
		out.Tokens = append(out.Tokens, p.next())
	}
	if len(out.Tokens) == 0 {
		return TextNoTags{}, false
	}
	out.Span = source.Span{Start: out.Tokens[0].Span.Start, End: out.Tokens[len(out.Tokens)-1].Span.End}
	return out, true
}

func (p *parser) parseStyle() Stmt {
	kw := p.next()
	stmt := &StyleStatement{Keyword: kw}
	stmt.Span = kw.Span
	p.skipSpaces()
	target, ok := p.parseIdString()
	if !ok {
		p.report(plainDiagnostic(codeLinkMissing, kw.Span))
		return stmt
	}
	stmt.Targets = []IdString{target}
	stmt.Span.End = target.Span.End
	p.skipSpaces()
	if styles, ok := p.parseStylesOpt(); ok {
		stmt.Styles = styles
		stmt.Span.End = styles.Span.End
	}
	return stmt
}

func (p *parser) parseClassDef() Stmt {
	kw := p.next()
	stmt := &ClassDefStatement{Keyword: kw}
	stmt.Span = kw.Span
	p.skipSpaces()
	names, ok := p.parseIdString()
	if !ok {
		p.report(plainDiagnostic(codeClassMalformed, kw.Span))
		return stmt
	}
	stmt.Names = []IdString{names}
	stmt.Span.End = names.Span.End
	p.skipSpaces()
	if styles, ok := p.parseStylesOpt(); ok {
		stmt.Styles = styles
		stmt.Span.End = styles.Span.End
	}
	return stmt
}

func (p *parser) parseClass() Stmt {
	kw := p.next()
	stmt := &ClassStatement{Keyword: kw}
	stmt.Span = kw.Span
	if !p.at(TokSpace) {
		p.report(plainDiagnostic(codeClassMalformed, kw.Span))
		return stmt
	}
	p.next()
	targets, ok := p.parseIdString()
	if !ok {
		p.report(plainDiagnostic(codeClassMalformed, kw.Span))
		return stmt
	}
	stmt.Targets = []IdString{targets}
	stmt.Span.End = targets.Span.End
	if !p.at(TokSpace) {
		p.report(plainDiagnostic(codeClassMalformed, kw.Span))
		return stmt
	}
	p.next()
	class, ok := p.parseIdString()
	if !ok {
		p.report(plainDiagnostic(codeClassMalformed, kw.Span))
		return stmt
	}
	stmt.Class = class
	stmt.Span.End = class.Span.End
	return stmt
}

func (p *parser) parseStylesOpt() (StylesOpt, bool) {
	out := StylesOpt{Styles: []Style{}}
	for {
		style, ok := p.parseStyleDecl()
		if !ok {
			break
		}
		out.Styles = append(out.Styles, style)
		out.Span = spanJoin(out.Span, style.Span)
		if !p.at(TokComma) {
			return out, true
		}
		p.next()
		p.skipSpaces()
	}
	return out, len(out.Styles) > 0
}

func (p *parser) parseStyleDecl() (Style, bool) {
	out := Style{Components: []Token{}}
	for isStyleComponent(p.peek().Kind) {
		out.Components = append(out.Components, p.next())
	}
	if len(out.Components) == 0 {
		return Style{}, false
	}
	out.Components = trimSpaceTokens(out.Components)
	if len(out.Components) == 0 {
		return Style{}, false
	}
	out.Span = source.Span{Start: out.Components[0].Span.Start, End: out.Components[len(out.Components)-1].Span.End}
	return out, true
}

func trimSpaceTokens(tokens []Token) []Token {
	start, end := 0, len(tokens)
	for start < end && tokens[start].Kind == TokSpace {
		start++
	}
	for end > start && tokens[end-1].Kind == TokSpace {
		end--
	}
	return tokens[start:end]
}

func isStyleComponent(k TokenKind) bool {
	switch k {
	case TokNum, TokNodeString, TokColon, TokSpace, TokBrkt, TokStyle:
		return true
	}
	return false
}

func (p *parser) parseLinkStyle() Stmt {
	kw := p.next()
	stmt := &LinkStyleStatement{Keyword: kw}
	stmt.Span = kw.Span
	p.skipSpaces()
	if def, ok := p.accept(TokDefault); ok {
		stmt.Default = true
		stmt.Span.End = def.Span.End
	} else if list, ok := p.parseNumList(); ok {
		stmt.Indices = list
		stmt.Span.End = list.Span.End
	} else {
		p.report(plainDiagnostic(codeLinkStyleRange, kw.Span))
		return stmt
	}
	p.skipSpaces()
	if p.at(TokInterpolate) {
		p.next()
		p.skipSpaces()
		alpha, ok := p.parseAlphaNum()
		if !ok {
			p.report(plainDiagnostic(codeLinkStyleRange, kw.Span))
			return stmt
		}
		stmt.Interpolation = &alpha
		stmt.Span.End = alpha.Span.End
		p.skipSpaces()
	}
	if styles, ok := p.parseStylesOpt(); ok {
		stmt.Styles = &styles
		stmt.Span.End = styles.Span.End
	}
	return stmt
}

func (p *parser) parseNumList() (NumList, bool) {
	out := NumList{Numbers: []Token{}}
	for {
		if p.at(TokColon) {
			p.report(plainDiagnostic(codeLinkStyleRange, p.peek().Span))
			p.next()
			continue
		}
		num, ok := p.accept(TokNum)
		if !ok {
			break
		}
		out.Numbers = append(out.Numbers, num)
		if p.at(TokColon) {
			p.report(plainDiagnostic(codeLinkStyleRange, p.peek().Span))
		}
		if !p.at(TokComma) {
			break
		}
		p.next()
		p.skipSpaces()
	}
	if len(out.Numbers) == 0 {
		return NumList{}, false
	}
	out.Span = source.Span{Start: out.Numbers[0].Span.Start, End: out.Numbers[len(out.Numbers)-1].Span.End}
	return out, true
}

func (p *parser) parseAlphaNum() (AlphaNum, bool) {
	out := AlphaNum{Tokens: []Token{}}
	for isAlphaNumToken(p.peek().Kind) {
		out.Tokens = append(out.Tokens, p.next())
	}
	if len(out.Tokens) == 0 {
		return AlphaNum{}, false
	}
	out.Span = source.Span{Start: out.Tokens[0].Span.Start, End: out.Tokens[len(out.Tokens)-1].Span.End}
	return out, true
}

func (p *parser) parseClick() Stmt {
	kw := p.next()
	stmt := &ClickStatement{Keyword: kw}
	stmt.Span = kw.Span
	stmt.Target = IdString{Tokens: []Token{kw}, Span: kw.Span}
	p.skipSpaces()
	p.parseClickAction(stmt)
	return stmt
}

func (p *parser) parseClickAction(stmt *ClickStatement) {
	switch p.peek().Kind {
	case TokCallbackName:
		stmt.Callback = p.parseCallbackAction()
	case TokHref:
		href := p.next()
		p.skipSpaces()
		stmt.Link = p.parseLinkAction(&href)
	case TokStr, TokMDStr:
		stmt.Link = p.parseLinkAction(nil)
	default:
		alpha, ok := p.parseAlphaNum()
		if !ok {
			return
		}
		stmt.Link = &LinkAction{URL: Text{Tokens: alpha.Tokens, Span: alpha.Span}, Span: alpha.Span}
		stmt.Span.End = alpha.Span.End
		p.skipSpaces()
		if tip, ok := p.parseClickString(); ok {
			stmt.Link.Tip = tip
			stmt.Link.Span.End = tip.Span.End
			stmt.Span.End = tip.Span.End
		}
		return
	}
	if stmt.Callback != nil {
		stmt.Span.End = stmt.Callback.Span.End
	} else {
		stmt.Span.End = stmt.Link.Span.End
	}
}

func (p *parser) parseCallbackAction() *CallbackAction {
	name := p.next()
	action := &CallbackAction{Name: name, Span: name.Span}
	if args, ok := p.accept(TokCallbackArgs); ok {
		action.Args = &args
		action.Span.End = args.Span.End
	}
	p.skipSpaces()
	if tip, ok := p.parseClickString(); ok {
		action.Span.End = tip.Span.End
	}
	p.skipSpaces()
	if p.at(TokLinkTarget) {
		extra := p.next()
		action.Extra = &extra
		action.Span.End = extra.Span.End
		p.report(plainDiagnostic(codeClickExtraText, extra.Span))
		p.skipToStatementBoundary()
	}
	return action
}

func (p *parser) parseLinkAction(href *Token) *LinkAction {
	action := &LinkAction{Href: href}
	if href != nil {
		action.Span = href.Span
	}
	url, ok := p.parseClickString()
	if !ok {
		return action
	}
	action.URL = *url
	action.Span = spanJoin(action.Span, url.Span)
	p.skipSpaces()
	if tip, ok := p.parseClickString(); ok {
		action.Tip = tip
		action.Span.End = tip.Span.End
		p.skipSpaces()
	}
	if target, ok := p.accept(TokLinkTarget); ok {
		action.Target = &target
		action.Span.End = target.Span.End
	}
	return action
}

func (p *parser) parseClickString() (*Text, bool) {
	tok := p.peek()
	if tok.Kind != TokStr && tok.Kind != TokMDStr {
		return nil, false
	}
	p.next()
	text := Text{Tokens: []Token{tok}, Span: tok.Span, Kind: LabelString}
	if tok.Kind == TokMDStr {
		text.Kind = LabelMarkdown
	}
	return &text, true
}
