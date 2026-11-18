package railroad

import (
	"strings"

	syntax "github.com/gosuda/elegant-mermaid/internal/syntax/railroad"
)

func (r *resolver) lowerBody(body syntax.Expression) Node {
	switch v := body.(type) {
	case *syntax.EbnfChoice:
		return r.ebnfChoice(v)
	case *syntax.AbnfAlternation:
		return r.abnfAlternation(v)
	case *syntax.PegOrderedChoice:
		return r.pegChoice(v)
	}
	return r.lowerConstructor(body)
}

func (r *resolver) lowerConstructor(body syntax.Expression) Node {
	switch v := body.(type) {
	case *syntax.RailroadSequenceExpr:
		return collapseSequence(r.lowerAll(v.Elements))
	case *syntax.RailroadChoiceExpr:
		return collapseChoice(r.lowerAll(v.Alternatives))
	case *syntax.RailroadOptionalExpr:
		return &Optional{Element: r.lowerBody(v.Element)}
	case *syntax.RailroadOneOrMoreExpr:
		return &Repetition{Element: r.lowerBody(v.Element), Min: 1, Max: Unbounded}
	case *syntax.RailroadZeroOrMoreExpr:
		return &Repetition{Element: r.lowerBody(v.Element), Min: 0, Max: Unbounded}
	case *syntax.RailroadTerminalExpr:
		return &Terminal{Value: v.Value.Text}
	case *syntax.RailroadNonTerminalExpr:
		return &NonTerminal{Name: v.Name.Text}
	}
	special := body.(*syntax.RailroadSpecialExpr)
	return &Special{Text: special.Text.Text}
}

func (r *resolver) lowerAll(items []syntax.Expression) []Node {
	out := make([]Node, len(items))
	for i, item := range items {
		out[i] = r.lowerBody(item)
	}
	return out
}

func collapseSequence(elements []Node) Node {
	if len(elements) == 1 {
		return elements[0]
	}
	return &Sequence{Elements: elements}
}

func collapseChoice(alternatives []Node) Node {
	if len(alternatives) == 1 {
		return alternatives[0]
	}
	return &Choice{Alternatives: alternatives}
}

func (r *resolver) ebnfChoice(c *syntax.EbnfChoice) Node {
	alternatives := make([]Node, len(c.Alternatives))
	for i := range c.Alternatives {
		alternatives[i] = r.ebnfSequence(&c.Alternatives[i])
	}
	return collapseChoice(alternatives)
}

func (r *resolver) ebnfSequence(s *syntax.EbnfSequence) Node {
	elements := make([]Node, len(s.Elements))
	for i := range s.Elements {
		elements[i] = r.ebnfTerm(&s.Elements[i])
	}
	return collapseSequence(elements)
}

func (r *resolver) ebnfTerm(t *syntax.EbnfTerm) Node {
	node := r.ebnfPrimary(t.Base)
	for _, postfix := range t.Postfixes {
		node = r.ebnfPostfix(node, postfix)
	}
	return node
}

func (r *resolver) ebnfPostfix(node Node, postfix syntax.EbnfPostfix) Node {
	switch postfix.(type) {
	case *syntax.EbnfOptionalPostfix:
		return &Optional{Element: node}
	case *syntax.EbnfZeroOrMorePostfix:
		return &Repetition{Element: node, Min: 0, Max: Unbounded}
	case *syntax.EbnfOneOrMorePostfix:
		return &Repetition{Element: node, Min: 1, Max: Unbounded}
	}
	exception := postfix.(*syntax.EbnfExceptionPostfix)
	return &Sequence{Elements: []Node{node, &Terminal{Value: "-"}, r.ebnfPrimary(exception.Except)}}
}

func (r *resolver) ebnfPrimary(primary syntax.EbnfPrimary) Node {
	switch v := primary.(type) {
	case *syntax.EbnfTerminal:
		return &Terminal{Value: v.Value.Text}
	case *syntax.EbnfNonTerminal:
		return &NonTerminal{Name: v.Name.Text}
	case *syntax.EbnfSpecial:
		return &Special{Text: v.Text.Text}
	case *syntax.EbnfGroup:
		return r.ebnfChoice(v.Element)
	case *syntax.EbnfOptional:
		return &Optional{Element: r.ebnfChoice(v.Element)}
	}
	repetition := primary.(*syntax.EbnfRepetition)
	return &Repetition{Element: r.ebnfChoice(repetition.Element), Min: 0, Max: Unbounded}
}

func (r *resolver) abnfAlternation(a *syntax.AbnfAlternation) Node {
	alternatives := make([]Node, len(a.Alternatives))
	for i := range a.Alternatives {
		alternatives[i] = r.abnfConcatenation(&a.Alternatives[i])
	}
	return collapseChoice(alternatives)
}

func (r *resolver) abnfConcatenation(c *syntax.AbnfConcatenation) Node {
	elements := make([]Node, len(c.Elements))
	for i := range c.Elements {
		elements[i] = r.abnfElement(&c.Elements[i])
	}
	return collapseSequence(elements)
}

func (r *resolver) abnfElement(e *syntax.AbnfElement) Node {
	inner := r.abnfPrimary(e.Primary)
	if e.Repeat == nil {
		return inner
	}
	lower, upper, upperText := repeatBounds(e.Repeat.Text)
	if lower == 0 && upper == 1 {
		return &Optional{Element: inner}
	}
	if upper != Unbounded {
		r.repeatNotice(*e.Repeat, upperText)
	}
	return &Repetition{Element: inner, Min: lower, Max: upper}
}

func repeatBounds(text string) (lower, upper int64, upperText string) {
	lowerDigits, upperDigits, star := strings.Cut(text, "*")
	if !star {
		n := parseCount(text)
		return n, n, trimZeros(text)
	}
	upper = Unbounded
	if upperDigits != "" {
		upper = parseCount(upperDigits)
	}
	return parseCount(lowerDigits), upper, trimZeros(upperDigits)
}

func (r *resolver) abnfPrimary(primary syntax.AbnfPrimary) Node {
	switch v := primary.(type) {
	case *syntax.AbnfStringLiteral:
		return &Terminal{Value: v.Value.Text}
	case *syntax.AbnfNumVal:
		return &Terminal{Value: v.Value.Text}
	case *syntax.AbnfRuleName:
		return &NonTerminal{Name: v.Name.Text}
	case *syntax.AbnfGroup:
		return r.abnfAlternation(v.Element)
	}
	optional := primary.(*syntax.AbnfOptionalGroup)
	return &Optional{Element: r.abnfAlternation(optional.Element)}
}

func (r *resolver) pegChoice(c *syntax.PegOrderedChoice) Node {
	alternatives := make([]Node, len(c.Alternatives))
	for i := range c.Alternatives {
		alternatives[i] = r.pegSequence(&c.Alternatives[i])
	}
	return collapseChoice(alternatives)
}

func (r *resolver) pegSequence(s *syntax.PegSequence) Node {
	elements := make([]Node, len(s.Elements))
	for i := range s.Elements {
		elements[i] = r.pegPrefix(&s.Elements[i])
	}
	return collapseSequence(elements)
}

func (r *resolver) pegPrefix(p *syntax.PegPrefix) Node {
	inner := r.pegSuffix(&p.Suffix)
	if p.Operator == nil {
		return inner
	}
	return &Special{Text: p.Operator.Text + label(inner)}
}

func label(node Node) string {
	switch v := node.(type) {
	case *Terminal:
		return `"` + v.Value + `"`
	case *NonTerminal:
		return v.Name
	case *Special:
		return v.Text
	}
	return "(...)"
}

func (r *resolver) pegSuffix(s *syntax.PegSuffix) Node {
	inner := r.pegPrimary(s.Primary)
	if s.Operator == nil {
		return inner
	}
	switch s.Operator.Kind {
	case "?":
		return &Optional{Element: inner}
	case "*":
		return &Repetition{Element: inner, Min: 0, Max: Unbounded}
	}
	return &Repetition{Element: inner, Min: 1, Max: Unbounded}
}

func (r *resolver) pegPrimary(primary syntax.PegPrimary) Node {
	switch v := primary.(type) {
	case *syntax.PegLiteral:
		return &Terminal{Value: v.Value.Text}
	case *syntax.PegIdentifier:
		return &NonTerminal{Name: v.Name.Text}
	case *syntax.PegGroup:
		return r.pegChoice(v.Element)
	}
	return &Special{Text: "."}
}
