package railroad

import (
	"errors"
	"strconv"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

var ErrArity = errors.New("railroad layout: composite node has the wrong child count")

type Kind uint8

const (
	KindTerminal Kind = iota
	KindNonTerminal
	KindSpecial
	KindSequence
	KindChoice
	KindOptional
	KindZeroOrMore
	KindOneOrMore
)

func (k Kind) leaf() bool { return k <= KindSpecial }

type Node struct {
	ID       string
	Kind     Kind
	Text     string
	Children []*Node
}

type Rule struct {
	ID    string
	Title string
	Root  *Node
}

type Constants struct {
	PadX, PadY, LineHeight, Hsep, Vsep              int64
	ArcRadius, TerminalRadius, MarkerRadius, Margin int64
	RuleNameGap, RuleEndGap, RuleMinBaseline        int64
	RuleMinHeight, EmptyWidth, EmptyHeight          int64
}

type Params struct {
	Profile   scene.Profile
	Options   scene.Options
	Constants Constants
	Metric    measure.Metric
}

type Join struct {
	ID       string
	From, To string
}

func RouteID(ordinal int) string { return "e" + strconv.Itoa(ordinal) }

func Joins(rules []Rule) []Join {
	var joins []Join
	for _, rule := range rules {
		joins = appendJoins(joins, rule.Root)
	}
	return joins
}

func appendJoins(joins []Join, n *Node) []Join {
	if n.Kind == KindSequence {
		for i := 0; i+1 < len(n.Children); i++ {
			joins = append(joins, Join{ID: RouteID(len(joins)), From: n.Children[i].ID, To: n.Children[i+1].ID})
		}
	}
	for _, child := range n.Children {
		joins = appendJoins(joins, child)
	}
	return joins
}

type point struct{ x, y int64 }

func fit(v int64) (int32, error) {
	if v < int64(geom.I32Min) || v > int64(geom.I32Max) {
		return 0, geom.ErrOverflow
	}
	return int32(v), nil
}

func (p Params) isCell() bool { return p.Profile == scene.ProfileCell }
