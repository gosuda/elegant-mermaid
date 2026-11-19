package layout

import (
	"fmt"
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	"github.com/gosuda/elegant-mermaid/internal/layout/railroad"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	railmodel "github.com/gosuda/elegant-mermaid/internal/model/railroad"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const (
	railroadKind = "railroad"
	ruleShape    = "rule"
)

var railroadKinds = []struct {
	shape string
	kind  railroad.Kind
}{
	{"terminal", railroad.KindTerminal},
	{"nonterminal", railroad.KindNonTerminal},
	{"special", railroad.KindSpecial},
	{"sequence", railroad.KindSequence},
	{"choice", railroad.KindChoice},
	{"optional", railroad.KindOptional},
	{"zeroOrMore", railroad.KindZeroOrMore},
	{"oneOrMore", railroad.KindOneOrMore},
}

func FromRailroad(m *railmodel.Model, profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic) {
	options = resolveOptions(options)
	options.Config = nil
	in := Input{Kind: railroadKind, Profile: profile, Direction: scene.DirectionTB, Options: options}
	rules := make([]railroad.Rule, len(m.Rules))
	for i, rule := range m.Rules {
		id := "r" + strconv.Itoa(i)
		next := 0
		rules[i] = railroad.Rule{ID: id, Title: rule.Name + " =", Root: railroadTree(rule.Definition, id, &next)}
		in.addRailroadRule(rules[i])
	}
	for _, join := range railroad.Joins(rules) {
		in.Routes = append(in.Routes, Route{ID: join.ID, From: join.From, To: join.To, Orthogonal: true})
	}
	return in, nil
}

func railroadTree(node railmodel.Node, rule string, next *int) *railroad.Node {
	out := &railroad.Node{ID: rule + "." + strconv.Itoa(*next)}
	*next++
	switch v := node.(type) {
	case *railmodel.Terminal:
		out.Kind, out.Text = railroad.KindTerminal, displayText(v.Value)
	case *railmodel.NonTerminal:
		out.Kind, out.Text = railroad.KindNonTerminal, displayText(v.Name)
	case *railmodel.Special:
		out.Kind, out.Text = railroad.KindSpecial, displayText("? "+v.Text+" ?")
	case *railmodel.Sequence:
		out.Kind = railroad.KindSequence
		out.Children = railroadChildren(v.Elements, rule, next)
	case *railmodel.Choice:
		out.Kind = railroad.KindChoice
		out.Children = railroadChildren(v.Alternatives, rule, next)
	case *railmodel.Optional:
		out.Kind = railroad.KindOptional
		out.Children = railroadChildren([]railmodel.Node{v.Element}, rule, next)
	case *railmodel.Repetition:
		out.Kind = railroad.KindOneOrMore
		if v.Min == 0 {
			out.Kind = railroad.KindZeroOrMore
		}
		out.Children = railroadChildren([]railmodel.Node{v.Element}, rule, next)
	}
	return out
}

func railroadChildren(nodes []railmodel.Node, rule string, next *int) []*railroad.Node {
	out := make([]*railroad.Node, len(nodes))
	for i, node := range nodes {
		out[i] = railroadTree(node, rule, next)
	}
	return out
}

func displayText(text string) string {
	return strings.Map(func(r rune) rune {
		switch {
		case r == '\t' || r == '\n' || r == '\r':
			return ' '
		case r < ' ' || r >= 0x7f && r <= 0x9f:
			return '\ufffd'
		}
		return r
	}, text)
}

func (in *Input) addRailroadRule(rule railroad.Rule) {
	in.Boxes = append(in.Boxes, Box{ID: rule.ID, Role: scene.RoleGroup, Shape: ruleShape, Text: rule.Title})
	in.Labels = append(in.Labels, Label{ID: rule.ID + ".label", Owner: rule.ID, Role: scene.TextRoleLabel, Text: rule.Title})
	in.addRailroadNode(rule.Root, rule.ID)
}

func (in *Input) addRailroadNode(n *railroad.Node, parent string) {
	box := Box{ID: n.ID, Shape: railroadShape(n.Kind), Parent: parent}
	if n.Kind >= railroad.KindSequence {
		box.Role = scene.RoleGroup
		in.Boxes = append(in.Boxes, box)
	} else {
		box.Exclusive, box.Text = true, n.Text
		in.Boxes = append(in.Boxes, box)
		in.Labels = append(in.Labels, Label{ID: n.ID + ".label", Owner: n.ID, Role: scene.TextRoleLabel, Text: n.Text})
	}
	for _, child := range n.Children {
		in.addRailroadNode(child, n.ID)
	}
}

func railroadShape(kind railroad.Kind) string {
	for _, row := range railroadKinds {
		if row.kind == kind {
			return row.shape
		}
	}
	return ""
}

func layoutRailroad(in Input) (scene.Scene, []diag.Diagnostic, error) {
	if err := railroadLimits(in); err != nil {
		return scene.Scene{}, nil, err
	}
	rules, err := railroadRules(in)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	constants, err := railroadConstants(in.Profile)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	options := resolveOptions(in.Options)
	options.Profile, options.Direction = in.Profile, in.Direction
	metric := measure.ForRole(measure.RoleLabel)
	if in.Profile == scene.ProfileCell {
		metric = measure.CellMetric()
	}
	s, err := railroad.Layout(rules, railroad.Params{Profile: in.Profile, Options: options, Constants: constants, Metric: metric})
	return s, nil, err
}

func railroadLimits(in Input) error {
	limits := resolveOptions(in.Options).Limits
	var bytes int64
	for _, b := range in.Boxes {
		if !labelOwned(in.Labels, b.ID) {
			bytes += int64(len(b.Text))
		}
	}
	for _, l := range in.Labels {
		bytes += int64(len(l.Text))
	}
	for _, c := range []struct {
		resource      string
		actual, limit int64
	}{
		{"nodes", int64(len(in.Boxes)), int64(limits.MaxNodes)},
		{"edges", int64(len(in.Routes)), int64(limits.MaxEdges)},
		{"text bytes", bytes, int64(limits.MaxTextBytes)},
	} {
		if c.actual > c.limit {
			return &layered.LimitError{Resource: c.resource, Limit: c.limit, Actual: c.actual}
		}
	}
	return railroadAmbiguousOwners(in)
}

func labelOwned(labels []Label, id string) bool {
	for _, l := range labels {
		if l.Owner == id {
			return true
		}
	}
	return false
}

func railroadAmbiguousOwners(in Input) error {
	boxes := make(map[string]struct{}, len(in.Boxes))
	for _, b := range in.Boxes {
		boxes[b.ID] = struct{}{}
	}
	for _, r := range in.Routes {
		if _, ambiguous := boxes[r.ID]; ambiguous {
			return fmt.Errorf("ambiguous box and route owner %q: %w", r.ID, layered.ErrGraph)
		}
	}
	return nil
}

type railroadBuilder struct {
	in       Input
	children map[string][]int
	seen     []bool
	text     map[string]string
}

func railroadRules(in Input) ([]railroad.Rule, error) {
	b := &railroadBuilder{in: in, children: map[string][]int{}, seen: make([]bool, len(in.Boxes)), text: map[string]string{}}
	for i, box := range in.Boxes {
		b.children[box.Parent] = append(b.children[box.Parent], i)
	}
	for _, l := range in.Labels {
		if _, taken := b.text[l.Owner]; !taken {
			b.text[l.Owner] = l.Text
		}
	}
	var rules []railroad.Rule
	for _, i := range b.children[""] {
		rule, err := b.rule(i)
		if err != nil {
			return nil, err
		}
		rules = append(rules, rule)
	}
	return rules, nil
}

func (b *railroadBuilder) rule(i int) (railroad.Rule, error) {
	box := b.in.Boxes[i]
	if box.Shape != ruleShape {
		root, err := b.node(i)
		return railroad.Rule{Root: root}, err
	}
	b.seen[i] = true
	kids := b.children[box.ID]
	if len(kids) != 1 {
		return railroad.Rule{}, railroad.ErrArity
	}
	root, err := b.node(kids[0])
	return railroad.Rule{ID: box.ID, Title: b.displayOf(box), Root: root}, err
}

func (b *railroadBuilder) displayOf(box Box) string {
	if text, ok := b.text[box.ID]; ok {
		return text
	}
	if box.Text != "" {
		return box.Text
	}
	return box.ID
}

func (b *railroadBuilder) node(i int) (*railroad.Node, error) {
	if b.seen[i] {
		return nil, railroad.ErrArity
	}
	b.seen[i] = true
	box := b.in.Boxes[i]
	out := &railroad.Node{ID: box.ID, Kind: railroadKindOf(box.Shape), Text: b.displayOf(box)}
	for _, child := range b.children[box.ID] {
		node, err := b.node(child)
		if err != nil {
			return nil, err
		}
		out.Children = append(out.Children, node)
	}
	return out, nil
}

func railroadKindOf(shape string) railroad.Kind {
	for _, row := range railroadKinds {
		if row.shape == shape {
			return row.kind
		}
	}
	return railroad.KindTerminal
}

func railroadConstants(profile scene.Profile) (railroad.Constants, error) {
	var c railroad.Constants
	for _, row := range []struct {
		name string
		into *int64
	}{
		{"pad_x", &c.PadX}, {"pad_y", &c.PadY}, {"line_height", &c.LineHeight}, {"hsep", &c.Hsep}, {"vsep", &c.Vsep},
		{"arc_radius", &c.ArcRadius}, {"terminal_radius", &c.TerminalRadius}, {"marker_radius", &c.MarkerRadius},
		{"margin", &c.Margin}, {"rule_name_gap", &c.RuleNameGap}, {"rule_end_gap", &c.RuleEndGap},
		{"rule_min_baseline", &c.RuleMinBaseline}, {"rule_min_height", &c.RuleMinHeight},
		{"empty_width", &c.EmptyWidth}, {"empty_height", &c.EmptyHeight},
	} {
		value, ok := layoutConstant(profile, "railroad."+row.name)
		if !ok {
			return railroad.Constants{}, geom.ErrDomain
		}
		*row.into = int64(value)
	}
	return c, nil
}
