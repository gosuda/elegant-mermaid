package railroad

import "github.com/gosuda/elegant-mermaid/internal/geom"

type shape struct {
	node        *Node
	kids        []*shape
	offsets     []point
	w, up, down int64
}

func (s *shape) height() int64 { return s.up + s.down }

func (s *shape) centre() int64 { return s.up }

type arity struct{ min, max int }

var arities = [...]arity{
	KindTerminal:    {0, 0},
	KindNonTerminal: {0, 0},
	KindSpecial:     {0, 0},
	KindSequence:    {2, 1 << 30},
	KindChoice:      {2, 1 << 30},
	KindOptional:    {1, 1},
	KindZeroOrMore:  {1, 1},
	KindOneOrMore:   {1, 1},
}

func (l *layouter) measure(n *Node) (*shape, error) {
	if int(n.Kind) >= len(arities) || len(n.Children) < arities[n.Kind].min || len(n.Children) > arities[n.Kind].max {
		return nil, ErrArity
	}
	s := &shape{node: n}
	for _, child := range n.Children {
		kid, err := l.measure(child)
		if err != nil {
			return nil, err
		}
		s.kids = append(s.kids, kid)
	}
	if err := l.size(s); err != nil {
		return nil, err
	}
	if s.w > int64(geom.I32Max) || s.height() > int64(geom.I32Max) {
		return nil, geom.ErrOverflow
	}
	return s, nil
}

func (l *layouter) size(s *shape) error {
	switch s.node.Kind {
	case KindSequence:
		l.sizeSequence(s)
	case KindChoice:
		l.sizeChoice(s)
	case KindOptional, KindZeroOrMore, KindOneOrMore:
		l.sizeWrapper(s)
	default:
		return l.sizeLeaf(s)
	}
	return nil
}

func (l *layouter) sizeLeaf(s *shape) error {
	width, err := l.p.Metric.TextWidth(s.node.Text)
	if err != nil {
		return err
	}
	c := l.k
	height := c.LineHeight + 2*c.PadY
	s.w = int64(width) + 2*c.PadX
	s.up = geom.FloorDiv(height, 2)
	s.down = height - s.up
	return nil
}

func (l *layouter) sizeSequence(s *shape) {
	var x int64
	for _, kid := range s.kids {
		s.offsets = append(s.offsets, point{x: x})
		x += kid.w + l.k.Hsep
		s.up = max(s.up, kid.up)
		s.down = max(s.down, kid.down)
	}
	s.w = x - l.k.Hsep
	for i, kid := range s.kids {
		s.offsets[i].y = s.up - kid.up
	}
}

func (l *layouter) sizeChoice(s *shape) {
	var widest, total int64
	for _, kid := range s.kids {
		widest = max(widest, kid.w)
		total += kid.height() + l.k.Vsep
	}
	total -= l.k.Vsep
	arc := l.k.ArcRadius
	var y int64
	for _, kid := range s.kids {
		s.offsets = append(s.offsets, point{x: 2*arc + geom.FloorDiv(widest-kid.w, 2), y: y})
		y += kid.height() + l.k.Vsep
	}
	s.w = widest + 4*arc
	s.up = geom.FloorDiv(total, 2)
	s.down = total - s.up
}

func (l *layouter) sizeWrapper(s *shape) {
	arc := l.k.ArcRadius
	kid := s.kids[0]
	childY, height := 2*arc, kid.height()+2*arc
	switch s.node.Kind {
	case KindZeroOrMore:
		height += 2 * arc
	case KindOneOrMore:
		childY = 0
	}
	s.offsets = []point{{x: 2 * arc, y: childY}}
	s.w = kid.w + 4*arc
	s.up = childY + kid.up
	s.down = height - s.up
}
