package scene

import (
	"errors"
	"fmt"
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/geom"
)

type Clause struct {
	ID      string
	Message string
}

var (
	ClauseCanvas = Clause{"canvas", "box outside canvas"}

	ClauseExclusiveSiblings = Clause{"exclusive-siblings", "exclusive sibling boxes overlap"}

	ClauseParent = Clause{"parent", "box outside its parent"}

	ClauseOrthogonal = Clause{"orthogonal", "orthogonal route has a diagonal segment"}

	ClausePorts = Clause{"ports", "route end is off its box boundary"}

	ClauseRouteClearance = Clause{"route-clearance", "route crosses an exclusive box"}

	ClauseLabelClearance = Clause{"label-clearance", "label overlaps an exclusive box"}

	ClauseFrameClearance = Clause{"frame-clearance", "group frame overlaps a foreign box or label"}
)

var ErrMalformed = errors.New("scene: malformed dump")

type MalformedError struct {
	Reason string
}

func (e *MalformedError) Error() string {
	return "malformed layout dump: " + e.Reason
}

func (e *MalformedError) Unwrap() error { return ErrMalformed }

func malformedf(format string, args ...any) error {
	return &MalformedError{Reason: fmt.Sprintf(format, args...)}
}

func (d *Dump) WellFormed() error {
	_, err := d.buildIndex()
	return err
}

type index struct {
	boxes  map[string]*Box
	routes map[string]*Route
	labels map[string]*Label
	anc    map[string][]string
}

func (d *Dump) buildIndex() (*index, error) {
	ix := &index{
		boxes:  make(map[string]*Box, len(d.Boxes)),
		routes: make(map[string]*Route, len(d.Routes)),
		labels: make(map[string]*Label, len(d.Labels)),
		anc:    make(map[string][]string, len(d.Boxes)),
	}
	if err := checkCanvas(d.Canvas); err != nil {
		return nil, err
	}
	if err := ix.addUnique(d); err != nil {
		return nil, err
	}
	if err := ix.checkRelations(d); err != nil {
		return nil, err
	}
	if err := d.checkShapes(); err != nil {
		return nil, err
	}
	for i := range d.Boxes {
		ix.anc[d.Boxes[i].ID] = ix.ancestors(d.Boxes[i].ID)
	}
	return ix, nil
}

func (ix *index) addUnique(d *Dump) error {
	for i := range d.Boxes {
		b := &d.Boxes[i]
		if _, dup := ix.boxes[b.ID]; dup {
			return malformedf("box id %s appears twice", b.ID)
		}
		ix.boxes[b.ID] = b
	}
	for i := range d.Routes {
		r := &d.Routes[i]
		if _, dup := ix.routes[r.ID]; dup {
			return malformedf("route id %s appears twice", r.ID)
		}
		ix.routes[r.ID] = r
	}
	for i := range d.Labels {
		l := &d.Labels[i]
		if _, dup := ix.labels[l.ID]; dup {
			return malformedf("label id %s appears twice", l.ID)
		}
		ix.labels[l.ID] = l
	}
	return nil
}

func (ix *index) checkRelations(d *Dump) error {
	for i := range d.Routes {
		r := &d.Routes[i]
		for _, end := range [...]string{r.From, r.To} {
			if _, ok := ix.boxes[end]; !ok {
				return malformedf("route %s names unknown box %s", r.ID, end)
			}
		}
	}
	for i := range d.Labels {
		if l := &d.Labels[i]; !ix.ownerExists(l.Owner) {
			return malformedf("label %s has unknown owner %s", l.ID, l.Owner)
		}
	}
	for i := range d.Boxes {
		if err := ix.checkParent(&d.Boxes[i]); err != nil {
			return err
		}
	}
	return nil
}

func (ix *index) ownerExists(owner string) bool {
	_, isRoute := ix.routes[owner]
	_, isBox := ix.boxes[owner]
	return isRoute || isBox
}

func (ix *index) checkParent(b *Box) error {
	if b.Parent == "" {
		return nil
	}
	if _, ok := ix.boxes[b.Parent]; !ok {
		return malformedf("box %s has unknown parent %s", b.ID, b.Parent)
	}
	if slices.Contains(ix.ancestors(b.ID), b.ID) {
		return malformedf("box %s is its own ancestor", b.ID)
	}
	return nil
}

func (ix *index) ancestors(id string) []string {
	var out []string
	for cur := ix.boxes[id]; cur != nil && cur.Parent != "" && len(out) < len(ix.boxes); cur = ix.boxes[cur.Parent] {
		out = append(out, cur.Parent)
	}
	return out
}

func (ix *index) ancestorsOf(id string) []string {
	return ix.anc[id]
}

func (d *Dump) checkShapes() error {
	for i := range d.Boxes {
		if err := checkRect("box "+d.Boxes[i].ID, d.Boxes[i].Rect); err != nil {
			return err
		}
	}
	for i := range d.Labels {
		if err := checkRect("label "+d.Labels[i].ID, d.Labels[i].Rect); err != nil {
			return err
		}
	}
	for i := range d.Routes {
		for _, p := range d.Routes[i].Points {
			if !pointWithinLimit(p) {
				return malformedf("route %s has a coordinate beyond the limit", d.Routes[i].ID)
			}
		}
	}
	return nil
}

func checkRect(name string, r geom.Rect) error {
	right, bottom := int64(r.X)+int64(r.W), int64(r.Y)+int64(r.H)
	if r.W < 0 || r.H < 0 || !fitsInt32(right) || !fitsInt32(bottom) {
		return malformedf("%s has an invalid rectangle", name)
	}
	for _, v := range [4]int64{int64(r.X), int64(r.Y), right, bottom} {
		if v < -geom.CoordLimit || v > geom.CoordLimit {
			return malformedf("%s has a coordinate beyond the limit", name)
		}
	}
	return nil
}

func fitsInt32(v int64) bool {
	return v >= int64(geom.I32Min) && v <= int64(geom.I32Max)
}

func pointWithinLimit(p geom.Point) bool {
	return int64(p.X) >= -geom.CoordLimit && int64(p.X) <= geom.CoordLimit &&
		int64(p.Y) >= -geom.CoordLimit && int64(p.Y) <= geom.CoordLimit
}

func checkCanvas(s geom.Size) error {
	return checkRect("canvas", geom.Rect{W: s.W, H: s.H})
}

type clauseTest func(*validator) (bool, error)

var clauseOrder = [...]struct {
	clause Clause
	test   clauseTest
}{
	{ClauseCanvas, (*validator).canvasOK},
	{ClauseExclusiveSiblings, (*validator).exclusiveSiblingsOK},
	{ClauseParent, (*validator).parentOK},
	{ClauseOrthogonal, (*validator).orthogonalOK},
	{ClausePorts, (*validator).portsOK},
	{ClauseRouteClearance, (*validator).routeClearanceOK},
	{ClauseLabelClearance, (*validator).labelClearanceOK},
	{ClauseFrameClearance, (*validator).frameClearanceOK},
}

type validator struct {
	d  *Dump
	ix *index
}

func (d *Dump) Validate() (Clause, bool, error) {
	ix, err := d.buildIndex()
	if err != nil {
		return Clause{}, false, err
	}
	v := &validator{d: d, ix: ix}
	for _, entry := range clauseOrder {
		ok, err := entry.test(v)
		if err != nil {
			return Clause{}, false, err
		}
		if !ok {
			return entry.clause, true, nil
		}
	}
	return Clause{}, false, nil
}

func (d *Dump) Check() (bool, error) {
	_, failed, err := d.Validate()
	if err != nil {
		return false, err
	}
	return !failed, nil
}

func (v *validator) canvasOK() (bool, error) {
	canvas := geom.Rect{W: v.d.Canvas.W, H: v.d.Canvas.H}
	for i := range v.d.Boxes {
		ok, err := geom.Contains(canvas, v.d.Boxes[i].Rect)
		if err != nil {
			return false, fmt.Errorf("scene: canvas clause: %w", err)
		}
		if !ok {
			return false, nil
		}
	}
	return true, nil
}

func (v *validator) exclusiveSiblingsOK() (bool, error) {
	for i := range v.d.Boxes {
		ok, err := v.siblingsOfBoxOK(i)
		if err != nil || !ok {
			return false, err
		}
	}
	return true, nil
}

func (v *validator) siblingsOfBoxOK(i int) (bool, error) {
	b := &v.d.Boxes[i]
	if !b.Exclusive {
		return true, nil
	}
	for j := i + 1; j < len(v.d.Boxes); j++ {
		c := &v.d.Boxes[j]
		if !c.Exclusive || c.Parent != b.Parent {
			continue
		}
		meet, err := geom.Intersects(b.Rect, c.Rect)
		if err != nil {
			return false, fmt.Errorf("scene: exclusive-siblings clause: %w", err)
		}
		if meet {
			return false, nil
		}
	}
	return true, nil
}

func (v *validator) parentOK() (bool, error) {
	for i := range v.d.Boxes {
		b := &v.d.Boxes[i]
		if b.Parent == "" {
			continue
		}
		ok, err := geom.Contains(v.ix.boxes[b.Parent].Rect, b.Rect)
		if err != nil {
			return false, fmt.Errorf("scene: parent clause: %w", err)
		}
		if !ok {
			return false, nil
		}
	}
	return true, nil
}

func (v *validator) orthogonalOK() (bool, error) {
	for i := range v.d.Routes {
		if r := &v.d.Routes[i]; r.Orthogonal && !geom.IsOrthogonal(r.Points) {
			return false, nil
		}
	}
	return true, nil
}

func (v *validator) portsOK() (bool, error) {
	for i := range v.d.Routes {
		if !routeEndsOnBoundaries(&v.d.Routes[i], v.ix.boxes) {
			return false, nil
		}
	}
	return true, nil
}

func routeEndsOnBoundaries(r *Route, boxes map[string]*Box) bool {
	if len(r.Points) == 0 {
		return false
	}
	return onBoundary(r.Points[0], boxes[r.From].Rect) &&
		onBoundary(r.Points[len(r.Points)-1], boxes[r.To].Rect)
}

func onBoundary(p geom.Point, r geom.Rect) bool {
	x1 := int64(r.X) + int64(r.W)
	y1 := int64(r.Y) + int64(r.H)
	px, py := int64(p.X), int64(p.Y)
	if px < int64(r.X) || px > x1 || py < int64(r.Y) || py > y1 {
		return false
	}
	return px == int64(r.X) || px == x1 || py == int64(r.Y) || py == y1
}

func (v *validator) routeClearanceOK() (bool, error) {
	for i := range v.d.Routes {
		ok, err := v.routeClear(&v.d.Routes[i])
		if err != nil || !ok {
			return false, err
		}
	}
	return true, nil
}

func (v *validator) routeClear(r *Route) (bool, error) {
	scope := v.boxScope(r)
	for j := range v.d.Boxes {
		b := &v.d.Boxes[j]
		_, inScope := scope[b.ID]
		if !b.Exclusive || inScope {
			continue
		}
		hit, err := geom.PolylineHitsRect(r.Points, b.Rect)
		if err != nil {
			return false, fmt.Errorf("scene: route-clearance clause: %w", err)
		}
		if hit {
			return false, nil
		}
	}
	return true, nil
}

func (v *validator) labelClearanceOK() (bool, error) {
	for i := range v.d.Labels {
		ok, err := v.labelClear(&v.d.Labels[i])
		if err != nil || !ok {
			return false, err
		}
	}
	return true, nil
}

func (v *validator) labelClear(l *Label) (bool, error) {
	ownerAnc := v.ownerAncestry(l.Owner)
	for j := range v.d.Boxes {
		b := &v.d.Boxes[j]
		_, isAncestor := ownerAnc[b.ID]
		if !b.Exclusive || isAncestor {
			continue
		}
		meet, err := geom.Intersects(l.Rect, b.Rect)
		if err != nil {
			return false, fmt.Errorf("scene: label-clearance clause: %w", err)
		}
		if meet {
			return false, nil
		}
	}
	return true, nil
}

func (v *validator) frameClearanceOK() (bool, error) {
	for i := range v.d.Boxes {
		g := &v.d.Boxes[i]
		if g.Role != RoleGroup {
			continue
		}
		ok, err := v.frameBoxesClear(g)
		if err == nil && ok {
			ok, err = v.frameLabelsClear(g)
		}
		if err != nil || !ok {
			return false, err
		}
	}
	return true, nil
}

func (v *validator) frameBoxesClear(g *Box) (bool, error) {
	for j := range v.d.Boxes {
		b := &v.d.Boxes[j]
		if b.ID == g.ID || v.isAncestor(g.ID, b.ID) || v.isAncestor(b.ID, g.ID) {
			continue
		}
		meet, err := geom.Intersects(g.Rect, b.Rect)
		if err != nil {
			return false, fmt.Errorf("scene: frame-clearance clause: %w", err)
		}
		if meet {
			return false, nil
		}
	}
	return true, nil
}

func (v *validator) frameLabelsClear(g *Box) (bool, error) {
	for j := range v.d.Labels {
		meet, err := geom.Intersects(g.Rect, v.d.Labels[j].Rect)
		if err != nil {
			return false, fmt.Errorf("scene: frame-clearance clause: %w", err)
		}
		if meet && !strictlyInside(g.Rect, v.d.Labels[j].Rect) {
			return false, nil
		}
	}
	return true, nil
}

func (v *validator) isAncestor(ancestor, id string) bool {
	return slices.Contains(v.ix.ancestorsOf(id), ancestor)
}

func strictlyInside(outer, inner geom.Rect) bool {
	return int64(outer.X) < int64(inner.X) &&
		int64(inner.X)+int64(inner.W) < int64(outer.X)+int64(outer.W) &&
		int64(outer.Y) < int64(inner.Y) &&
		int64(inner.Y)+int64(inner.H) < int64(outer.Y)+int64(outer.H)
}

func (v *validator) boxScope(r *Route) map[string]struct{} {
	scope := map[string]struct{}{r.From: {}, r.To: {}}
	v.addAncestors(scope, r.From)
	v.addAncestors(scope, r.To)
	return scope
}

func (v *validator) ownerAncestry(owner string) map[string]struct{} {
	anc := make(map[string]struct{})
	if r, ok := v.ix.routes[owner]; ok {
		v.addAncestors(anc, r.From)
		v.addAncestors(anc, r.To)
		return anc
	}
	anc[owner] = struct{}{}
	v.addAncestors(anc, owner)
	return anc
}

func (v *validator) addAncestors(dst map[string]struct{}, id string) {
	ancestors := v.ix.ancestorsOf(id)
	for _, a := range ancestors {
		dst[a] = struct{}{}
	}
}
