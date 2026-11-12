package scene

import (
	"errors"
	"fmt"

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
)

var ErrMalformed = errors.New("scene: malformed dump")

type MalformedError struct {
	Reason string
}

func (e *MalformedError) Error() string {
	return "malformed dump: " + e.Reason
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
	if err := ix.addBoxes(d.Boxes); err != nil {
		return nil, err
	}
	if err := checkCanvas(d.Canvas); err != nil {
		return nil, err
	}
	if err := ix.addRoutes(d.Routes); err != nil {
		return nil, err
	}
	if err := ix.addLabels(d.Labels); err != nil {
		return nil, err
	}
	return ix, ix.checkParentChains(d.Boxes)
}

func (ix *index) addBoxes(boxes []Box) error {
	for i := range boxes {
		b := &boxes[i]
		if _, dup := ix.boxes[b.ID]; dup {
			return malformedf("duplicate box id %s", b.ID)
		}
		if err := checkRect("box "+b.ID, b.Rect); err != nil {
			return err
		}
		ix.boxes[b.ID] = b
	}
	return nil
}

func (ix *index) addRoutes(routes []Route) error {
	for i := range routes {
		r := &routes[i]
		if _, dup := ix.routes[r.ID]; dup {
			return malformedf("duplicate route id %s", r.ID)
		}
		if err := ix.checkEndpoint(r, r.From); err != nil {
			return err
		}
		if err := ix.checkEndpoint(r, r.To); err != nil {
			return err
		}
		for _, p := range r.Points {
			if err := checkPoint("route "+r.ID, p); err != nil {
				return err
			}
		}
		ix.routes[r.ID] = r
	}
	return nil
}

func (ix *index) checkEndpoint(r *Route, boxID string) error {
	if _, ok := ix.boxes[boxID]; !ok {
		return malformedf("route %s names unknown box %s", r.ID, boxID)
	}
	return nil
}

func (ix *index) addLabels(labels []Label) error {
	for i := range labels {
		l := &labels[i]
		if _, dup := ix.labels[l.ID]; dup {
			return malformedf("duplicate label id %s", l.ID)
		}
		if !ix.ownerExists(l.Owner) {
			return malformedf("label %s names unknown owner %s", l.ID, l.Owner)
		}
		if err := checkRect("label "+l.ID, l.Rect); err != nil {
			return err
		}
		ix.labels[l.ID] = l
	}
	return nil
}

func (ix *index) ownerExists(owner string) bool {
	_, isRoute := ix.routes[owner]
	_, isBox := ix.boxes[owner]
	return isRoute || isBox
}

func (ix *index) checkParentChains(boxes []Box) error {
	for i := range boxes {
		if _, err := ix.walkAncestors(boxes[i].ID); err != nil {
			return err
		}
	}
	return nil
}

func (ix *index) walkAncestors(id string) ([]string, error) {
	var out []string
	seen := make(map[string]struct{}, len(ix.boxes))
	for cur := ix.boxes[id].Parent; cur != ""; {
		parent, ok := ix.boxes[cur]
		if !ok {
			return nil, malformedf("box %s names unknown parent %s", id, cur)
		}
		if _, dup := seen[cur]; dup {
			return nil, malformedf("box %s has a parent cycle", id)
		}
		seen[cur] = struct{}{}
		out = append(out, cur)
		cur = parent.Parent
	}
	ix.anc[id] = out
	return out, nil
}

func (ix *index) ancestorsOf(id string) []string {
	return ix.anc[id]
}

func checkRect(kind string, r geom.Rect) error {
	if r.W < 0 || r.H < 0 {
		return malformedf("%s has a negative size", kind)
	}
	for _, v := range [4]int64{int64(r.X), int64(r.Y), int64(r.X) + int64(r.W), int64(r.Y) + int64(r.H)} {
		if v < -geom.CoordLimit || v > geom.CoordLimit {
			return malformedf("%s has a coordinate beyond the limit", kind)
		}
	}
	return nil
}
func checkPoint(kind string, p geom.Point) error {
	if int64(p.X) < -geom.CoordLimit || int64(p.X) > geom.CoordLimit ||
		int64(p.Y) < -geom.CoordLimit || int64(p.Y) > geom.CoordLimit {
		return malformedf("%s has a point beyond the limit", kind)
	}
	return nil
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
	v.addAncestors(anc, owner)
	return anc
}

func (v *validator) addAncestors(dst map[string]struct{}, id string) {
	ancestors := v.ix.ancestorsOf(id)
	for _, a := range ancestors {
		dst[a] = struct{}{}
	}
}
