package chart

import (
	"errors"
	"strconv"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const (
	vennRootID      = "venn"
	vennTitleID     = "title"
	vennMaxSets     = 3
	vennPixelUnits  = 64
	vennRadiusParts = 4
)

var errVennTooMany = errors.New("venn/too-many-sets: venn diagram has more than three sets")

func vennSetID(i int) string { return "set" + strconv.Itoa(i) }

func vennRegionID(k int) string { return "region" + strconv.Itoa(k) }

func vennLabelID(box string) string { return box + ".label" }

func vennTextID(box string, j int) string { return box + ".t" + strconv.Itoa(j) }

type vennItem struct {
	id, owner, text string
	title           bool
	box             textBox
	rect            geom.Rect
}

type vennBox struct {
	id, parent string
	set        int
	members    []int
	items      []int
	rect       geom.Rect
}

type vennPlan struct {
	v       *chartmodel.Venn
	o       scene.Options
	radius  int64
	steps   vennSteps
	width   int64
	height  int64
	band    int64
	items   []vennItem
	boxes   []vennBox
	circles []vennCircle
	laidOut bool
}

func newVennPlan(m *chartmodel.Chart, o scene.Options) (*vennPlan, error) {
	v := m.Venn
	if len(v.Sets) > vennMaxSets {
		return nil, errVennTooMany
	}
	if err := vennCheckMagnitude(v); err != nil {
		return nil, err
	}
	p := &vennPlan{v: v, o: o}
	root := vennBox{id: vennRootID, set: -1}
	if m.Title != "" {
		root.items = append(root.items, len(p.items))
		p.items = append(p.items, vennItem{id: vennTitleID, owner: vennRootID, text: m.Title, title: true})
	}
	p.boxes = append(p.boxes, root)
	for i, s := range v.Sets {
		p.addBox(vennBox{id: vennSetID(i), parent: vennRootID, set: i}, s.Label, s.Texts)
	}
	for k, r := range v.Regions {
		p.addBox(vennBox{id: vennRegionID(k), parent: vennRootID, set: -1, members: r.Sets}, r.Label, r.Texts)
	}
	return p, nil
}

func vennCheckMagnitude(v *chartmodel.Venn) error {
	for _, s := range v.Sets {
		if err := checkMagnitude(int64(s.Size)); err != nil {
			return err
		}
	}
	for _, o := range v.Overlaps {
		if err := checkMagnitude(int64(o.Value)); err != nil {
			return err
		}
	}
	return nil
}

func (p *vennPlan) addBox(b vennBox, label string, texts []string) {
	if label != "" {
		b.items = append(b.items, len(p.items))
		p.items = append(p.items, vennItem{id: vennLabelID(b.id), owner: b.id, text: label})
	}
	for j, t := range texts {
		b.items = append(b.items, len(p.items))
		p.items = append(p.items, vennItem{id: vennTextID(b.id, j), owner: b.id, text: t})
	}
	p.boxes = append(p.boxes, b)
}

func (p *vennPlan) dumpBoxes() []scene.Box {
	out := make([]scene.Box, len(p.boxes))
	for i, b := range p.boxes {
		out[i] = scene.Box{ID: b.id, Role: scene.RoleNode, Parent: b.parent}
		if p.laidOut {
			out[i].Rect = b.rect
		}
	}
	return out
}

func (p *vennPlan) dumpLabels() []scene.Label {
	out := make([]scene.Label, len(p.items))
	for i, it := range p.items {
		out[i] = scene.Label{ID: it.id, Owner: it.owner, Text: it.text}
		if p.laidOut {
			out[i].Rect = it.rect
			out[i].Lines = it.lines()
		}
	}
	return out
}

func (it vennItem) lines() []string {
	out := make([]string, 0, len(it.box.lines))
	for _, line := range it.box.lines {
		out = append(out, line.Text)
	}
	return out
}

func vennConstants(names ...string) ([]int64, error) {
	out := make([]int64, len(names))
	for i, name := range names {
		value, err := constant(scene.ProfileVector, "venn."+name)
		if err != nil {
			return nil, err
		}
		out[i] = value
	}
	return out, nil
}

func (p *vennPlan) configure(m *chartmodel.Chart) error {
	c, err := vennConstants("width", "height", "acos_iterations", "bisect_iterations", "sqrt3_half_q15")
	if err != nil {
		return err
	}
	widthUnits, heightUnits := c[0], c[1]
	if n, ok := m.Integer("width"); ok {
		widthUnits = n * vennPixelUnits
	}
	if n, ok := m.Integer("height"); ok {
		heightUnits = n * vennPixelUnits
	}
	p.radius = geom.FloorDiv(min(widthUnits, heightUnits), vennRadiusParts*vennPixelUnits) * vennPixelUnits
	p.steps = vennSteps{acos: int(c[2]), bisect: int(c[3]), sqrt3Half: c[4]}
	return nil
}

func (p *vennPlan) measureAll() error {
	for i := range p.items {
		role := measure.RoleLabel
		if p.items[i].title {
			role = measure.RoleTitle
		}
		lines, err := measure.StyledLines(p.items[i].text, int32(p.width), measure.ForRole(role).WithFontFamily(p.o.FontFamily))
		if err != nil {
			return err
		}
		var widest int64
		for _, line := range lines {
			widest = max(widest, int64(line.Width))
		}
		p.items[i].box = textBox{lines: lines, w: widest, h: int64(len(lines)) * int64(role.LineHeightPx()) * vennPixelUnits}
	}
	return nil
}

func (p *vennPlan) arrange() error {
	sizes := make([]int64, len(p.v.Sets))
	for i, s := range p.v.Sets {
		sizes[i] = int64(s.Size)
	}
	largest := vennLargest(sizes)
	radii, err := vennRadii(sizes, largest, p.radius)
	if err != nil {
		return err
	}
	var distance int64
	if len(radii) == 2 {
		distance = vennDistance(radii[0], radii[1], vennTarget(p.overlap(), largest, p.radius), p.steps)
	}
	p.circles = vennCentres(radii, p.radius, distance, p.steps)
	for i := range p.circles {
		p.circles[i].y += p.band
	}
	return nil
}

func (p *vennPlan) overlap() int64 {
	var value int64
	for _, o := range p.v.Overlaps {
		if o.A == 0 && o.B == 1 {
			value = int64(o.Value)
		}
	}
	return value
}

func (p *vennPlan) fit(r rect) rect {
	r.x = Clamp(r.x, 0, max(p.width-r.w, 0))
	r.y = Clamp(r.y, 0, max(p.height-r.h, 0))
	return r
}

func (p *vennPlan) clearEarlierLabels(r rect, id int) rect {
	r.y = max(r.y, p.band)
	for range id {
		next := r.y
		for _, earlier := range p.items[:id] {
			b := earlier.rect
			if vennLabelOverlap(r, b) {
				next = max(next, int64(b.Y)+int64(b.H))
				break
			}
		}
		if next == r.y {
			break
		}
		r.y = next
	}
	return r
}

func vennLabelOverlap(r rect, b geom.Rect) bool {
	return r.w > 0 && r.h > 0 && b.W > 0 && b.H > 0 &&
		r.x < int64(b.X)+int64(b.W) && int64(b.X) < r.x+r.w &&
		r.y < int64(b.Y)+int64(b.H) && int64(b.Y) < r.y+r.h
}

func (p *vennPlan) anchor(b vennBox) (x, y int64, err error) {
	if b.set >= 0 {
		return p.setAnchor(b.set)
	}
	var sx, sy int64
	for _, i := range b.members {
		sx += p.circles[i].x
		sy += p.circles[i].y
	}
	n := int64(len(b.members))
	return geom.FloorDiv(sx, n), geom.FloorDiv(sy, n), nil
}

func (p *vennPlan) setAnchor(set int) (x, y int64, err error) {
	c := p.circles[set]
	if len(p.circles) == 1 {
		return c.x, c.y, nil
	}
	var sx, sy int64
	for i, o := range p.circles {
		if i != set {
			sx += o.x
			sy += o.y
		}
	}
	n := int64(len(p.circles) - 1)
	dx, dy := c.x-geom.FloorDiv(sx, n), c.y-geom.FloorDiv(sy, n)
	length, err := geom.Isqrt(dx*dx + dy*dy)
	if err != nil || length == 0 {
		return c.x, c.y, err
	}
	return c.x + geom.FloorDiv(dx*c.r, 2*length), c.y + geom.FloorDiv(dy*c.r, 2*length), nil
}

func (p *vennPlan) stack(b vennBox) (rect, error) {
	ax, ay, err := p.anchor(b)
	if err != nil {
		return rect{}, err
	}
	var total int64
	for _, id := range b.items {
		total += p.items[id].box.h
	}
	top := ay - geom.FloorDiv(total, 2)
	lo, hi := struct{ x, y int64 }{ax, ay}, struct{ x, y int64 }{ax, ay}
	for _, id := range b.items {
		it := &p.items[id]
		r := p.clearEarlierLabels(p.fit(rect{ax - geom.FloorDiv(it.box.w, 2), top, it.box.w, it.box.h}), id)
		g, err := r.geom()
		if err != nil {
			return rect{}, err
		}
		it.rect = g
		top = r.y + it.box.h
		lo.x, lo.y, hi.x, hi.y = min(lo.x, r.x), min(lo.y, r.y), max(hi.x, r.x+r.w), max(hi.y, r.y+r.h)
	}
	return rect{lo.x, lo.y, hi.x - lo.x, hi.y - lo.y}, nil
}

func (p *vennPlan) placeTitle() error {
	for i := range p.items {
		it := &p.items[i]
		if !it.title {
			continue
		}
		g, err := p.fit(rect{geom.FloorDiv(p.width-it.box.w, 2), 0, it.box.w, it.box.h}).geom()
		it.rect = g
		return err
	}
	return nil
}

func (p *vennPlan) boxRect(b vennBox) (rect, error) {
	if b.id == vennRootID {
		return rect{0, 0, p.width, p.height}, nil
	}
	labels, err := p.stack(b)
	if b.set < 0 {
		return labels, err
	}
	c := p.circles[b.set]
	return rect{c.x - c.r, c.y - c.r, 2 * c.r, 2 * c.r}, err
}

func (p *vennPlan) place() error {
	for _, it := range p.items {
		p.width = max(p.width, it.box.w)
	}
	if err := p.placeTitle(); err != nil {
		return err
	}
	for i := range p.boxes {
		r, err := p.boxRect(p.boxes[i])
		if err != nil {
			return err
		}
		if p.boxes[i].rect, err = r.geom(); err != nil {
			return err
		}
	}
	for _, b := range p.boxes {
		p.width = max(p.width, int64(b.rect.X)+int64(b.rect.W))
		p.height = max(p.height, int64(b.rect.Y)+int64(b.rect.H))
	}
	for _, it := range p.items {
		p.width = max(p.width, int64(it.rect.X)+int64(it.rect.W))
		p.height = max(p.height, int64(it.rect.Y)+int64(it.rect.H))
	}
	root, err := (rect{0, 0, p.width, p.height}).geom()
	if err != nil {
		return err
	}
	p.boxes[0].rect = root
	p.laidOut = true
	return nil
}

func layoutVenn(m *chartmodel.Chart, o scene.Options) (scene.Scene, []diag.Diagnostic, error) {
	p, err := newVennPlan(m, o)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	if err = p.configure(m); err != nil {
		return scene.Scene{}, nil, err
	}
	p.width = 4 * p.radius
	if err = p.measureAll(); err != nil {
		return scene.Scene{}, nil, err
	}
	p.band = p.titleBand()
	p.height = p.width + p.band
	if err = p.arrange(); err != nil {
		return scene.Scene{}, nil, err
	}
	if err = p.place(); err != nil {
		return scene.Scene{}, nil, err
	}
	return p.build()
}

func (p *vennPlan) titleBand() int64 {
	for _, it := range p.items {
		if it.title {
			return it.box.h
		}
	}
	return 0
}

func vennModelSkeleton(m *chartmodel.Chart) (Skeleton, error) {
	p, err := newVennPlan(m, scene.Options{})
	if err != nil {
		return Skeleton{}, err
	}
	return Skeleton{Boxes: p.dumpBoxes(), Labels: p.dumpLabels()}, nil
}
