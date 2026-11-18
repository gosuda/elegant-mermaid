package layered

import "math"

type rankSpan struct{ first, last int32 }

type optionalSpan struct {
	span rankSpan
	ok   bool
}

type regionReservation struct {
	group       int
	left, right int32
	span        rankSpan
}

type frameMinima struct{ border, padding, title int32 }

type regionBand struct {
	group       int
	left, right int32
	span        rankSpan
}

type regionConstraints struct {
	widths  []int32
	spans   []optionalSpan
	bands   []regionBand
	origins []int32
}

type localRegionSet struct {
	parent  int
	regions []int
}

func addCoordinates(a, b int32) (int32, error) {
	return coordinate(int64(a) + int64(b))
}

func subtractCoordinates(a, b int32) (int32, error) {
	return coordinate(int64(a) - int64(b))
}

func mergeSpans(a, b optionalSpan) optionalSpan {
	if a.ok && b.ok {
		return optionalSpan{span: rankSpan{first: min(a.span.first, b.span.first), last: max(a.span.last, b.span.last)}, ok: true}
	}
	if a.ok {
		return a
	}
	return b
}

type indexedGroups struct {
	children  [][]int
	order     []int
	byParent  []int
	bandCount int
}

func childForest(parents []int) ([][]int, []int, error) {
	n := len(parents)
	children := make([][]int, n)
	var roots []int
	for child, parent := range parents {
		if parent < 0 {
			roots = append(roots, child)
			continue
		}
		if parent >= n || parent == child {
			return nil, nil, ErrGraph
		}
		children[parent] = append(children[parent], child)
	}
	order, err := groupPreorder(children, roots)
	return children, order, err
}

func groupPreorder(children [][]int, roots []int) ([]int, error) {
	order := make([]int, 0, len(children))
	stack := roots
	for len(stack) > 0 {
		group := stack[len(stack)-1]
		stack = append(stack[:len(stack)-1], children[group]...)
		order = append(order, group)
	}
	if len(order) != len(children) {
		return nil, ErrGraph
	}
	return order, nil
}

func validRegionSet(set localRegionSet, byParent []int) bool {
	return set.parent >= 0 && set.parent < len(byParent) && len(set.regions) > 0 && byParent[set.parent] < 0
}

func validRegion(region, parent int, parents, owner []int) bool {
	return region >= 0 && region < len(parents) && parents[region] == parent && owner[region] < 0
}

func indexRegionSets(parents []int, sets []localRegionSet) ([]int, int, error) {
	n := len(parents)
	owner := make([]int, n)
	byParent := make([]int, n)
	for i := range owner {
		owner[i], byParent[i] = -1, -1
	}
	bands := 0
	for index, set := range sets {
		if !validRegionSet(set, byParent) {
			return nil, 0, ErrGraph
		}
		byParent[set.parent] = index
		for _, region := range set.regions {
			if !validRegion(region, set.parent, parents, owner) {
				return nil, 0, ErrGraph
			}
			owner[region] = index
			bands++
		}
	}
	return byParent, bands, nil
}

func indexGroups(parents []int, sets []localRegionSet) (indexedGroups, error) {
	children, order, err := childForest(parents)
	if err != nil {
		return indexedGroups{}, err
	}
	byParent, bands, err := indexRegionSets(parents, sets)
	if err != nil {
		return indexedGroups{}, err
	}
	return indexedGroups{children: children, order: order, byParent: byParent, bandCount: bands}, nil
}

type regionWorkbook struct {
	indexedGroups
	inset    int32
	widths   []int32
	spans    []optionalSpan
	lefts    []int32
	rights   []int32
	reserved []bool
	origins  []int32
	offsets  []int32
}

func newRegionWorkbook(n int, indexed indexedGroups, inset, minimum int32) *regionWorkbook {
	book := &regionWorkbook{indexedGroups: indexed, inset: inset, widths: make([]int32, n), spans: make([]optionalSpan, n), lefts: make([]int32, n), rights: make([]int32, n), reserved: make([]bool, n), origins: make([]int32, n), offsets: make([]int32, n)}
	for i := range n {
		book.widths[i], book.origins[i] = minimum, inset
		book.lefts[i], book.rights[i] = math.MaxInt32, math.MinInt32
	}
	return book
}

func (book *regionWorkbook) foldReservations(reservations []regionReservation) error {
	for _, reservation := range reservations {
		if err := book.validateReservation(reservation); err != nil {
			return err
		}
		g := reservation.group
		book.lefts[g] = min(book.lefts[g], reservation.left)
		book.rights[g] = max(book.rights[g], reservation.right)
		book.reserved[g] = true
		book.spans[g] = mergeSpans(book.spans[g], optionalSpan{span: reservation.span, ok: true})
	}
	return nil
}

func (book *regionWorkbook) validateReservation(reservation regionReservation) error {
	if reservation.group < 0 || reservation.group >= len(book.widths) || reservation.left > reservation.right || reservation.span.first < 0 || reservation.span.first > reservation.span.last {
		return ErrGraph
	}
	return nil
}

func (book *regionWorkbook) resolveNestedExtents(sets []localRegionSet) error {
	for position := len(book.order) - 1; position >= 0; position-- {
		g := book.order[position]
		if err := book.absorbFootprint(g); err != nil {
			return err
		}
		if err := book.absorbChildren(g); err != nil {
			return err
		}
		if err := book.layOutRegions(g, sets); err != nil {
			return err
		}
	}
	return nil
}

func (book *regionWorkbook) insetWidth(width int32) (int32, error) {
	width, err := addCoordinates(width, book.inset)
	if err != nil {
		return 0, err
	}
	return addCoordinates(width, book.inset)
}

func (book *regionWorkbook) absorbFootprint(g int) error {
	if !book.reserved[g] {
		return nil
	}
	width, err := subtractCoordinates(book.rights[g], book.lefts[g])
	if err != nil {
		return err
	}
	width, err = book.insetWidth(width)
	if err != nil {
		return err
	}
	book.widths[g] = max(book.widths[g], width)
	book.origins[g], err = subtractCoordinates(book.inset, book.lefts[g])
	return err
}

func (book *regionWorkbook) absorbChildren(g int) error {
	span, width := book.spans[g], book.widths[g]
	for _, child := range book.children[g] {
		span = mergeSpans(span, book.spans[child])
		covered, err := book.insetWidth(book.widths[child])
		if err != nil {
			return err
		}
		width = max(width, covered)
	}
	book.spans[g], book.widths[g] = span, width
	return nil
}

func (book *regionWorkbook) layOutRegions(g int, sets []localRegionSet) error {
	index := book.byParent[g]
	if index < 0 {
		return nil
	}
	cursor := book.inset
	for _, region := range sets[index].regions {
		book.offsets[region] = cursor
		next, err := addCoordinates(cursor, book.widths[region])
		if err != nil {
			return err
		}
		cursor = next
	}
	total, err := addCoordinates(cursor, book.inset)
	if err != nil {
		return err
	}
	book.widths[g] = max(book.widths[g], total)
	return nil
}

func (book *regionWorkbook) shareCommonSpans(sets []localRegionSet) {
	for _, g := range book.order {
		index := book.byParent[g]
		if index < 0 {
			continue
		}
		var span optionalSpan
		for _, region := range sets[index].regions {
			span = mergeSpans(span, book.spans[region])
		}
		if !span.ok {
			span = book.spans[g]
		}
		span.ok = true
		for _, region := range sets[index].regions {
			book.spans[region] = span
		}
	}
}

func (book *regionWorkbook) bands(sets []localRegionSet) ([]regionBand, error) {
	bands := make([]regionBand, 0, book.bandCount)
	for _, set := range sets {
		for _, region := range set.regions {
			right, err := addCoordinates(book.offsets[region], book.widths[region])
			if err != nil {
				return nil, err
			}
			if !book.spans[region].ok {
				return nil, ErrGraph
			}
			bands = append(bands, regionBand{group: region, left: book.offsets[region], right: right, span: book.spans[region].span})
		}
	}
	return bands, nil
}

func frameMinimum(minima frameMinima) (int32, int32, error) {
	if minima.border < 0 || minima.padding < 0 || minima.title < 0 {
		return 0, 0, ErrGraph
	}
	inset, err := addCoordinates(minima.border, minima.padding)
	if err != nil {
		return 0, 0, err
	}
	minimum, err := coordinate(2*int64(inset) + int64(minima.title))
	if err != nil {
		return 0, 0, err
	}
	return inset, max(minimum, 1), nil
}

type regionProblem struct {
	parents      []int
	sets         []localRegionSet
	reservations []regionReservation
	minima       frameMinima
}

func solveRegions(problem regionProblem) (regionConstraints, error) {
	inset, minimum, err := frameMinimum(problem.minima)
	if err != nil {
		return regionConstraints{}, err
	}
	indexed, err := indexGroups(problem.parents, problem.sets)
	if err != nil {
		return regionConstraints{}, err
	}
	book := newRegionWorkbook(len(problem.parents), indexed, inset, minimum)
	if err := book.foldReservations(problem.reservations); err != nil {
		return regionConstraints{}, err
	}
	if err := book.resolveNestedExtents(problem.sets); err != nil {
		return regionConstraints{}, err
	}
	book.shareCommonSpans(problem.sets)
	bands, err := book.bands(problem.sets)
	if err != nil {
		return regionConstraints{}, err
	}
	return regionConstraints{widths: book.widths, spans: book.spans, bands: bands, origins: book.origins}, nil
}
