package layout

import (
	"math"
	"slices"
	"strconv"
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	ermodel "github.com/gosuda/elegant-mermaid/internal/model/er"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func FromER(m *ermodel.Model, profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic) {
	options = resolveOptions(options)
	direction, _ := scene.ParseDirection(m.Direction)
	in := Input{Kind: "er", Profile: profile, Direction: direction, Options: options}
	ids := erGroupIDs(m)
	for i := range m.Entities {
		entity := &m.Entities[i]
		if erHiddenByGroup(m, entity.ID) {
			continue
		}
		in.Boxes = append(in.Boxes, Box{
			ID:        entity.ID,
			Role:      scene.RoleNode,
			Shape:     "erBox",
			Parent:    erParentID(entity.Parent, ids),
			Exclusive: true,
			Text:      erTableText(entity),
		})
	}
	erAppendGroups(&in, m, ids)
	erAppendRelationships(&in, m, ids)
	return in, nil
}

func erGroupIDs(m *ermodel.Model) []string {
	ids := make([]string, 0, len(m.Groups))
	for index, group := range m.Groups {
		id := group.ID
		ordinal := index
		for erGroupIDTaken(m, ids, id, group.ID) {
			id = group.ID + ".group" + strconv.Itoa(ordinal)
			ordinal++
		}
		ids = append(ids, id)
	}
	return ids
}

func erGroupIDTaken(m *ermodel.Model, ids []string, id, own string) bool {
	if slices.Contains(ids, id) {
		return true
	}
	if slices.ContainsFunc(m.Entities, func(e ermodel.Entity) bool { return e.ID == id && id != own }) {
		return true
	}
	return slices.ContainsFunc(m.Groups, func(g ermodel.Group) bool { return g.ID == id && id != own })
}

func erHiddenByGroup(m *ermodel.Model, id string) bool {
	return slices.ContainsFunc(m.Groups, func(g ermodel.Group) bool { return g.ID == id })
}

func erParentID(parent int, ids []string) string {
	if parent >= 0 && parent < len(ids) {
		return ids[parent]
	}
	return ""
}

func erAppendGroups(in *Input, m *ermodel.Model, ids []string) {
	for i := range m.Groups {
		group := &m.Groups[i]
		parent := erParentID(group.Parent, ids)
		in.Boxes = append(in.Boxes, Box{
			ID:        ids[i],
			Role:      scene.RoleGroup,
			Parent:    parent,
			Exclusive: false,
			Text:      erLabelLines(group.Label),
			Direction: group.Direction,
		})
		in.Groups = append(in.Groups, Group{ID: ids[i], DirectionSpan: group.DirectionSpan})
	}
}

func erTargetID(m *ermodel.Model, target ermodel.Target, ids []string) string {
	if target.Group {
		if target.Index < len(ids) {
			return ids[target.Index]
		}
		return ""
	}
	if target.Index >= len(m.Entities) {
		return ""
	}
	id := m.Entities[target.Index].ID
	for i := len(m.Groups) - 1; i >= 0; i-- {
		if m.Groups[i].ID == id {
			if i < len(ids) {
				return ids[i]
			}
			return ""
		}
	}
	return id
}

func erAppendRelationships(in *Input, m *ermodel.Model, ids []string) {
	routeIDs := allocateRouteIDs(in.Boxes, len(m.Relationships))
	for i := range m.Relationships {
		relation := &m.Relationships[i]
		id := routeIDs[i]
		if relation.Label != "" {
			in.Labels = append(in.Labels, Label{ID: id + ".label", Owner: id, Role: scene.TextRoleLabel, Text: erLabelLines(relation.Label)})
		}
		line := "dashed"
		if relation.Identifying {
			line = "normal"
		}
		in.Routes = append(in.Routes, Route{
			ID:          id,
			From:        erTargetID(m, relation.FromTarget, ids),
			To:          erTargetID(m, relation.ToTarget, ids),
			Orthogonal:  true,
			MarkerStart: relation.MarkerStart,
			MarkerEnd:   relation.MarkerEnd,
			Line:        line,
			MinLength:   1,
		})
	}
}

func erLabelLines(text string) string {
	var out strings.Builder
	out.Grow(len(text))
	for i := 0; i < len(text); {
		c, size := utf8.DecodeRuneInString(text[i:])
		switch {
		case c == '\r' && strings.HasPrefix(text[i+size:], "\n"):
		case c == '\r' || c == '\n':
			out.WriteString("<br/>")
		default:
			out.WriteString(text[i : i+size])
		}
		i += size
	}
	return out.String()
}

func erTableText(entity *ermodel.Entity) string {
	rows := entity.TableRows()
	encoded := make([]string, len(rows))
	for i, row := range rows {
		fields := make([]string, len(row))
		for j, field := range row {
			fields[j] = erEncodeField(field)
		}
		encoded[i] = strings.Join(fields, "|")
	}
	return erEncodeField(entity.DisplayName()) + "<br/><br/>" + strings.Join(encoded, "<br/>")
}

func erEncodeField(text string) string {
	var out strings.Builder
	out.Grow(len(text))
	for i := 0; i < len(text); {
		c, size := utf8.DecodeRuneInString(text[i:])
		if length, ok := erBreakLength(c, text[i+size:]); ok {
			out.WriteString("\\n")
			i += size + length
			continue
		}
		switch c {
		case '\\':
			out.WriteString("\\\\")
		case '|':
			out.WriteString("\\p")
		case '<':
			out.WriteString("\\l")
		case '\t':
			out.WriteString("\\t")
		case '\n':
			out.WriteString("\\n")
		default:
			out.WriteString(text[i : i+size])
		}
		i += size
	}
	return out.String()
}

func erBreakLength(c rune, tail string) (int, bool) {
	if c != '<' {
		return 0, false
	}
	for _, ending := range []string{"br>", "br/>", "br />"} {
		if len(tail) >= len(ending) && strings.EqualFold(tail[:len(ending)], ending) {
			return len(ending), true
		}
	}
	return 0, false
}

func erDecodeField(text string) string {
	var out strings.Builder
	out.Grow(len(text))
	for i := 0; i < len(text); {
		c, size := utf8.DecodeRuneInString(text[i:])
		if c != '\\' {
			out.WriteString(text[i : i+size])
			i += size
			continue
		}
		next, nextSize := utf8.DecodeRuneInString(text[i+size:])
		if nextSize == 0 {
			out.WriteByte('\\')
			i += size
			continue
		}
		switch next {
		case 'n':
			out.WriteByte('\n')
		case 't':
			out.WriteByte('\t')
		case 'p':
			out.WriteByte('|')
		case 'l':
			out.WriteByte('<')
		default:
			out.WriteString(text[i+size : i+size+nextSize])
		}
		i += size + nextSize
	}
	return out.String()
}

func erConstant(profile scene.Profile, name string) int32 {
	prefix := "vector.er."
	if profile == scene.ProfileCell {
		prefix = "cell.er."
	}
	for _, c := range gen.LayoutConst {
		if c.Name == prefix+name {
			return c.Value
		}
	}
	return 0
}

func erMetric(profile scene.Profile) measure.Metric {
	if profile == scene.ProfileCell {
		return measure.CellMetric()
	}
	return measure.ForRole(measure.RoleLabel)
}

func erLineHeight(profile scene.Profile) int32 {
	if profile == scene.ProfileCell {
		return 1
	}
	return measure.RoleLabel.LineHeightPx() * 64
}

func erPieceWidth(piece string, profile scene.Profile) (int32, error) {
	lines, err := measure.StyledLines(piece, math.MaxInt32, erMetric(profile))
	if err != nil {
		return 0, err
	}
	var width int32
	for i := range lines {
		width = max(width, lines[i].Width)
	}
	return width, nil
}

func erTextWidth(text string, profile scene.Profile) (int32, error) {
	var width int64
	for piece := range strings.SplitSeq(text, "\n") {
		w, err := erPieceWidth(piece, profile)
		if err != nil {
			return 0, err
		}
		width = max(width, int64(w))
	}
	return checkedI32(width)
}

type erColumn struct {
	index int
	width int32
}

type erTable struct {
	heading       string
	rows          [][]string
	columns       []erColumn
	rowHeights    []int32
	headingHeight int32
	paddingX      int32
	paddingY      int32
	separator     int32
	profile       scene.Profile
}

func erNewTable(text string, profile scene.Profile) (*erTable, error) {
	heading, attributes, _ := strings.Cut(text, "<br/><br/>")
	heading = erDecodeField(heading)
	var rows [][]string
	if attributes != "" {
		for line := range strings.SplitSeq(attributes, "<br/>") {
			fields := strings.Split(line, "|")
			for i := range fields {
				fields[i] = erDecodeField(fields[i])
			}
			rows = append(rows, fields)
		}
	}
	columns, err := erColumnWidths(rows, profile)
	if err != nil {
		return nil, err
	}
	rowHeights := make([]int32, len(rows))
	for i := range rows {
		if rowHeights[i], err = erRowHeight(rows[i], profile); err != nil {
			return nil, err
		}
	}
	headingHeight, err := erRowHeight([]string{heading}, profile)
	if err != nil {
		return nil, err
	}
	separator := int32(0)
	if profile == scene.ProfileCell {
		separator = 1
	}
	return &erTable{
		heading:       heading,
		rows:          rows,
		columns:       columns,
		rowHeights:    rowHeights,
		headingHeight: headingHeight,
		paddingX:      erConstant(profile, "padding_x"),
		paddingY:      erConstant(profile, "padding_y"),
		separator:     separator,
		profile:       profile,
	}, nil
}

func (t *erTable) width() (int32, error) {
	var columns, gaps int64
	for _, column := range t.columns {
		columns += int64(column.width)
	}
	gaps = int64(max(0, len(t.columns)-1)) * int64(t.paddingX)
	headingWidth, err := erTextWidth(t.heading, t.profile)
	if err != nil {
		return 0, err
	}
	width := max(columns+gaps, int64(headingWidth))
	return checkedI32(width + 2*int64(t.paddingX))
}

func (t *erTable) height() (int32, error) {
	var rows int64
	for _, h := range t.rowHeights {
		rows += int64(h)
	}
	rows = max(rows, int64(erLineHeight(t.profile)))
	return checkedI32(int64(t.headingHeight) + rows + int64(t.separator) + 2*int64(t.paddingY))
}

func erTableSize(text string, profile scene.Profile) (geom.Size, error) {
	table, err := erNewTable(text, profile)
	if err != nil {
		return geom.Size{}, err
	}
	width, err := table.width()
	if err != nil {
		return geom.Size{}, err
	}
	height, err := table.height()
	if err != nil {
		return geom.Size{}, err
	}
	return geom.Size{
		W: max(width, erConstant(profile, "min_width")),
		H: max(height, erConstant(profile, "min_height")),
	}, nil
}

func checkedI32(v int64) (int32, error) {
	if v > math.MaxInt32 || v < math.MinInt32 {
		return 0, geom.ErrOverflow
	}
	return int32(v), nil
}

func erColumnWidths(rows [][]string, profile scene.Profile) ([]erColumn, error) {
	var widths [4]int32
	for _, row := range rows {
		for i, field := range row {
			if i >= len(widths) {
				break
			}
			w, err := erTextWidth(field, profile)
			if err != nil {
				return nil, err
			}
			widths[i] = max(widths[i], w)
		}
	}
	var out []erColumn
	for i, width := range widths {
		if i >= 2 && width == 0 {
			continue
		}
		out = append(out, erColumn{index: i, width: width})
	}
	return out, nil
}

func erRowHeight(row []string, profile scene.Profile) (int32, error) {
	lines := 1
	for _, field := range row {
		lines = max(lines, strings.Count(field, "\n")+1)
	}
	return checkedI32(int64(lines) * int64(erLineHeight(profile)))
}

func layoutER(in Input) (scene.Scene, []diag.Diagnostic, error) {
	input, err := erFamilyInput(in)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	options := resolveOptions(in.Options)
	options.Profile, options.Direction = in.Profile, in.Direction
	var budget bool
	s, err := layered.LayoutFamily(input, layered.Options{Scene: options, BudgetExhausted: &budget})
	var ds []diag.Diagnostic
	if budget {
		ds = append(ds, diag.Diagnostic{Code: "layout/budget-exhausted", Severity: diag.SeverityInfo, Message: "layout stopped at its iteration cap"})
	}
	if err != nil {
		return s, ds, err
	}
	if err := erTableScene(in, &s); err != nil {
		return s, ds, err
	}
	diag.Sort(ds)
	return s, ds, nil
}

func erFamilyInput(in Input) (layered.Input, error) {
	input := familyInput(in)
	input.Sizes = make([]geom.Size, len(in.Boxes))
	for i := range in.Boxes {
		if in.Boxes[i].Shape != "erBox" {
			continue
		}
		size, err := erTableSize(in.Boxes[i].Text, in.Profile)
		if err != nil {
			return layered.Input{}, err
		}
		input.Sizes[i] = size
	}
	return input, nil
}

func erTableScene(in Input, s *scene.Scene) error {
	for _, group := range s.Groups {
		box, ok := erBoxByID(in, group.Owner)
		if !ok || box.Shape != "erBox" {
			continue
		}
		rect, ok := sceneBoxRect(s, group.Owner)
		if !ok {
			continue
		}
		items, err := erTableItems(box.Text, rect, in.Profile)
		if err != nil {
			return err
		}
		group.Items = items
	}
	return nil
}

func erBoxByID(in Input, id string) (Box, bool) {
	for i := range in.Boxes {
		if in.Boxes[i].ID == id {
			return in.Boxes[i], true
		}
	}
	return Box{}, false
}

func sceneBoxRect(s *scene.Scene, id string) (geom.Rect, bool) {
	for i := range s.Boxes {
		if s.Boxes[i].ID == id {
			return s.Boxes[i].Rect, true
		}
	}
	return geom.Rect{}, false
}

func erTableItems(text string, rect geom.Rect, profile scene.Profile) ([]scene.Primitive, error) {
	table, err := erNewTable(text, profile)
	if err != nil {
		return nil, err
	}
	shapes := []scene.Primitive{&scene.Rect{Shape: scene.Shape{Style: "node"}, Rect: rect}}
	top := rect.Y + table.paddingY
	heading, err := erTextItem(table.heading, geom.Rect{X: rect.X, Y: top, W: rect.W, H: table.headingHeight}, scene.AlignMiddle, profile)
	if err != nil {
		return nil, err
	}
	texts := []scene.Primitive{heading}
	divider := top + table.headingHeight
	right := rect.X + rect.W - table.separator
	shapes = append(shapes, erRule(geom.Point{X: rect.X, Y: divider}, geom.Point{X: right, Y: divider}))
	if err := erAttributeItems(table, rect, divider, &shapes, &texts); err != nil {
		return nil, err
	}
	return append(shapes, texts...), nil
}

func erRule(start, end geom.Point) scene.Primitive {
	return &scene.Polyline{Shape: scene.Shape{Style: "rule"}, Points: []geom.Point{start, end}}
}

func erTextItem(text string, rect geom.Rect, align scene.Align, profile scene.Profile) (*scene.Text, error) {
	var lines [][]scene.Run
	for piece := range strings.SplitSeq(text, "\n") {
		runs, err := erRunLines(piece, profile)
		if err != nil {
			return nil, err
		}
		lines = append(lines, runs...)
	}
	return &scene.Text{Rect: rect, Role: scene.TextRoleLabel, Size: 14, Align: align, Style: "text", Lines: lines}, nil
}

func erRunLines(piece string, profile scene.Profile) ([][]scene.Run, error) {
	lines, err := measure.StyledLines(piece, math.MaxInt32, erMetric(profile))
	if err != nil {
		return nil, err
	}
	out := make([][]scene.Run, 0, len(lines))
	for i := range lines {
		runs := make([]scene.Run, len(lines[i].Runs))
		for j, run := range lines[i].Runs {
			runs[j] = scene.Run{Text: run.Text, Bold: run.Bold, Italic: run.Italic}
		}
		if len(runs) == 0 {
			runs = []scene.Run{{Text: ""}}
		}
		out = append(out, runs)
	}
	if len(out) == 0 {
		return [][]scene.Run{{{Text: ""}}}, nil
	}
	return out, nil
}

func erAttributeItems(table *erTable, rect geom.Rect, divider int32, shapes, texts *[]scene.Primitive) error {
	bottom := rect.Y + rect.H - table.separator
	x := rect.X + table.paddingX
	for pos := range table.columns {
		column := table.columns[pos]
		if err := erAppendColumn(table, column, geom.Point{X: x, Y: divider}, texts); err != nil {
			return err
		}
		x += column.width + table.paddingX
		if pos+1 < len(table.columns) {
			lineX := x - table.paddingX/2
			*shapes = append(*shapes, erRule(geom.Point{X: lineX, Y: divider}, geom.Point{X: lineX, Y: bottom}))
		}
	}
	return nil
}

func erAppendColumn(table *erTable, column erColumn, origin geom.Point, texts *[]scene.Primitive) error {
	y := origin.Y + table.separator
	for i := range table.rows {
		text := ""
		if column.index < len(table.rows[i]) {
			text = table.rows[i][column.index]
		}
		item, err := erTextItem(text, geom.Rect{X: origin.X, Y: y, W: column.width, H: table.rowHeights[i]}, scene.AlignStart, table.profile)
		if err != nil {
			return err
		}
		*texts = append(*texts, item)
		y += table.rowHeights[i]
	}
	return nil
}
