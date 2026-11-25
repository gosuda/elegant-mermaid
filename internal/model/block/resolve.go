package block

import (
	"math"
	"slices"
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/block"
)

const maxSpaceSlots = 1 << 16

type resolver struct {
	src       string
	model     *Model
	diags     []diag.Diagnostic
	database  map[string]*Block
	explicit  map[string]struct{}
	anonymous int
	spaces    int
	slots     int
}

func newResolver(src []byte, document *syn.Start) *resolver {
	pre := syntax.Preprocess(src)
	model := &Model{Root: &Block{Type: "composite", Span: 1, Columns: AutoColumns}}
	var blocks []syntax.ConfigValue
	if pre.HasConfig {
		blocks = append(blocks, pre.Config)
	}
	if pre.HasInit {
		blocks = append(blocks, pre.Init)
	}
	for _, block := range blocks {
		readPadding(model, block)
	}
	r := &resolver{src: string(src), model: model, database: map[string]*Block{}, explicit: map[string]struct{}{}}
	r.collectIDs(document.Document)
	model.Root.ID = r.generate("root", 0)
	return r
}

func (r *resolver) collectIDs(document syn.Document) {
	for _, statement := range document.Statements {
		switch st := statement.Kind.(type) {
		case *syn.NodeStatement:
			r.collectNode(st)
		case *syn.BlockStatement:
			if st.Header != nil {
				r.collectNode(st.Header)
			}
			r.collectIDs(st.Body)
		case *syn.CssClassStatement:
			r.collectList(st.IDs.Text)
		case *syn.StyleStatement:
			r.explicit[strings.TrimSpace(st.IDs.Text)] = struct{}{}
		}
	}
}

func (r *resolver) collectNode(statement *syn.NodeStatement) {
	r.explicit[statement.First.ID.Text] = struct{}{}
	for _, link := range statement.Links {
		r.explicit[link.Node.ID.Text] = struct{}{}
	}
}

func (r *resolver) collectList(ids string) {
	for id := range strings.SplitSeq(ids, ",") {
		r.explicit[strings.TrimSpace(id)] = struct{}{}
	}
}

func (r *resolver) generate(prefix string, ordinal int) string {
	wanted := prefix + strconv.Itoa(ordinal)
	candidate := wanted
	for suffix := 1; ; suffix++ {
		if _, taken := r.explicit[candidate]; !taken {
			r.explicit[candidate] = struct{}{}
			return candidate
		}
		candidate = wanted + "~" + strconv.Itoa(suffix)
	}
}

func (r *resolver) issue(code, message string, span source.Span) {
	r.diags = append(r.diags, syn.Diagnostic(code, message, span))
}

func clamp(text string) int32 {
	value, err := strconv.ParseInt(text, 10, 64)
	if err != nil || value > math.MaxInt32 {
		return math.MaxInt32
	}
	return int32(value)
}

func (r *resolver) document(parent *Block, document syn.Document) {
	reference := AutoColumns
	for _, statement := range document.Statements {
		if st, ok := statement.Kind.(*syn.ColumnsStatement); ok {
			reference = clamp(st.Token.Text)
			break
		}
	}
	for _, statement := range document.Statements {
		r.statement(parent, statement.Kind, reference)
	}
}

func (r *resolver) statement(parent *Block, kind syn.StatementKind, reference int32) {
	switch st := kind.(type) {
	case *syn.ColumnsStatement:
		parent.Columns = clamp(st.Token.Text)
	case *syn.SpaceStatement:
		r.space(parent, st)
	case *syn.NodeStatement:
		r.nodeStatement(parent, st, reference)
	case *syn.BlockStatement:
		r.composite(parent, st, reference)
	case *syn.ClassDefStatement:
		r.classDef(st)
	case *syn.CssClassStatement:
		r.applyClass(st)
	case *syn.StyleStatement:
		r.applyStyle(st)
	}
}

func (r *resolver) space(parent *Block, st *syn.SpaceStatement) {
	count := min(clamp(st.Token.Text), int32(maxSpaceSlots-r.slots))
	ordinal := r.spaces
	template := r.generate("space", ordinal)
	r.spaces++
	for slot := range count {
		child := &Block{ID: template + "-" + strconv.Itoa(int(slot)), Type: "space", Span: 1, IDSpan: st.Token.Span}
		r.database[child.ID] = child
		parent.Children = append(parent.Children, child)
	}
	r.slots += int(count)
}

func (r *resolver) nodeBlock(node syn.Node, size *syn.Token) *Block {
	block := &Block{ID: node.ID.Text, Type: "na", Span: 1, IDSpan: node.ID.Span, Columns: AutoColumns}
	if size != nil {
		block.Span = clamp(size.Text)
		block.SizeSpan = size.Span
	}
	if node.Shape != nil {
		block.Type = shapeType(node.Shape)
		block.Label = syntax.DecodeEntities(node.Shape.Label.Text)
		for _, dir := range node.Shape.Dirs {
			block.Directions = append(block.Directions, dir.Text)
		}
	}
	if block.Label == "" {
		block.Label = block.ID
	}
	return block
}

var shapeTypes = map[string]string{
	"[]": "square", "()": "round", "(())": "circle", ">]": "rect_left_inv_arrow", "{}": "diamond",
	"{{}}": "hexagon", "([])": "stadium", "[[]]": "subroutine", "[()]": "cylinder", "((()))": "doublecircle",
	"[//]": "lean_right", "[\\\\]": "lean_left", "[/\\]": "trapezoid", "[\\/]": "inv_trapezoid", "<[]>": "block_arrow",
}

func shapeType(shape *syn.NodeShapeNLabel) string {
	if name, ok := shapeTypes[shape.Open.Text+shape.Close.Text]; ok {
		return name
	}
	return "na"
}

func (r *resolver) place(parent, block *Block) {
	existing := r.database[block.ID]
	if existing == nil {
		r.database[block.ID] = block
		parent.Children = append(parent.Children, block)
		return
	}
	if existing.Type == "composite" || existing.Type == "space" {
		return
	}
	if block.Type != "na" {
		existing.Type = block.Type
	}
	if block.Label != block.ID {
		existing.Label = block.Label
	}
}

func (r *resolver) checkWidth(block *Block, reference int32) {
	if reference > 0 && block.SizeSpan != (source.Span{}) && block.Span > reference {
		r.issue(codeWidthExceeds, "block "+block.ID+" width "+strconv.Itoa(int(block.Span))+" exceeds configured column width "+strconv.Itoa(int(reference)), block.SizeSpan)
	}
}

func (r *resolver) nodeStatement(parent *Block, st *syn.NodeStatement, reference int32) {
	first := r.nodeBlock(st.First, st.Size)
	r.checkWidth(first, reference)
	r.place(parent, first)
	previous := first.ID
	for _, link := range st.Links {
		target := r.nodeBlock(link.Node, nil)
		r.place(parent, target)
		resolved := edge(previous, target.ID, link.Link)
		resolved.StatementSpan = st.Span
		r.model.Edges = append(r.model.Edges, resolved)
		previous = target.ID
	}
}

func (r *resolver) composite(parent *Block, st *syn.BlockStatement, reference int32) {
	block := &Block{Type: "composite", Span: 1, Columns: AutoColumns}
	if st.Header != nil {
		named := r.nodeBlock(st.Header.First, st.Header.Size)
		block.ID, block.Label, block.Span, block.SizeSpan, block.IDSpan = named.ID, named.Label, named.Span, named.SizeSpan, named.IDSpan
		r.checkWidth(block, reference)
	} else {
		block.ID = r.generate("block", r.anonymous)
		r.anonymous++
	}
	if r.database[block.ID] == nil {
		r.database[block.ID] = block
		parent.Children = append(parent.Children, block)
	}
	r.document(block, st.Body)
}

func edge(start, end string, link syn.Link) Edge {
	spelling := strings.TrimSpace(link.End.Text)
	e := Edge{Start: start, End: end, Span: link.Span, Thickness: "normal", Pattern: "solid", ArrowStart: "arrow_open"}
	if link.Label != nil {
		e.Label = syntax.DecodeEntities(link.Label.Text)
	}
	if strings.Contains(spelling, "==") {
		e.Thickness = "thick"
	}
	if strings.Contains(spelling, ".-") {
		e.Pattern = "dotted"
	}
	e.ArrowEnd = arrowEnd(spelling)
	e.ArrowStart = arrowStart(spelling)
	return e
}

func arrowEnd(spelling string) string {
	switch spelling[len(spelling)-1] {
	case 'x':
		return "arrow_cross"
	case 'o':
		return "arrow_circle"
	case '>':
		return "arrow_point"
	}
	return ""
}

func arrowStart(spelling string) string {
	switch spelling[0] {
	case 'x':
		return "arrow_cross"
	case 'o':
		return "arrow_circle"
	case '<':
		return "arrow_point"
	}
	return "arrow_open"
}

func (r *resolver) classDef(st *syn.ClassDefStatement) {
	id := strings.TrimSpace(st.ID.Text)
	i := slices.IndexFunc(r.model.Classes, func(c ClassDef) bool { return c.ID == id })
	if i < 0 {
		r.model.Classes = append(r.model.Classes, ClassDef{ID: id})
		i = len(r.model.Classes) - 1
	}
	class := &r.model.Classes[i]
	for attribute := range strings.SplitSeq(strings.TrimSpace(st.Style.Text), ",") {
		fixed := strings.TrimSpace(removeFirstSemicolon(attribute))
		if strings.Contains(attribute, "color") {
			text := strings.Replace(fixed, "fill", "bgFill", 1)
			class.TextStyles = append(class.TextStyles, strings.Replace(text, "color", "fill", 1))
		}
		class.Styles = append(class.Styles, fixed)
	}
}

func removeFirstSemicolon(text string) string {
	if i := strings.IndexByte(text, ';'); i >= 0 {
		return text[:i] + text[i+1:]
	}
	return text
}

func (r *resolver) applyClass(st *syn.CssClassStatement) {
	class := strings.TrimSpace(st.Class.Text)
	for id := range strings.SplitSeq(st.IDs.Text, ",") {
		id = strings.TrimSpace(id)
		block := r.database[id]
		if block == nil {
			block = &Block{ID: id, Type: "na", Span: 1, Columns: AutoColumns}
			r.database[id] = block
		}
		block.Classes = append(block.Classes, class)
	}
}

func (r *resolver) applyStyle(st *syn.StyleStatement) {
	text := strings.TrimSpace(st.Style.Text)
	if text == "" {
		return
	}
	block := r.database[strings.TrimSpace(st.IDs.Text)]
	if block == nil {
		r.issue(codeStyleTarget, "style references unknown block "+strings.TrimSpace(st.IDs.Text), st.IDs.Span)
		return
	}
	block.Styles = strings.Split(text, ",")
}
