package main

import (
	"cmp"
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"slices"
	"strings"
)

var requiredThemeTokens = []string{"bg", "surface", "fg"}

type kindKeyword struct {
	Text string `json:"text"`
	Case string `json:"case"`
}

type kindInput struct {
	ID       string        `json:"id"`
	Family   string        `json:"family"`
	Keywords []kindKeyword `json:"keywords"`
	Aliases  []string      `json:"aliases"`
}

type layoutConstInput struct {
	Name   string `json:"name"`
	Vector int32  `json:"vector"`
	Cell   int32  `json:"cell"`
}

type glyphJoinInput struct {
	Mask        uint8  `json:"mask"`
	Light       string `json:"light"`
	Heavy       string `json:"heavy"`
	Double      string `json:"double"`
	Rounded     string `json:"rounded"`
	Dotted      string `json:"dotted"`
	Ascii       string `json:"ascii"`
	AsciiDotted string `json:"ascii_dotted"`
}

type scriptInput struct {
	Base string `json:"base"`
	Sup  string `json:"sup"`
	Sub  string `json:"sub"`
}

type cellSymbolInput struct {
	Name    string `json:"name"`
	Unicode string `json:"unicode"`
	Ascii   string `json:"ascii"`
}

type shapeRow struct {
	Name   string `json:"name"`
	Fill   string `json:"fill"`
	Stroke string `json:"stroke"`
	Tint   string `json:"tint"`
	Cell   string `json:"cell"`
}

type textStyleRow struct {
	Name   string `json:"name"`
	Colour string `json:"colour"`
}

type stylesInput struct {
	Shape []shapeRow     `json:"shape"`
	Text  []textStyleRow `json:"text"`
}

type markerInput struct {
	Name   string     `json:"name"`
	Paint  string     `json:"paint"`
	Cell   []string   `json:"cell"`
	Ascii  []string   `json:"ascii"`
	Points [][2]int32 `json:"points"`
	Ref    [2]int32   `json:"ref"`
}

type themeInput struct {
	Name   string            `json:"name"`
	Tokens map[string]string `json:"tokens"`
}

type registryRow struct {
	Code      string   `json:"code"`
	Severity  string   `json:"severity"`
	Summary   string   `json:"summary"`
	Help      string   `json:"help"`
	Rationale string   `json:"rationale"`
	FixSafety string   `json:"fix_safety"`
	Aliases   []string `json:"aliases"`
	Source    string   `json:"source"`
	Status    string   `json:"status"`
	Reason    string   `json:"reason"`
}

type configKeyInput struct {
	Kind  string
	Key   string
	Class string
}

type shapeInput struct {
	ID      string   `json:"id"`
	Family  string   `json:"family"`
	Handler string   `json:"handler"`
	Corner  string   `json:"corner"`
	Aliases []string `json:"aliases"`
}

type entityInput struct {
	Codepoints []uint32 `json:"codepoints"`
}

type entityRow struct {
	Name string
	CPS  []uint32
}

type sourcesInput struct {
	Path   string `json:"path"`
	URL    string `json:"url"`
	SHA256 string `json:"sha256"`
}

type inputs struct {
	root string

	kinds       []kindInput
	layoutConst []layoutConstInput
	glyphJoin   []glyphJoinInput
	scripts     []scriptInput
	cellSymbols []cellSymbolInput
	styles      stylesInput
	markers     []markerInput
	themes      []themeInput
	shapes      []shapeInput

	diagnostics []registryRow
	lintRules   []registryRow
	configKeys  []configKeyInput

	entities []entityRow

	eaw      []byte
	gbp      []byte
	emoji    []byte
	derived  []byte
	propList []byte

	regularTTF  []byte
	semiboldTTF []byte

	sources   []sourcesInput
	sourcesOK bool

	readme []byte
}

func loadInputs(root string) (*inputs, error) {
	in := &inputs{root: root}
	loaders := []func(string, *inputs) error{
		loadKindInputs,
		loadLayoutConsts,
		loadGlyphJoin,
		loadScripts,
		loadCellSymbols,
		loadStyles,
		loadMarkers,
		loadThemes,
		loadShapes,
		loadRegistries,
		loadEntities,
		loadUnicodeData,
		loadFontData,
		loadSources,
		loadReadme,
	}
	for _, load := range loaders {
		if err := load(root, in); err != nil {
			return nil, err
		}
	}
	return in, nil
}

func loadKindInputs(root string, in *inputs) error {
	if err := loadJSONFile(root, "spec/data/kinds.json", &in.kinds); err != nil {
		return err
	}
	return checkUniqueStrings(kindIDs(in.kinds), "kind id")
}

func kindIDs(kinds []kindInput) []string {
	ids := make([]string, 0, len(kinds))
	for _, k := range kinds {
		ids = append(ids, k.ID)
	}
	return ids
}

func loadLayoutConsts(root string, in *inputs) error {
	if err := loadJSONFile(root, "spec/data/layout-constants.json", &in.layoutConst); err != nil {
		return err
	}
	names := make([]string, 0, 2*len(in.layoutConst))
	for _, c := range in.layoutConst {
		names = append(names, "vector."+c.Name, "cell."+c.Name)
	}
	return checkUniqueStrings(names, "layout constant")
}

func loadGlyphJoin(root string, in *inputs) error {
	if err := loadJSONFile(root, "spec/data/glyph-join.json", &in.glyphJoin); err != nil {
		return err
	}
	masks := make([]string, 0, len(in.glyphJoin))
	for _, g := range in.glyphJoin {
		masks = append(masks, fmt.Sprint(g.Mask))
	}
	return checkUniqueStrings(masks, "glyph join mask")
}

func loadScripts(root string, in *inputs) error {
	if err := loadJSONFile(root, "spec/data/scripts.json", &in.scripts); err != nil {
		return err
	}
	bases := make([]string, 0, len(in.scripts))
	for _, s := range in.scripts {
		bases = append(bases, s.Base)
	}
	return checkUniqueStrings(bases, "script base")
}

func loadCellSymbols(root string, in *inputs) error {
	if err := loadJSONFile(root, "spec/data/cell-symbols.json", &in.cellSymbols); err != nil {
		return err
	}
	names := make([]string, 0, len(in.cellSymbols))
	for _, s := range in.cellSymbols {
		names = append(names, s.Name)
	}
	return checkUniqueStrings(names, "cell symbol")
}

func loadStyles(root string, in *inputs) error {
	if err := loadJSONFile(root, "spec/data/styles.json", &in.styles); err != nil {
		return err
	}
	names := make([]string, 0, len(in.styles.Shape)+len(in.styles.Text))
	for _, s := range in.styles.Shape {
		names = append(names, s.Name)
	}
	for _, s := range in.styles.Text {
		names = append(names, s.Name)
	}
	return checkUniqueStrings(names, "style")
}

func loadMarkers(root string, in *inputs) error {
	if err := loadJSONFile(root, "spec/data/markers.json", &in.markers); err != nil {
		return err
	}
	names := make([]string, 0, len(in.markers))
	for _, m := range in.markers {
		names = append(names, m.Name)
	}
	return checkUniqueStrings(names, "marker")
}

func loadThemes(root string, in *inputs) error {
	if err := loadJSONFile(root, "spec/data/themes.json", &in.themes); err != nil {
		return err
	}
	names := make([]string, 0, len(in.themes))
	for _, t := range in.themes {
		names = append(names, t.Name)
	}
	if err := checkUniqueStrings(names, "theme"); err != nil {
		return err
	}
	for _, t := range in.themes {
		for _, token := range requiredThemeTokens {
			if _, ok := t.Tokens[token]; !ok {
				return fmt.Errorf("theme %q has no %q token", t.Name, token)
			}
		}
	}
	return nil
}

func loadShapes(root string, in *inputs) error {
	if err := loadJSONFile(root, "spec/data/shapes.json", &in.shapes); err != nil {
		return err
	}
	ids := make([]string, 0, len(in.shapes))
	for _, s := range in.shapes {
		ids = append(ids, s.ID)
	}
	return checkUniqueStrings(ids, "shape id")
}

func loadRegistries(root string, in *inputs) error {
	rows, err := loadRegistryDir(root, "spec/data/diagnostics", in.kinds)
	if err != nil {
		return err
	}
	in.diagnostics = rows
	rules, err := loadRegistryDir(root, "spec/data/lint-rules", in.kinds)
	if err != nil {
		return err
	}
	in.lintRules, err = adoptedLintRules(rules)
	if err != nil {
		return err
	}
	in.configKeys, err = loadConfigKeys(root)
	return err
}

func adoptedLintRules(rows []registryRow) ([]registryRow, error) {
	adopted := make([]registryRow, 0, len(rows))
	codes := make([]string, 0, len(rows))
	for _, r := range rows {
		if r.Status != "" && r.Status != "adopted" {
			continue
		}
		adopted = append(adopted, r)
		codes = append(codes, r.Code)
	}
	if err := checkUniqueStrings(codes, "adopted lint rule"); err != nil {
		return nil, err
	}
	return adopted, nil
}

func loadRegistryDir(root, rel string, kinds []kindInput) ([]registryRow, error) {
	names, err := jsonFileNames(root, rel)
	if err != nil {
		return nil, err
	}
	var rows []registryRow
	codes := make([]string, 0)
	for _, name := range orderedRegistryFiles(names, kinds) {
		var fileRows []registryRow
		if err := loadJSONFile(root, rel+"/"+name, &fileRows); err != nil {
			return nil, err
		}
		for _, r := range fileRows {
			rows = append(rows, r)
			codes = append(codes, r.Code)
		}
	}
	if err := checkUniqueStrings(codes, "diagnostic code"); err != nil {
		return nil, err
	}
	if rel == "spec/data/diagnostics" {
		slices.SortStableFunc(rows, func(a, b registryRow) int { return cmp.Compare(a.Code, b.Code) })
	}
	return rows, nil
}

func orderedRegistryFiles(names []string, kinds []kindInput) []string {
	present := make(map[string]bool, len(names))
	for _, n := range names {
		present[n] = true
	}
	order := make([]string, 0, len(names))
	used := make(map[string]bool, len(names))
	take := func(name string) {
		if present[name] && !used[name] {
			order = append(order, name)
			used[name] = true
		}
	}
	take("common.json")
	for _, k := range kinds {
		take(k.ID + ".json")
	}
	rest := make([]string, 0, len(names))
	for _, n := range names {
		if !used[n] {
			rest = append(rest, n)
		}
	}
	slices.Sort(rest)
	return append(order, rest...)
}

func jsonFileNames(root, rel string) ([]string, error) {
	entries, err := os.ReadDir(filepath.Join(root, filepath.FromSlash(rel)))
	if errors.Is(err, os.ErrNotExist) {
		return nil, nil
	}
	if err != nil {
		return nil, err
	}
	names := make([]string, 0, len(entries))
	for _, e := range entries {
		if !e.IsDir() && strings.HasSuffix(e.Name(), ".json") {
			names = append(names, e.Name())
		}
	}
	slices.Sort(names)
	return names, nil
}

func loadConfigKeys(root string) ([]configKeyInput, error) {
	names, err := jsonFileNames(root, "spec/data/config-keys")
	if err != nil {
		return nil, err
	}
	var keys []configKeyInput
	seen := make([]string, 0)
	for _, name := range names {
		var rows []configKeyInput
		if err := loadJSONFile(root, "spec/data/config-keys/"+name, &rows); err != nil {
			return nil, err
		}
		kind := strings.TrimSuffix(name, ".json")
		if kind == "common" {
			kind = ""
		}
		for _, r := range rows {
			if err := checkConfigClass(r.Class); err != nil {
				return nil, fmt.Errorf("%s: %w", name, err)
			}
			keys = append(keys, configKeyInput{Kind: kind, Key: r.Key, Class: r.Class})
			seen = append(seen, kind+"/"+r.Key)
		}
	}
	if err := checkUniqueStrings(seen, "config key"); err != nil {
		return nil, err
	}
	slices.SortStableFunc(keys, func(a, b configKeyInput) int {
		return cmp.Or(cmp.Compare(a.Kind, b.Kind), cmp.Compare(a.Key, b.Key))
	})
	return keys, nil
}

func checkConfigClass(class string) error {
	switch class {
	case "honoured", "accepted-ignored", "rejected":
		return nil
	}
	return fmt.Errorf("unknown config class %q", class)
}

func loadEntities(root string, in *inputs) error {
	var raw map[string]entityInput
	if err := loadJSONFile(root, "spec/data/entities.json", &raw); err != nil {
		return err
	}
	rows := make([]entityRow, 0, len(raw))
	for name, value := range raw {
		if !strings.HasSuffix(name, ";") {
			continue
		}
		rows = append(rows, entityRow{Name: name, CPS: value.Codepoints})
	}
	slices.SortStableFunc(rows, func(a, b entityRow) int { return cmp.Compare(a.Name, b.Name) })
	in.entities = rows
	return nil
}

func loadUnicodeData(root string, in *inputs) error {
	files := []struct {
		rel  string
		dest *[]byte
	}{
		{"spec/data/unicode/EastAsianWidth.txt", &in.eaw},
		{"spec/data/unicode/GraphemeBreakProperty.txt", &in.gbp},
		{"spec/data/unicode/emoji-data.txt", &in.emoji},
		{"spec/data/unicode/DerivedCoreProperties.txt", &in.derived},
		{"spec/data/unicode/PropList.txt", &in.propList},
	}
	for _, f := range files {
		data, err := readOptional(root, f.rel)
		if err != nil {
			return err
		}
		*f.dest = data
	}
	return nil
}

func loadFontData(root string, in *inputs) error {
	var err error
	if in.regularTTF, err = readOptional(root, "spec/data/fonts/Inter-Regular.ttf"); err != nil {
		return err
	}
	if in.semiboldTTF, err = readOptional(root, "spec/data/fonts/Inter-SemiBold.ttf"); err != nil {
		return err
	}
	return nil
}

func loadSources(root string, in *inputs) error {
	if err := loadJSONFile(root, "spec/data/SOURCES.json", &in.sources); err != nil {
		return err
	}
	in.sourcesOK = in.sources != nil
	return nil
}

func loadReadme(root string, in *inputs) error {
	data, err := readOptional(root, "README.md")
	if err != nil {
		return err
	}
	in.readme = data
	return nil
}

func readOptional(root, rel string) ([]byte, error) {
	data, err := os.ReadFile(filepath.Join(root, filepath.FromSlash(rel)))
	if errors.Is(err, os.ErrNotExist) {
		return nil, nil
	}
	if err != nil {
		return nil, err
	}
	return data, nil
}

func loadJSONFile(root, rel string, v any) error {
	data, err := readOptional(root, rel)
	if err != nil || data == nil {
		return err
	}
	if err := unmarshalStrict(data, v); err != nil {
		return fmt.Errorf("%s: %w", rel, err)
	}
	return nil
}

func checkUniqueStrings(names []string, what string) error {
	seen := make(map[string]struct{}, len(names))
	for _, name := range names {
		if _, dup := seen[name]; dup {
			return fmt.Errorf("duplicate %s %q", what, name)
		}
		seen[name] = struct{}{}
	}
	return nil
}
