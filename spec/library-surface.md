# Library surface

This file lists the public names of the Go package `mermaid`, the Go package `raster`, and the Rust crate `elegant_mermaid` side by side, and fixes the error, aliasing, option, and block contracts that the signatures do not show.

## Public names

- library-surface-01: The public types MUST be the pairs of the table below; the Go column names package `mermaid` unless prefixed `raster.`, and the Rust column names crate `elegant_mermaid` unless prefixed `raster::`. [just go-check]

    |Go|Rust|
    |---|---|
    |`Kind uint8` (closed enum of the 33 kinds)|`DiagramKind` (closed enum of the 33 kinds)|
    |`Severity uint8`|`Severity`|
    |`FixSafety uint8` (`FixSafe < FixUnsafe`)|`FixSafety`|
    |`Span{Start, End int}`|`Span{start: usize, end: usize}`|
    |`Position{Line, Column int}`|`Position{line: usize, column: usize}`|
    |`Edit{Span Span; NewText string}`|`Edit{span: Span, new_text: String}`|
    |`Fix{Title string; Safety FixSafety; Edits []Edit}`|`Fix{title: String, safety: FixSafety, edits: Vec<Edit>}`|
    |`Related{Span Span; Message string}`|`Related{span: Span, message: String}`|
    |`Diagnostic{Code string; Severity Severity; Message string; Span Span; Related []Related; Help string; Fixes []Fix}`|`Diagnostic{code: &'static str, severity: Severity, message: String, span: Span, related: Vec<Related>, help: String, fixes: Vec<Fix>}`|
    |`LintConfig{Select, Ignore []string; Severity map[string]Severity; Off []string}`|`LintConfig{select: Vec<String>, ignore: Vec<String>, severity: BTreeMap<String, Severity>, off: Vec<String>}`|
    |`Document` (unexported state)|`Document<'src>` (private `Cow<'src, str>`)|

    |Go|Rust|
    |---|---|
    |`FixOutcome` (none in Go; `ApplyFixes` returns `(out []byte, applied int)`)|`FixOutcome{text: String, applied: usize}`|
    |`IconPack` (unexported state)|`IconPack` (private state)|
    |`GlyphOutlines` (unexported: per weight and rune, move/line/quad commands in font units, units per em, and the Noto fallback font bytes of render-svg-63)|`GlyphOutlines` (private state)|
    |`Profile uint8`|`Profile`|
    |`Limits{MaxNodes, MaxEdges, MaxTextBytes int}`|`Limits{max_nodes: u32, max_edges: u32, max_text_bytes: u32}`|
    |`Cancel` (none in Go; Go functions take `context.Context`)|`Cancel` (private `Option<Arc<AtomicBool>>`)|
    |`LayoutOptions{Profile Profile; Theme string; Thoroughness int; MaxWidth int; Limits Limits; IconPacks []*IconPack; Config []byte}`|`LayoutOptions{profile: Profile, theme: String, thoroughness: u8, max_width: u32, limits: Limits, icon_packs: Vec<IconPack>, config: Option<String>, cancel: Cancel}`|
    |`Scene` (unexported state)|`Scene` (private state)|
    |`TextMode uint8`|`TextMode`|
    |`SVGOptions` (embeds `LayoutOptions`; `Background string; Text TextMode; Outlines *GlyphOutlines; IDPrefix string`)|`SvgOptions{layout: LayoutOptions, background: String, text: TextMode, outlines: Option<GlyphOutlines>, id_prefix: String}`|
    |`Charset uint8`|`Charset`|
    |`ColorMode uint8`|`ColorMode`|
    |`TextOptions` (embeds `LayoutOptions`; `Charset Charset; Color ColorMode`)|`TextOptions{layout: LayoutOptions, charset: Charset, color: ColorMode}`|
    |`Block{Source []byte; Span Span; Lines []BlockLine}`|`Block<'src>{source: Cow<'src, [u8]>, span: Span, lines: Vec<BlockLine>}`|
    |`BlockLine{HostOffset, BlockOffset, Len int}`|`BlockLine{host_offset: usize, block_offset: usize, len: usize}`|
    |`raster.Options{Scale int; Background string}`|`raster::PngOptions{scale: u32, background: String}`|

- library-surface-02: The public constants and enum variants MUST be the pairs of the table below. [just go-check]

    |Go|Rust|
    |---|---|
    |`KindFlowchart` through `KindInfo` (33 constants: `Kind` plus the kind id in PascalCase)|`DiagramKind::Flowchart` through `DiagramKind::Info` (33 variants: the kind id in PascalCase, no prefix)|
    |`SeverityError`, `SeverityWarning`, `SeverityInfo`|`Severity::Error`, `Severity::Warning`, `Severity::Info`|
    |`FixSafe`, `FixUnsafe`|`FixSafety::Safe`, `FixSafety::Unsafe`|
    |`ProfileVector`, `ProfileCell`|`Profile::Vector`, `Profile::Cell`|
    |`TextFont`, `TextPaths`|`TextMode::Font`, `TextMode::Paths`|
    |`CharsetUnicode`, `CharsetASCII`|`Charset::Unicode`, `Charset::Ascii`|
    |`ColorNone`, `ColorANSI16`, `ColorANSI256`, `ColorTruecolor`|`ColorMode::None`, `ColorMode::Ansi16`, `ColorMode::Ansi256`, `ColorMode::Truecolor`|

    The 33 kind ids, in the order of `spec/data/kinds.json`: `Flowchart`, `Swimlane`, `Agentflow`, `Class`, `State`, `Er`, `Requirement`, `Usecase`, `C4`, `Sequence`, `Block`, `Architecture`, `Kanban`, `Packet`, `Mindmap`, `Treeview`, `Ishikawa`, `Gitgraph`, `Eventmodeling`, `Timeline`, `Journey`, `Gantt`, `Xychart`, `Quadrant`, `Treemap`, `Wardley`, `Pie`, `Radar`, `Sankey`, `Venn`, `Cynefin`, `Railroad`, `Info`.

- library-surface-03: The public free functions MUST be the pairs of the table below. [just go-check]

    |Go|Rust|
    |---|---|
    |`Parse(src []byte) *Document`|`parse(source: &str) -> Document<'_>` and `parse_bytes(source: &[u8]) -> Document<'_>`|
    |`Lint(d *Document, cfg LintConfig) []Diagnostic`|`lint(document: &Document<'_>, config: &LintConfig) -> Vec<Diagnostic>`|
    |`ApplyFixes(src []byte, cfg LintConfig, max FixSafety) (out []byte, applied int)`|`apply_fixes(source: &[u8], config: &LintConfig, max: FixSafety) -> FixOutcome`|
    |`ParseIconPack(data []byte) (*IconPack, error)`|`parse_icon_pack(source: &str) -> Result<IconPack, IconPackError>`|
    |`Layout(ctx context.Context, d *Document, o LayoutOptions) (*Scene, error)`|`layout(document: &Document<'_>, options: &LayoutOptions) -> Result<Scene, RenderError>`|
    |`RenderSVG(ctx context.Context, d *Document, o SVGOptions) ([]byte, error)`|`render_svg(document: &Document<'_>, options: &SvgOptions) -> Result<String, RenderError>`|
    |`RenderSVGSource(ctx context.Context, src []byte, o SVGOptions) ([]byte, error)`|`render_svg_str(source: &str, options: &SvgOptions) -> Result<String, RenderError>`|
    |`RenderText(ctx context.Context, d *Document, o TextOptions) ([]byte, error)`|`render_text(document: &Document<'_>, options: &TextOptions) -> Result<String, RenderError>`|
    |`RenderTextSource(ctx context.Context, src []byte, o TextOptions) ([]byte, error)`|`render_text_str(source: &str, options: &TextOptions) -> Result<String, RenderError>`|
    |`MarkdownBlocks(src []byte) []Block`|`markdown::blocks(source: &[u8]) -> Vec<Block<'_>>`|
    |`raster.PNG(s *mermaid.Scene, o raster.Options) ([]byte, error)`|`raster::png(scene: &Scene, options: &raster::PngOptions) -> Result<Vec<u8>, RasterError>` (feature `png`)|
    |`raster.InterOutlines() *mermaid.GlyphOutlines`|`raster::inter_outlines() -> GlyphOutlines` (feature `png`)|

- library-surface-04: The public methods MUST be the pairs of the table below. [just go-check]

    |Go|Rust|
    |---|---|
    |`Kind.String() string` (returns the spec id)|`DiagramKind::id(self) -> &'static str`|
    |`(*Document).Source() []byte`|`Document::source(&self) -> &str`|
    |`(*Document).Kind() (Kind, bool)`|`Document::kind(&self) -> Option<DiagramKind>`|
    |`(*Document).Diagnostics() []Diagnostic`|`Document::diagnostics(&self) -> &[Diagnostic]`|
    |`(*Document).HasErrors() bool`|`Document::has_errors(&self) -> bool`|
    |`(*Document).Position(offset int) Position`|`Document::position(&self, offset: usize) -> Position`|
    |`(*Scene).Dump() []byte`|`Scene::dump(&self) -> String`|
    |`(Block).HostOffset(blockOffset int) int`|`Block::host_offset(&self, block_offset: usize) -> usize`|
    |(none; Go functions take `context.Context`)|`Cancel::new() -> Self`, `Cancel::cancel(&self)`, `Cancel::is_cancelled(&self) -> bool`|

- library-surface-05: The Go error sentinels and the Rust error variants MUST be the pairs of the table below. [just go-check]

    |Go|Rust|
    |---|---|
    |`ErrInvalidDocument`|`RenderError::InvalidDocument{errors: usize}`|
    |`ErrTooLarge`|`RenderError::TooLarge{limit: u32, actual: u32}`|
    |`ErrOverflow`|`RenderError::Overflow`|
    |`ErrBadConfig`|`RenderError::InvalidConfig{errors: usize}` and `RasterError::InvalidConfig{errors: usize}`|
    |`ErrBadIconPack`|`IconPackError::Malformed{reason: String}`|
    |(none; a cancelled `context.Context` returns `ctx.Err()` unchanged)|`RenderError::Cancelled`|
    |`raster.ErrPixelsTooLarge`|`RasterError::PixelsTooLarge{width: u32, height: u32}`|
    |`raster.ErrEncode`|`RasterError::Encode{message: String}`|

- library-surface-06: A Go test MUST check that every Go name of the tables of library-surface-01 to library-surface-05 exists, and MUST fail when one is missing. [just go-check]
- library-surface-07: A Rust test MUST check that every Rust name of the tables of library-surface-01 to library-surface-05 exists, and MUST fail when one is missing. [just rust-check]
- library-surface-08: Every Go function MUST have a Rust counterpart with the same semantics. [just parity]

## Packages and builds

- library-surface-09: Package `raster` MUST import package `mermaid`, and package `mermaid` MUST NOT import package `raster`. [just go-check]
- library-surface-10: A `Document` MUST be immutable after `Parse`, and it and every function of the surface MUST be safe for concurrent use. Shared flowchart lexer tables MUST be initialized before parsing starts and MUST remain read-only. [just go-check]
- library-surface-11: The Rust `Document<'src>` and `Scene` MUST be `Send + Sync`. [just rust-check]
- library-surface-12: The Rust core MUST be `#![forbid(unsafe_code)]` and MUST declare `rust-version = "1.99"`. [just rust-check]
- library-surface-13: The Rust core MUST build for `wasm32-unknown-unknown`, and the Go core MUST build for `GOOS=js GOARCH=wasm`. [just wasm-parity]

## Errors

- library-surface-14: Each Go error returned by this package or by `raster` MUST wrap exactly one sentinel with `%w`, and callers MUST test it with `errors.Is`. [just go-check]
- library-surface-15: `Layout`, `RenderSVG`, `RenderText`, `RenderSVGSource`, and `RenderTextSource` MUST return `ErrInvalidDocument` when the document has error-severity diagnostics. [just go-check]
- library-surface-16: `ErrTooLarge` and `ErrOverflow` MUST come from `Layout`, so every render function MUST return them too. [just go-check]
- library-surface-17: `ErrBadConfig` MUST cover an invalid option value, an unknown theme name, `Config` text that does not parse or whose root is not a mapping, and `TextPaths` without `Outlines`. [just go-check]
- library-surface-18: `ErrBadIconPack` MUST come from `ParseIconPack`, and `ParseIconPack` MUST NOT repair invalid UTF-8. [just go-check]
- library-surface-19: The raster functions MUST return `raster.ErrPixelsTooLarge`, `raster.ErrEncode`, or `mermaid.ErrBadConfig`. [just go-check]
- library-surface-20: A cancelled context MUST make the Go functions return `ctx.Err()` unchanged, and this MUST be the one error that is not wrapped. [just go-check]
- library-surface-21: The Rust error cases MUST be `RenderError::InvalidDocument`, `TooLarge`, `Overflow`, `InvalidConfig`, and `Cancelled`; `RasterError::PixelsTooLarge`, `Encode`, and `InvalidConfig`; and `IconPackError::Malformed`. [just rust-check]
- library-surface-22: The Rust error enums MUST derive `Debug` and `thiserror::Error` and MUST be `#[non_exhaustive]`. [just rust-check]
- library-surface-23: `InvalidConfig { errors }` MUST count the invalid config entries, or 1 for one invalid option value or one unparsable `Config` text. [just rust-check]

## Aliasing

- library-surface-24: `Parse` MUST NOT copy valid input: `Source` MUST return the caller's slice, and the caller MUST NOT change `src` while the `Document` is in use. [just go-check]
- library-surface-25: `Block.Source` MUST alias the host slice only for a top-level fence, where no container prefix was removed; otherwise `Source` MUST be a copy that the `Block` owns; Rust MUST hold a top-level fence as `Cow::Borrowed` and any other block as `Cow::Owned`. [just go-check]
- library-surface-26: An input that is not valid UTF-8 MUST be repaired into a copy that the `Document` owns, and `Source`, every `Span`, and every `Position` MUST use that copy. [just go-check]
- library-surface-27: `ApplyFixes` MUST return a new slice that never aliases `src`, and it MUST return repaired text when `src` was invalid. [just go-check]
- library-surface-28: Rust `parse(&str)` MUST borrow its input; Rust functions that take `&str` MUST require valid UTF-8, so a caller holding bytes MUST use `parse_bytes`. [just rust-check]

## Options

- library-surface-29: Option structs MUST be plain data; the Go zero value and the Rust `Default` MUST both mean house defaults, and Go zero fields MUST take their defaults one field at a time. [just parity]
- library-surface-30: A Go `Thoroughness` outside 1 to 5, or a negative `Limits` field, MUST be `ErrBadConfig`. [just go-check]
- library-surface-31: A Rust `scale` or `thoroughness` outside its range, or a Rust limit of 0, MUST be `InvalidConfig { errors: 1 }`. [just rust-check]
- library-surface-32: The fields and defaults MUST be as follows. [just parity]

    - `LayoutOptions`: `Profile` is `ProfileVector` (Go zero value) or `Profile::Vector` (default), or `ProfileCell` or `Profile::Cell`. `Theme` is a theme name; `""` in Go and `"elegant-light"` in Rust are the default. `Thoroughness` is 1 to 5; Go `0` and Rust `3` are the default. `MaxWidth` is in columns, is the packing and wrapping target of the cell profile, and is `0` (natural width) by default; the vector profile ignores it, and Go rejects a negative value with `ErrBadConfig`. `Limits` holds `MaxNodes` 2000, `MaxEdges` 5000, and `MaxTextBytes` 1 048 576; Rust gets these from `Limits::default()`. A model over a limit is `ErrTooLarge` or `TooLarge`. `IconPacks` and `icon_packs` are empty by default. `Config` and `config` are empty (Go) or `None` (Rust) by default. `cancel` (Rust only) is `Cancel::default()`, which never fires. `LayoutOptions` carries `cancel`; `SvgOptions` and `TextOptions` reach it through `layout`. `PngOptions` has no cancel, because `raster.PNG` takes no context.
    `MaxTextBytes` MUST count the UTF-8 bytes of resolved text that layout measures, once per owned text value. This MUST include node labels, edge labels, group titles, and an ID used as displayed fallback text. Source comments, source syntax, and accessibility metadata used only by SVG MUST NOT count. Equivalent layout models MUST have the same count regardless of their source representation. Layout MUST check the count before measurement.
    `MaxNodes` MUST count every model box, including an empty group. `MaxEdges` MUST count every semantic route, including self-loops and group endpoints. Synthetic layout nodes and constraints MUST NOT count toward either model limit.
    - `SVGOptions` (Rust field `layout`): `RenderSVG` always uses the vector profile and ignores `Profile`. `Background` is `""` (the theme `bg` token) or a hex colour `#rgb` or `#rrggbb`; other values are `ErrBadConfig`. `Text` is `TextFont` (default) or `TextPaths`. `TextPaths` requires `Outlines`; nil outlines are `ErrBadConfig`; `Outlines` is ignored for `TextFont`. `Outlines` is nil by default, and `raster.InterOutlines()` builds the value. `IDPrefix` is `""` (no prefix) by default; otherwise it MUST match `[A-Za-z][A-Za-z0-9_-]*` and is prepended to every `id` attribute, and other values are `ErrBadConfig`.
    - `TextOptions` (Rust field `layout`): `RenderText` always uses the cell profile and ignores `Profile`. `Charset` is `CharsetUnicode` (default) or `CharsetASCII`, and Rust `Charset::Unicode` (default) or `Charset::Ascii`. `Color` is `ColorNone` (default), `ColorANSI16`, `ColorANSI256`, or `ColorTruecolor`, and Rust `ColorMode::None` (default), `Ansi16`, `Ansi256`, or `Truecolor`.
    - `raster.Options` and `PngOptions`: `Scale` is 1 to 8; Go `0` and Rust `2` are the default. Other values are `ErrBadConfig` and `InvalidConfig { errors: 1 }`. `Background` follows the SVG rule: `""` (the theme `bg` token) or a hex colour. A pixel side is `px = (units * scale + 63) div 64`, where `units` is the scene side in 1/64 px. A side above 16384 px, or an area above 67 108 864 px (2^26), is `raster.ErrPixelsTooLarge` or `RasterError::PixelsTooLarge`.

- library-surface-33: The zero `LintConfig` and `LintConfig::default()` MUST select every registered rule at its default severity. [just go-check]
- library-surface-34: `LayoutOptions.Config` MUST take an upstream config document, which is one block mapping in the config-value grammar of spec/preprocessing.md, and the frontmatter `config` key MUST use the same grammar. [just go-check]

## Blocks

- library-surface-35: `MarkdownBlocks` and `markdown::blocks` MUST scan the host as bytes, and a block whose text is not valid UTF-8 MUST get `source/invalid-utf8` when it is parsed. [just go-check]
- library-surface-36: `Block.Source` MUST be the block text with its container prefixes (block quote and list item prefixes) removed. [just go-check]
- library-surface-37: `Lines` MUST have one `BlockLine` for each line of `Source`: `BlockOffset` is the offset in `Source` of the line's first content byte, `HostOffset` is the host offset of that byte, and `Len` is the byte count of the line's content without its line ending. [just go-check]
- library-surface-38: `HostOffset(blockOffset)` MUST clamp `blockOffset` to `[0, len(Source)]`, MUST find the line `i` with the largest `BlockOffset_i <= blockOffset`, and MUST return `HostOffset_i + min(blockOffset - BlockOffset_i, Len_i)`. [just go-check]
- library-surface-39: An offset on a line ending MUST map to the host position just after that line's content, and a block with no lines MUST map every offset to `Span.Start`. [just go-check]
- library-surface-40: Rust MUST use the same rule with the fields `lines`, `host_offset`, `block_offset`, and `len`. [just rust-check]
- library-surface-41: `--fix` on a Markdown host MUST edit inside the blocks only and MUST map each edit back to host offsets; the fence and container rules are fixed in spec/markdown-extraction.md. [just go-check]

## Icon packs

- library-surface-42: The error of `ParseIconPack` and `parse_icon_pack` MUST read `malformed icon pack: REASON` in both languages, so the Go sentinel `ErrBadIconPack` MUST read `malformed icon pack` and MUST be followed by `: REASON`, and the CLI MUST print `FILE: malformed icon pack: REASON` as spec/cli.md states. [just go-check: TestParsePackReasons]
- library-surface-43: A pack MUST be read in this order, and the reader MUST give the first fault: `invalid UTF-8` for bytes that are not UTF-8; `invalid JSON at byte N: DETAIL` for text that is not one JSON document of RFC 8259 with at most 64 levels of arrays and objects, with N the zero-based byte offset of the fault and DETAIL one of `expected a value`, `unknown literal`, `expected a member name`, `expected ':'`, `expected ',' or '}'`, `expected ',' or ']'`, `expected a digit`, `expected a fraction digit`, `expected an exponent digit`, `invalid number`, `unterminated string`, `control character in string`, `unterminated escape`, `invalid escape`, `unpaired surrogate`, `invalid code point`, `expected a hex digit`, `trailing content`, and `nesting is too deep`; `the root must be an object`; `missing string prefix`; `the prefix must not be empty`; `missing icons object`; then the pack-level `left`, `top`, `width`, and `height` in that order, then `the default size must be positive`; then each icon in member order. [just go-check: TestParsePackReasons]
- library-surface-44: For each icon, the reader MUST give `icon NAME must be an object`, then `icon NAME needs a string body`, then the icon's `width` and `height`, then `icon NAME needs a positive size`, then its `left` and `top`. A dimension MUST give `KEY must be a number` when the value is not a JSON number and `KEY is out of range` when its text has an exponent, more than 6 integer digits, or more than 6 fraction digits, with KEY one of `left`, `top`, `width`, and `height`; an absent dimension MUST take the pack value, and the pack value MUST default to 0 for `left` and `top` and to 16 for `width` and `height`. A repeated member MUST take its last value, and a member that the rule does not name MUST be ignored. [just go-check: TestParsePackReasons]
- library-surface-45: The Rust tests `icon_pack_reasons_are_fixed` and `icon_pack_accepts_the_shared_valid_documents` MUST check the same documents and the same REASON texts as `TestParsePackReasons` and `TestParsePackAccepts`. [just rust-check: icon_pack_reasons_are_fixed]

## Error texts

- library-surface-46: The text of an error that a Go function returns (`Error()`) and the text of the matching Rust error (`Display`) MUST be the same: `model exceeds the limit of LIMIT; actual ACTUAL` for a model over a limit (`RenderError::TooLarge`), `arithmetic overflow` for an overflow (`RenderError::Overflow`, `GeomError::Overflow`, `geom.ErrOverflow`, and the sentinel `ErrOverflow`), `domain error` for a domain fault (`GeomError::Domain` and `geom.ErrDomain`), `image is too large: WxH pixels` for `RasterError::PixelsTooLarge` and the Go `*raster.RasterError` of kind `PixelsTooLarge`, and `PNG encoding failed: MESSAGE` for the Encode kind of both. The texts of the other Go sentinels, such as `ErrTooLarge`, are not bound by this rule, because a returned error carries the text of its cause. [just go-check: TestErrorTexts]
- library-surface-47: The Rust test `error_texts` MUST check the same texts as the Go tests `TestErrorTexts` of the root package, `internal/geom`, and `raster`. [just rust-check: error_texts]

## Icon drawing

- library-surface-48: A pack icon body MUST be zero or more `<path>` elements separated by ASCII whitespace (space, tab, CR, LF, FF), and any other text, element, or attribute MUST make the icon unsupported; a `<path>` element MUST be `<path`, one or more whitespace characters, attributes, and then `/>` or `></path>`, each attribute MUST be a name without whitespace or any of `<>/"'`, then `=`, then a value in single or double quotes with no whitespace around the `=`, the only accepted attributes MUST be `d` (any value) and `fill` with the value `currentColor`, and the element MUST have a `d`. [just go-check: TestPackBodies]
- library-surface-49: Path data MUST use the commands `M m L l H h V v C c S s Q q T t Z z`, MUST start with `M` or `m`, MUST read an `M` that has more coordinate pairs as `L` for the extra pairs (and `m` as `l`), MUST read other commands with more argument groups as repeats of the same command, MUST take no argument after `Z` or `z` except a new command, and any other command letter (for example `A`) or text MUST make the icon unsupported; separators MUST be ASCII whitespace, with at most one comma, which MAY sit before a number or a command. [just go-check: TestPackBodies]
- library-surface-50: A number in path data MUST be an optional sign, digits with an optional `.` and fraction digits (at least one digit in all), and no exponent, and its value MUST be fixed point with six fraction digits: the first six fraction digits are kept, the seventh digit rounds half up (5 to 9 adds one unit), and later digits are ignored, all on the magnitude, so the sign applies afterwards (`-0.0000005` is -1 unit); the integer part (leading zeros dropped) MUST be below 1000000, and every number and every absolute coordinate of every command, including a smooth reflected control point, MUST have a magnitude below 1000000, or the icon is unsupported. [just go-check: TestPackPathNumbers]
- library-surface-51: An icon whose larger dimension is below 1 MUST be unsupported; otherwise the scale `S` MUST be the integer `max(1, round_half_up(1536 / max(width, height)))` units per source unit, a source length `v` MUST map to `round_half_up(v * S)` units, the icon box MUST have the side 1536 units, a point `(x, y)` MUST map to `origin + (floor_div(1536 - unit(width), 2) + unit(x - left), floor_div(1536 - unit(height), 2) + unit(y - top))`, and a result outside int32 MUST make the icon unsupported. [just go-check: TestPackScaleAndOrigin]
- library-surface-52: A `Q` or `T` segment MUST become a cubic whose first control point is `round_half_up(from + 2 * control, 3)` and whose second is `round_half_up(to + 2 * control, 3)` per axis, computed on the mapped integer points, where `from` is the mapped current point (the mapped start point after `Z`); relative commands, `S`, and `T` MUST follow SVG: relative coordinates add the current point, `S` reflects the previous cubic's second control point and `T` the previous quadratic's control point, and a command of another kind uses the current point. [just go-check: TestPackQuadraticToCubic]
- library-surface-53: An icon MUST draw one `Ink` path per `<path>` element in body order, each starting from the origin state, so a body with no `<path>` element MUST be supported and draw nothing. [just go-check: TestPackBodies]
- library-surface-54: A flowchart node `icon: 'PREFIX:NAME'` MUST resolve to the first pack with that prefix that defines NAME, and a name with no `:`, an absent name, and an unsupported icon MUST be missing; a missing icon MUST raise `icon/pack-missing` (info) with the node's span and message `icon NAME is not available`, and MUST draw the built-in `unknown` icon. [just go-check: TestPlaceIcons]
- library-surface-55: The built-in `unknown` icon MUST be one `Ink` path, the question-mark outline of Inter Regular at 2048 units per em scaled to the 1536-unit box (`round_half_up(v * 1536 / 2048)`) and centred in it, in the vector profile, and one `SymbolRef` `unknown` with style `ink` in the cell profile, and a supported pack icon MUST also be one `SymbolRef` `unknown` with style `ink` in the cell profile. [just go-check: TestBuiltinIcons]
- library-surface-56: The icon box MUST be centred horizontally on its node and vertically on the node's top edge, so the node's label stays clear of the icon: the vector box origin is `(x + floor_div(w, 2) - 768, y - 768)` and the cell symbol is at `(x + floor_div(w, 2), y)`, where `(x, y, w, h)` is the node box. The drawn items MUST be placed in the node's group before its first marker, symbol, or text item, and `emd render` and the library layout MUST place icons while `emd layout` MUST NOT. [just go-check: TestPlaceIcons]
- library-surface-57: The Rust tests `icon_path_numbers`, `icon_path_numbers_reject_exponents`, `icon_path_coordinates_stay_below_the_limit`, `icon_scale_and_origin`, `icon_result_outside_int32_is_unsupported`, `icon_quadratic_to_cubic`, `icon_relative_and_smooth_commands`, `icon_bodies`, `icon_resolution`, and `icon_placement` MUST compute their expected values from rules library-surface-48 to library-surface-56, as the Go tests `TestPackPathNumbers`, `TestPackPathNumbersRejectExponents`, `TestPackCoordinatesStayBelowTheLimit`, `TestPackScaleAndOrigin`, `TestPackResultOutsideInt32IsUnsupported`, `TestPackQuadraticToCubic`, `TestPackRelativeAndSmoothCommandsFollowSVG`, `TestPackBodies`, and `TestPlaceIcons` do, and neither language MUST read saved expected output. [just rust-check: icon_scale_and_origin]
