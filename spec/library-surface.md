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
    |`GlyphOutlines` (unexported: per weight and rune, move/line/quad commands in font units, and units per em)|`GlyphOutlines` (private state)|
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
- library-surface-10: A `Document` MUST be immutable after `Parse`, and it and every function of the surface MUST be safe for concurrent use. [just go-check]
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
