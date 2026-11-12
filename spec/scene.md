# Scene primitives, styles, and element styles

This file fixes the parts of a scene, the closed primitive set, the shape and text style tables, the paint constants, and the element style rules that every back end reads.

## Scene parts

- scene-01: A scene MUST hold four parts: `profile`, `canvas`, the dump part, and `items`. [just go-check]
- scene-02: `profile` MUST be `vector` or `cell`, and `canvas` MUST hold `w` and `h` in profile units. [just parity]
- scene-03: The dump part MUST be `boxes`, `routes`, and `labels`, exactly as `spec/layout-dump.md` defines them. [just parity]
- scene-04: `items` MUST be an ordered list of `Group` values, and draw order MUST be list order, so a later item is drawn over an earlier one. [just go-check]
- scene-05: Validators, metrics, and Lean theorems MUST read only the dump part, and back ends MUST read only `profile`, `canvas`, and `items`. [just validate]

## Groups

- scene-06: Groups MUST NOT nest, and a `Group` MUST have `role`, `owner`, and `items`. [just go-check]
- scene-07: Group `role` MUST be one of `decor`, `group`, `edge`, or `node`. [just go-check]
- scene-08: `owner` MUST be the id of the dump box for roles `group` and `node`, the id of the dump route for role `edge`, and the empty string for `decor`. [just go-check]
- scene-09: Groups MUST appear in this order: at most one `decor` group under the diagram, which holds bands, grids, and axes. Then one `group` group for each dump box with role `group` in dump order. Then one `edge` group for each dump route in dump order. Then one `node` group for each dump box with role `node` in dump order. Then at most one `decor` group over the diagram, which holds the title, legends, and the gantt today line. [just go-check]
- scene-10: Inside a group, shape primitives MUST come first, then `MarkerRef` items, then `SymbolRef` items, then `Text` items, each kind in emission order, and the source-end marker MUST come before the target-end marker. [just go-check]
- scene-11: A route label MUST be a `Text` item in that route's `edge` group, and node text MUST be a `Text` item in the `node` group. [just parity]
- scene-12: Unless the kind's section places it, the text box of a node with `n` text lines MUST be `rect.x = box.x`, `rect.w = box.w`, `rect.h = n * LH`, and `rect.y = box.y + floor_div(box.h - n * LH, 2)`, with `align` `middle`, where `LH` is the role line height, which is 1 row in the cell profile. [just go-check]

## Roles

- scene-13: Dump box `role` MUST be `node` or `group`. [just parity]
- scene-14: Text `role` MUST be `title`, `label`, or `body`, with the sizes and weights of the role table of `spec/text-measurement.md`. [just go-check]

## Primitives

- scene-15: Every shape primitive, which is `Rect`, `RoundRect`, `Ellipse`, `Polygon`, `Polyline`, or `Path`, MUST carry `style`, `series`, `width`, and `line`. [just go-check]
- scene-16: `series` MUST be 0 to 11, MUST be read only by series styles, and MUST be 0 for every other style. [just go-check]
- scene-17: `width` MUST be `normal`, `emphasis`, or an integer in units, and the integer form MUST be used only by sankey links and treeview guides. [just go-check]
- scene-18: `line` MUST be `solid`, `dashed`, `dotted`, or `double`, and `double` MUST appear only in cell-profile scenes, for a flowchart shape whose `corner` in `spec/data/shapes.json` is `double`. [just go-check]
- scene-19: `Rect` MUST have `rect`. [just go-check]
- scene-20: `RoundRect` MUST have `rect` and `r`, where `r` is the corner radius in units: the `radius` token of 512 units, or 768 units under `look: neo`, unless the kind's layout section states a radius; `r` MUST be 0 in the cell profile, where the primitive type alone selects rounded corners. [just go-check]
- scene-21: `Ellipse` MUST have `cx`, `cy`, `rx`, and `ry`. [just go-check]
- scene-22: `Polygon` MUST have `points`, MUST be closed, and MUST have at least 3 points. [just go-check]
- scene-23: `Polyline` MUST have `points`, MUST be open, and MUST have at least 2 points. It MUST have `corner`, a radius in units where 0 means sharp, and a route MUST set `corner` to `corner_radius`, which is 512 units in the vector profile and 0 in the cell profile. [just go-check]
- scene-24: `Path` MUST have `commands`, and each command MUST be one of `M x y`, `L x y`, `C x1 y1 x2 y2 x y`, `A cx cy r a0 sweep`, or `Z`. [just go-check]
- scene-25: `A` MUST be a circular arc given by centre, radius, start angle, and signed sweep, with angles in 1/65536 turn and the parameters of the Arc rule of `spec/render-cells.md`, and elliptical arcs MUST NOT exist in the scene. [just go-check]
- scene-26: `Text` MUST have `rect`, `role`, `size`, `align`, `style`, `series`, and `lines`, where each line is a list of runs `{text, bold, italic}`. [just go-check]
- scene-27: `size` MUST be the role size in px unless the kind or the math rule sets another size, for example `info.font_size`, and `align` MUST be `start`, `middle`, or `end`. [just go-check]
- scene-28: `series` of a `Text` MUST be the series index of the fill that the text sits on, and it MUST be 0 for every other text. [just go-check]
- scene-29: `MarkerRef` MUST have `marker`, a name in `spec/data/markers.json`, `at`, the route end point, and `axis`, which is `+x`, `-x`, `+y`, or `-y`, the direction toward the end point chosen by the arrowhead axis rule of `spec/render-svg.md`. Its style MUST come from the `paint` field of the marker. [just go-check]
- scene-30: `SymbolRef` MUST have `symbol`, a name in `spec/data/cell-symbols.json`, `at`, a cell, and `style`, a shape style used for colour only. A `SymbolRef` MUST appear only in cell-profile scenes, and its rows MUST be the symbol table of `spec/render-cells.md`. [just go-check]
- scene-31: The cell back end MUST set the cell `symbol` to the `unicode` glyph of the row, or to its `ascii` glyph in the ASCII charset, and a vector back end MUST never receive a `SymbolRef`. [just go-check]
- scene-32: The closed primitive set MUST be `Rect`, `RoundRect`, `Ellipse`, `Polygon`, `Polyline`, `Path`, `Text`, `MarkerRef`, `SymbolRef`, and `Group`, and a backend-specific field in the scene MUST be a defect. [just go-check]

## Shape styles

- scene-33: Colour tokens MUST be the closed list of `spec/render-cells.md`, in its rank order. [just go-check]
- scene-34: Shape styles MUST be the closed list of this table, where `line` draws the stroke, `fill` draws the shape in its fill colour token, so a shape one cell thick is filled by cell rule 2 of `spec/render-cells.md` and a larger shape is drawn as its outline in that token by cell rules 1 and 5, and `none` draws nothing; no area more than one cell thick MUST be filled. [just gen-check]

    |Style|Fill|Stroke|Cell|
    |---|---|---|---|
    |`node`|`surface`|`border`|`line`|
    |`group`|none|`border`|`line`|
    |`band`|`surface`|none|`none`|
    |`note`|`surface`|`accent`|`line`|
    |`edge`|none|`line`|`line`|
    |`rule`|none|`border`|`line`|
    |`mark`|`line`|`line`|`fill`|
    |`mark-hollow`|`bg`|`line`|`line`|
    |`ink`|`fg`|none|`fill`|
    |`ink-line`|none|`fg`|`line`|
    |`series`|`series[n]`|`line`|`fill`|
    |`series-line`|none|`series[n]`|`line`|
    |`series-tint`|`series[n]` at tint opacity|`line`|`line`|
    |`series-flow`|none|`series[n]` at tint opacity|`line`|
    |`error`|`surface`|`error`|`line`|
    |`warning`|`surface`|`warning`|`line`|
    |`success`|`surface`|`success`|`line`|
    |`plate`|`bg`|none|`none`|

## Text styles

- scene-35: Text styles MUST be the closed list below. [just gen-check]

    - `text` takes `fg`.
    - `text-muted` takes `muted`.
    - `text-inverse` takes `bg`.
    - `text-on-series` takes the choice for the active theme and the series index of the fill. The choice is `fg` when `fg` on `series[n]` reaches 4.5:1 and has the higher contrast. It is `bg` when `bg` on `series[n]` reaches 4.5:1 and has the higher contrast. Otherwise it is `plate`.

- scene-36: With the `plate` choice, the layout MUST emit a `Rect` of the text box in style `plate` directly before the `Text`, with `width` `normal`, `line` `solid`, and `series` 0, and the `Text` MUST take style `text`. [just go-check]
- scene-37: `tools/specgen` MUST compute the choice from `spec/data/themes.json` with the integer contrast rule of `spec/themes.md` and write the table `seriestext`, which holds `SeriesText{theme, series, choice}` with choice 0 for `fg`, 1 for `bg`, and 2 for `plate`, one row for each of the 20 theme names and each series index, key and sort `(theme, series)` with `theme` bytewise. [just gen-check]

## Paint constants

- scene-38: Paint constants MUST live in `spec/data/layout-constants.json` under the prefix `paint.`: `paint.tint_alpha` MUST be 102 of 255 (40 percent), the stroke widths MUST be 64 units (1 px) for `normal` and 128 units (2 px) for `emphasis`, `paint.dash_dotted_on` and `paint.dash_dotted_off` MUST be 192 units each, and `paint.dash_dashed_on` and `paint.dash_dashed_off` MUST be 512 and 256 units. [just gen-check]
- scene-39: The SVG back end MUST write the tint as opacity `0.4`, and it MUST write the dash patterns as `3 3` and `8 4` by the SVG number rule. [just go-check]
- scene-40: Every `series-line` item MUST take `line` by the `floor_mod(n, 3)` rule on its series index `n`: `solid` for 0, `dashed` for 1, and `dotted` for 2, so that series lines never rest on colour alone. [just go-check]

## Style data

- scene-41: `spec/data/styles.json` MUST hold two arrays: `shape` with rows `{name, fill, stroke, tint, cell}`, where `fill` and `stroke` are a colour token name, `series`, or `none`, `tint` is `none`, `fill`, or `stroke` and names the paint that takes `paint.tint_alpha`, and `cell` is `line`, `fill`, or `none`; and `text` with rows `{name, colour}`, where `colour` is a colour token name or `on-series`. [just gen-check]
- scene-42: A text row whose colour is `on-series` MUST resolve through `seriestext`, and `tools/specgen` MUST write the table `styles` as `Style{name, class, fill, stroke, tint, cell}` with class 0 for shape rows and 1 for text rows, a text row storing its colour in `fill`, key `name`, and sort `name` bytewise. [just gen-check]
- scene-43: Styles MUST NOT depend on the theme, and a back end MUST resolve a token through the active theme. [just theme-check]
- scene-44: `look: neo` MUST change `width` `normal` to `emphasis` and change the radius token, and it MUST change no style row; in a cell scene `look` MUST have no effect, so `width` keeps the element rule value and `r` is 0. [just go-check]

## Element style rules

- scene-45: The first rule that matches an element MUST win. A blank `width` and `line` cell MUST mean `normal`, `solid`, and a blank text style cell MUST mean `text`. [just go-check]
- scene-46: Element styles MUST be those of this table. [just go-check]

    |Element|Shape style|`width` and `line`|Text style|
    |---|---|---|---|
    |An element with a series index (table below): filled shape|`series`|`normal`, `solid`|`text-on-series` for text inside the fill|
    |An element with a series index: open line or outline without fill (xychart line plot, radar curve outline, gitgraph branch line)|`series-line`|`emphasis`; `line` by the `floor_mod(n, 3)` rule||
    |An element with a series index: area that can overlap another (venn set, radar area)|`series-tint`|`normal`, `solid`|`text`|
    |Sankey link|`series-flow`|`width` = the link width in units, `solid`||
    |Gantt task tagged `crit`; gantt today line|`error`|`normal`, `solid`|`text`|
    |Gantt task tagged `done`|`success`||`text`|
    |Gantt task tagged `active`|`note`||`text`|
    |Note (sequence, class, state)|`note`||`text`|
    |Group frame: every dump box with role `group` (subgraph, cluster, lane, composite state, namespace, boundary, fragment frame, kanban section, architecture group, treemap section)|`group`|`normal`, `solid`|title `text`|
    |Route: every dump route (edge, message, relation, link, rail, rib, spine)|`edge`|thick line kind: `emphasis`; dotted line kind: `dotted`; dashed line kind (ER non-identifying, class dependency and realization): `dashed`; else `normal`, `solid`|route label `text`|
    |Marker|from `paint` in `spec/data/markers.json`: `filled` gives `mark`, `hollow` gives `mark-hollow`, `open` gives `edge`|`normal`, `solid`||
    |Divider, compartment rule, axis line, tick, grid line, graticule, guide, lifeline|`rule`|`normal`, `solid`; a treeview guide has `width` = `treeview.line_thickness` in units (the config value times 64); a sequence fragment `else` divider is `dotted`; a state concurrency divider is `dashed`|tick, axis, and bit-number text `text-muted`|
    |Background band (gantt section band, sequence `rect` block, quadrant field, cynefin domain, journey section band)|`band`||`text`|
    |Filled symbol without a series index (state start, inner disc of state end (vector profile only), fork and join bar, junction, autonumber badge (vector profile only), railroad start and end marker, block arrow, gantt milestone)|`ink`||`text-inverse` for text on it|
    |Stroke-only symbol (built-in icon strokes, actor figure, outer ring of state end (vector profile only), journey face)|`ink-line`|icons `emphasis`; else `normal`||
    |Railroad special node|`node`|`normal`, `dashed`|`text`|
    |Every other dump box with role `node`|`node`|`normal`, `solid`|`text`|
    |Every other text|||`text`|

- scene-47: The source line kind of a route MUST give the `width` and `line` of this table, and every other route MUST be `normal`, `solid`. [just go-check]

    |Kind|Source line kind|`width`, `line`|
    |---|---|---|
    |flowchart, swimlane, agentflow, block|thick link (`==>`, `===`)|`emphasis`, `solid`|
    |flowchart, swimlane, agentflow, block|dotted link (`-.->`, `-.-`)|`normal`, `dotted`|
    |flowchart, swimlane, agentflow|invisible link (`~~~`)|no item is emitted; the route stays in the dump|
    |class|relation with a dotted line (`..`; `classDb.ts` line 867, `lineType == 1`)|`normal`, `dashed`|
    |class, state|note connector (`classDb.ts` line 825; `state/dataFetcher.ts` line 462)|`normal`, `dashed`|
    |er|non-identifying relationship (`erDb.ts` line 452)|`normal`, `dashed`|
    |requirement|every relationship except `contains` (`requirementDb.ts` lines 327 to 331)|`normal`, `dashed`|
    |usecase|relationship with a `«type»` label (`usecaseDb.ts` line 266)|`normal`, `dotted`|
    |sequence|the dotted message kinds named in the sequence line kind table (rule 7 of `spec/layout/sequence.md`)|`normal`, `dotted`|
    |gitgraph|cherry-pick link|`normal`, `dotted`|
    |every kind|every other route|`normal`, `solid`|

- scene-48: The series index MUST be taken `floor_mod 12` and MUST follow this table. [just go-check]

    |Kind|Series index|
    |---|---|
    |pie|slice index in declaration order|
    |xychart|plot index; bar and line plots count together in declaration order|
    |radar|curve index|
    |sankey|node index in order of first appearance; a link takes the index of its source node|
    |venn|set index|
    |treemap|index of the top-level section that holds the leaf; for a leaf outside a section, the leaf index|
    |gitgraph|branch index in lane order; used by commits, the branch line, and the branch label|
    |timeline|section index; without sections, the period index|
    |journey|section index|
    |gantt|section index, for task bars with no tag|
    |quadrant|0 for every point|
    |every other kind|no element has a series index|

- scene-49: `spec/data/markers.json` MUST carry three more fields per marker, `paint`, `cell`, and `ascii`, with these values. [just gen-check]

    |Markers|`paint`|`cell` (+x, -x, +y down, -y up)|`ascii`|
    |---|---|---|---|
    |`point`, `dependency`, `barb`, `barbNeo`|`filled`|▶ ◀ ▼ ▲|`> < v ^`|
    |`extension`|`hollow`|▷ ◁ ▽ △|`> < v ^`|
    |`openArrow`, `requirement_arrow`, `requirement_arrow_neo`, `hierarchy`|`open`|`> < v ^`|`> < v ^`|
    |`composition`|`filled`|◆ for all four|`*`|
    |`aggregation`|`hollow`|◇|`o`|
    |`circle`|`filled`|●|`*`|
    |`lollipop`, `hollowCircle`|`hollow`|○|`o`|
    |`requirement_contains`, `requirement_contains_neo`|`hollow`|⊕ (U+2295)|`+`|
    |`cross`|`open`|× (U+00D7)|`x`|
    |`only_one`, `only_one_neo`|`open`|`1`|`1`|
    |`zero_or_one`, `zero_or_one_neo`|`hollow`|`?`|`?`|
    |`one_or_more`, `one_or_more_neo`|`open`|`+`|`+`|
    |`zero_or_more`, `zero_or_more_neo`|`hollow`|`*`|`*`|

- scene-50: Each back end MUST draw the polygon or polyline of the marker from `spec/data/markers.json`, and no SVG `<marker>` element MUST be written. [just go-check]
- scene-51: The plain arrowhead of a route MUST be the marker `point`, whose `points` are the triangle of the arrowhead rule of `spec/render-svg.md`: the tip, then the two base points 512 units behind the tip and 256 units to each side. [just go-check]
- scene-52: The markers `extension` and `aggregation` MUST be drawn hollow, which is this project's choice, because `markers.js` does not set their fill and UML draws them hollow. [just go-check]
- scene-53: The 25 marker names MUST be `extension`, `composition`, `aggregation`, `dependency`, `lollipop`, `point`, `circle`, `cross`, `barb`, `barbNeo`, `hierarchy`, `only_one`, `zero_or_one`, `one_or_more`, `zero_or_more`, `only_one_neo`, `zero_or_one_neo`, `one_or_more_neo`, `zero_or_more_neo`, `requirement_arrow`, `requirement_contains`, `requirement_arrow_neo`, `requirement_contains_neo`, `openArrow`, and `hollowCircle`, and each marker outline MUST be a polygon or a polyline. [just gen-check]

## Cell profile elements

- scene-54: Under the cell profile a state start MUST be one `SymbolRef` `disc` in style `ink`, and a state end MUST be one `SymbolRef` `bullseye` in style `ink`, never a ring and a disc. [just go-check]
- scene-55: Under the cell profile a service of the architecture kind MUST be one `Rect` of `icon_width` by `icon_height` cells, 7 by 3, in the node style of its element row, and its icon MUST be one `SymbolRef` in the centre cell `(x + floor_div(w, 2), y + floor_div(h, 2))`, where `(x, y)` is the top-left cell and `w` and `h` are the size of the `Rect`. [just go-check]
- scene-56: Under the cell profile a built-in icon MUST be one `SymbolRef` with the icon name in style `ink-line`, and a pack icon MUST be one `SymbolRef` `unknown` in style `ink`, so an icon MUST NOT be a `Text` item, because label text prints unchanged in both charsets. [just go-check]
- scene-57: Under the cell profile a message number MUST have no shape, and its label MUST be `(k) ` followed by the message text, or `(k)` alone when the message has no text, measured and placed with that prefix. [just go-check]
