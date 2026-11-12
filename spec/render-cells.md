# Cell (text) back end

This file fixes the cell canvas, the glyph join table, label placement, the braille raster, the cell mapping of scene items, and text colour.

## Scope and canvas record

- render-cells-01: The mapping of this file MUST apply to a scene whose profile is `cell`; a kind with text strategy `braille raster` MUST use the braille rule of this file on its vector scene. [just go-check]
- render-cells-02: Every rasteriser write MUST go through `put(c, r, f)`, which MUST apply `f` only when `0 <= c < W` and `0 <= r < H`. [just proofs: cells_inside_canvas]
- render-cells-03: A canvas of `W` columns and `H` rows MUST hold, in each cell, `mask` (four bits, N = 1, E = 2, S = 4, W = 8), `style` (`none` = 0, `dotted` = 1, `rounded` = 2, `light` = 3, `heavy` = 4, `double` = 5), `dots` (eight braille bits), `label` (nothing, one grapheme cluster with its cell width of 1 or 2, or the continuation marker for the second cell of a width-2 cluster), and `symbol` (0 or one code point). [just lean-parity]
- render-cells-04: `mergeCell` MUST OR `mask`, take the larger `style` code, OR `dots`, and take the larger `symbol`, and it MUST NOT change `label`. [just proofs: canvas_merge_order_independent]
- render-cells-05: The code point of a symbol name MUST be `Join.symbol(charset, name)`, which reads the `unicode` or `ascii` column of the `cellsymbols` table. [just gen-check]
- render-cells-06: `Canvas.putSymbol g c r s` MUST be `put(c, r, f)`, where `f` sets `symbol` to the larger of its current value and `s`. [just proofs: putSymbol_changes_symbol_only]

## Cell geometry

- render-cells-07: Scene units MUST be cells, so `W` and `H` MUST equal the scene extent. [just proofs: canvas_size_eq_scene_extent]
- render-cells-08: A horizontal segment from `(x0, y)` to `(x1, y)` with `x0 < x1` MUST set `E` on cells `x0..x1-1` and `W` on cells `x0+1..x1`, and a vertical segment MUST set `S` and `N` in the same way. [just lean-parity]
- render-cells-09: Lean `Canvas.segment` MUST make every such write through `put`, and each primitive's style MUST be merged into every cell it touches. [just lean-parity]
- render-cells-10: A `rect` covering cells `x` to `x+w-1` and `y` to `y+h-1` MUST be four orthogonal segments along its sides when `w >= 2` and `h >= 2`, and a rect with `w = 1` or `h = 1` MUST follow cell rule 2 of this file. [just lean-parity]
- render-cells-11: A `polyline` MUST be treated as a list of orthogonal segments. [just lean-parity]

## Glyphs

- render-cells-12: `glyph(charset, style, mask)`, which is Lean `Join.glyph`, MUST read the table generated from `spec/data/glyph-join.json`, whose arms equal the mask in every style. [just proofs: join_glyph_matches_mask]

  |Mask|Arms|light|heavy|double|rounded|dotted|ascii|ascii_dotted|
  |---|---|---|---|---|---|---|---|---|
  |0|none|space|space|space|space|space|space|space|
  |1|N|╵|╹|╵|╵|╵|`\|`|`:`|
  |2|E|╶|╺|╶|╶|╶|`-`|`.`|
  |3|N E|└|┗|╚|╰|└|`+`|`+`|
  |4|S|╷|╻|╷|╷|╷|`\|`|`:`|
  |5|N S|│|┃|║|│|┆|`\|`|`:`|
  |6|E S|┌|┏|╔|╭|┌|`+`|`+`|
  |7|N E S|├|┣|╠|├|├|`+`|`+`|
  |8|W|╴|╸|╴|╴|╴|`-`|`.`|
  |9|N W|┘|┛|╝|╯|┘|`+`|`+`|
  |10|E W|─|━|═|─|┄|`-`|`.`|
  |11|N E W|┴|┻|╩|┴|┴|`+`|`+`|
  |12|S W|┐|┓|╗|╮|┐|`+`|`+`|
  |13|N S W|┤|┫|╣|┤|┤|`+`|`+`|
  |14|E S W|┬|┳|╦|┬|┬|`+`|`+`|
  |15|N E S W|┼|╋|╬|┼|┼|`+`|`+`|

- render-cells-13: In style `rounded`, masks 3, 6, 9, and 12 MUST print ╰, ╭, ╯, and ╮, and every other mask MUST use the light column. [just gen-check]
- render-cells-14: In style `dotted`, mask 5 MUST print `┆` (U+2506), mask 10 MUST print `┄` (U+2504), and every other mask MUST use the light glyph, so the arms equal the mask. [just go-check]
- render-cells-15: Because Unicode has no double stub, masks 1, 2, 4, and 8 in style `double` MUST print the light stub. [just gen-check]
- render-cells-16: Mask 0 MUST print U+0020 in every style. [just go-check]
- render-cells-17: The `ascii` charset MUST ignore style, except style `dotted`: mask 0 MUST print U+0020, masks 1, 4, and 5 MUST print `|`, masks 2, 8, and 10 MUST print `-`, and every other mask MUST print `+`. [just go-check]
- render-cells-18: In style `dotted`, the `ascii` charset MUST print masks 2, 8, and 10 as `.`, masks 1, 4, and 5 as `:`, and every other non-zero mask as `+`. [just go-check]
- render-cells-19: An ASCII lookup MUST use the `dotted` rows when the cell style is `dotted`, and the style 0 rows otherwise; the generated `glyphjoin` table MUST have unicode style 0 with one row for mask 0, unicode styles 1 to 5 with 16 rows each, and ascii rows for style 0 and for style `dotted` with 16 rows each, keyed and sorted by `(charset, style, mask)`. [just gen-check]

## Line style of an item

- render-cells-20: The line style of an item MUST be set by the first rule of this list that matches. [just go-check]

  1. `line` = `double` gives `double`.
  2. `line` = `dotted` or `dashed` gives `dotted`.
  3. `width` = `emphasis` gives `heavy`.
  4. A `RoundRect` gives `rounded`.
  5. Any other item gives `light`.

- render-cells-21: In the cell profile the `r` field of a `RoundRect` MUST be 0, and the primitive type alone MUST select rounded corners. [just go-check]
- render-cells-22: The line kind MUST select the glyph before the width does, so a dotted series line is not drawn heavy. [just go-check]

## Limits of cell output

- render-cells-23: `dashed` and `dotted` MUST print with the same glyphs, so two such lines differ by their labels only. [just go-check]
- render-cells-24: A filled shape wider and taller than one cell MUST print as its outline, so a gantt tag (`crit`, `done`, `active`) and a series index change only the colour of a bar, and nothing when colour is off. [just go-check]
- render-cells-25: The label of each element MUST carry its identity in every mode. [just go-check]

## Per primitive

- render-cells-26: An item whose style has `cell` = `none` MUST draw nothing; otherwise the cell rules of this list MUST apply. [just go-check]

  1. `Rect` or `RoundRect` with `w >= 2` and `h >= 2`: four sides by the cell-geometry rule of this file, in the item's line style. When the style `cell` is `fill`, the four sides take the fill token. No area is filled.
  2. `Rect` or `RoundRect` with `w = 1` or `h = 1`: when the style `cell` is `fill`, every cell gets `dots = 0xFF` (prints `⣿`, or `#` in ASCII) and the cells take the fill token; a label may still overwrite these cells by the label rule. Otherwise it is one segment along its longer side through its cells, in the item's line style. A 1 by 1 hollow rect sets `symbol` to `box-hollow` (`□`, ASCII `o`).
  3. `Polyline` whose segments are all axis-aligned: the cell-geometry rule, in the item's line style.
  4. One-cell symbols. An `Ellipse` with `rx <= 1` and `ry <= 1` sets `symbol` at cell `(cx, cy)`: `disc` (`●`, ASCII `*`) when the style `cell` is `fill`, else `ring` (`○`, ASCII `o`). A `Polygon` whose bounding box is at most 1 by 1 cell sets `symbol` at its top-left cell: `diamond` (`◆`, ASCII `*`) when the style `cell` is `fill`, else `diamond-hollow` (`◇`, ASCII `o`). These rules are the default for every other one-cell shape.
  5. Every other shape (a `Polyline` with a sloped segment, a larger `Ellipse`, a larger `Polygon`, a `Path`) is stroked as dots with the Stroke rule of this file. An `Ellipse` is first the 64-point polygon of the Ellipse rule, computed in dot space with centre `(2cx, 4cy + 2)` and radii `2rx` and `4ry`. A `C` segment uses the Cubic rule and an `A` segment uses the Arc rule, both in dot space. When the style `cell` is `fill`, the dots take the fill token. No area is filled.
  6. `MarkerRef`: sets `symbol` at cell `at` to the marker's `cell` glyph for its axis, or to the `ascii` glyph in the ASCII charset. Each arrowhead replaces the last cell of its route.
  7. `Text`: a label for the label rule of this file, using the item's `rect`, `align`, and `lines`. Bold and italic are not shown.
  8. `SymbolRef`: sets `symbol` at cell `at` to the row's `unicode` glyph, or to its `ascii` glyph in the ASCII charset.

- render-cells-27: A `SymbolRef` MUST appear only in cell-profile scenes, and a vector back end MUST never receive one. [just go-check]
- render-cells-28: A `plate` rect MUST draw nothing in the cell profile. [just go-check]
- render-cells-29: A braille kind MUST use the braille rule of this file on the vector scene, and for those kinds the Cubic rule MUST apply and the style `cell` column MUST select the parts drawn: `fill` draws the fill then the stroke, `line` draws the stroke only, and `none` draws nothing. [just go-check]
- render-cells-30: The symbol rows of `spec/data/cell-symbols.json`, with their generated table `cellsymbols`, MUST be these. [just go-check]

  |Name|Unicode|ASCII|
  |---|---|---|
  |`disc`|● U+25CF|`*`|
  |`ring`|○ U+25CB|`o`|
  |`bullseye`|◉ U+25C9|`@`|
  |`diamond`|◆ U+25C6|`*`|
  |`diamond-hollow`|◇ U+25C7|`o`|
  |`box-hollow`|□ U+25A1|`o`|
  |`cloud`|☁ U+2601|`~`|
  |`database`|▤ U+25A4|`=`|
  |`disk`|◎ U+25CE|`o`|
  |`internet`|◊ U+25CA|`*`|
  |`server`|▥ U+25A5|`#`|
  |`unknown`|`?`|`?`|

- render-cells-31: Every glyph of the marker table, the symbol table, `┄`, `┆`, and `⣿` MUST have cell width 1 under the Cluster width rule, because it has East Asian Width `A` or `N` and no `Emoji_Presentation`. [just go-check]

## Symbols and icons under the cell profile

- render-cells-32: A state start MUST be one `SymbolRef` `disc` with style `ink`. [just go-check]
- render-cells-33: A state end MUST be one `SymbolRef` `bullseye` with style `ink`, and two symbols in one cell MUST merge to the larger code point. [just go-check]
- render-cells-34: An architecture service MUST be one `Rect` of `icon_width` by `icon_height` cells (7 by 3) in the node style of its element row, with its icon as one `SymbolRef` in the centre cell `(x + floor_div(w, 2), y + floor_div(h, 2))`, and its label MUST keep the placement of the architecture label rule. [just go-check]
- render-cells-35: A built-in icon MUST be one `SymbolRef` with the icon name and style `ink-line`, never a `Text` item, because label text prints unchanged in both charsets. [just go-check]
- render-cells-36: A pack icon MUST be one `SymbolRef` `unknown` with style `ink`. [just go-check]
- render-cells-37: A message number MUST have no shape in the cell profile: the label MUST be `(k) ` followed by the message text, or `(k)` alone when the message has no text, measured and placed with that prefix. [just go-check]

## Label placement

- render-cells-38: Placement MUST run after lines, dots, and symbols, in declaration order. [just go-check]
- render-cells-39: For the cell profile the box in cells MUST be `c0 = rect.x`, `w = rect.w`, `r0 = rect.y`, and line `k` MUST start on row `r0 + k`. [just go-check]
- render-cells-40: For a braille raster the box in units MUST give `c0 = floor_div(rect.x, 512)`, `w = ceil_div(rect.x + rect.w, 512) - c0`, and `r0 = floor_div(rect.y, 1024)`, and line `k` MUST start on row `floor_div(rect.y + k * LH, 1024)`, where `LH` is the line height of the item's role in units and is at least 1024 for every role. [just go-check]
- render-cells-41: The start column MUST be `Place.lineStart(align, c0, w, lineW)`, where `lineW` is the cell width of the cluster list of line `k`: `c0` for `start`, `c0 + floor_div(w - lineW, 2)` for `middle`, and `c0 + w - lineW` for `end`. [just proofs: lineStart_inside_rect]
- render-cells-42: The start-column formulas MUST hold for every `lineW`, so a line wider than its box MUST start left of `c0` for `middle` and `end`. [just go-check]
- render-cells-43: Clusters MUST be written left to right from the start column, and a cluster of cell width `cw` at column `c` MUST be written only when `0 <= c`, `c + cw <= W`, and every cell from `c` to `c + cw - 1` on that row has `mask = 0`, `symbol = 0`, and no `label`. [just proofs: label_never_overwrites_border]
- render-cells-44: Writing MUST set `label` on the first cell and, for `cw = 2`, the continuation marker on the second cell. [just go-check]
- render-cells-45: A cluster that cannot be written MUST be counted, never dropped silently: `placeAll` MUST return the number of such clusters, and the Go and Rust cell renderers MUST return the same number. [just go-check]
- render-cells-46: A label MUST be truncated when that number is above 0, and `hard_ok` MUST require 0. [just go-check]
- render-cells-47: A label MAY overwrite the `dots` of a cell, and it MUST NOT write into a cell with `mask != 0` or `symbol != 0`. [just proofs: label_never_overwrites_border]
- render-cells-48: After `placeAll`, no cell MUST hold text from two different labels. [just proofs: place_labels_disjoint]

## Braille raster

- render-cells-49: The kinds marked `braille raster`, which are `xychart` line plots, `pie`, `radar`, `sankey`, and `venn`, MUST use this braille rule, whose input is the scene under the vector profile in units of 1/64 px. [just go-check]
- render-cells-50: The canvas MUST be `W = ceil_div(extent_w, 512)` by `H = ceil_div(extent_h, 1024)` cells, where a cell is 8 px by 16 px and a dot is 4 px square, which is 256 units; dot `(i, j)`, with `0 <= i < 2W` and `0 <= j < 4H`, MUST belong to cell `(floor_div(i, 2), floor_div(j, 4))` and cover units `[256 i, 256 i + 256) x [256 j, 256 j + 256)`. [just go-check]
- render-cells-51: The braille bits MUST be indexed by dot column and row inside the cell as `(0,0)` = 0x01, `(0,1)` = 0x02, `(0,2)` = 0x04, `(1,0)` = 0x08, `(1,1)` = 0x10, `(1,2)` = 0x20, `(0,3)` = 0x40, `(1,3)` = 0x80, and a cell's `dots` MUST be the OR of its set bits. [just proofs: braille_bit_roundtrip]
- render-cells-52: A cell with `dots = 0` MUST print U+0020; otherwise it MUST print U+2800 + `dots` in the unicode charset and `#` in the ascii charset. [just proofs: braille_bit_roundtrip]
- render-cells-53: Dot `(i, j)` MUST have sample point `(256 i + 128, 256 j + 128)` in units, and a fill MUST set the dot when its sample point is inside the shape. [just go-check]
- render-cells-54: The braille rule MUST use `sin_q15` of `spec/geometry-kernel.md` and no other table, with angles in 1/65536 turn and table index `floor_div(angle, 16)`. [just lean-parity]
- render-cells-55: The Arc rule MUST hold in any integer space, with integer centre `(cx, cy)`, radius `r`, start angle `a0`, and sweep `s` in 1/65536 turn in the coordinates of its caller, so a caller in units and a caller in dot space use the same formulas: `n = max(4, ceil_div(|s|, 1024))`, and vertex `k`, for `0 <= k <= n`, MUST have angle `a_k = a0 + floor_div(s * k, n)`, `x = cx + floor_div(2 * r * sin_q15(a_k + 16384) + 32768, 65536)`, and `y = cy + floor_div(2 * r * sin_q15(a_k) + 32768, 65536)`. [just go-check]
- render-cells-56: `Braille.ellipse` MUST have integer centre `(cx, cy)` and integer radii `rx` and `ry` in the coordinates of its caller, and its polygon MUST have 64 vertices, where vertex `j`, for `0 <= j < 64`, has angle `a = j * 1024` in 1/65536 turn, `x = cx + floor_div(rx * cos_q15(a), 32768)`, and `y = cy - floor_div(ry * sin_q15(a), 32768)`; fill and stroke MUST use these vertices as a closed polygon. [just go-check]
- render-cells-57: `Braille.fill` MUST include the edge from `v_(m-1)` back to `v_0`, MUST count an edge `(x1, y1)` to `(x2, y2)` when `(y1 <= py < y2)` or `(y2 <= py < y1)` and `((x2 - x1) * (py - y1) + (x1 - px) * (y2 - y1)) * (y2 - y1) > 0`, and MUST treat the sample `(px, py)` as inside when the count is odd; a filled arc MUST be the polygon whose vertices are the centre followed by the arc vertices. [just proofs: fill_raster_inside]
- render-cells-58: `Braille.stroke` MUST set the dots of an integer Bresenham line between each pair of consecutive vertices, mapping each vertex to a dot by `floor_div(v, 256)`, with `dx = |x1 - x0|`, `sx = 1 if x0 < x1 else -1`, `dy = -|y1 - y0|`, `sy = 1 if y0 < y1 else -1`, and `err = dx + dy`; each step MUST set the dot `(x0, y0)`, stop when it equals `(x1, y1)`, compute `e2 = 2 * err`, then apply `err = err + dy` and `x0 = x0 + sx` when `e2 >= dy`, and apply `err = err + dx` and `y0 = y0 + sy` when `e2 <= dx`; the fuel MUST be `|dx| + |dy| + 1`, and stroke width MUST be ignored. [just proofs: line_raster_connected]
- render-cells-59: Products in the fill and the Bresenham steps MUST be checked against int64, and an overflow MUST be the kernel's `overflow` error (`geom.ErrOverflow`, `GeomError::Overflow`, `LayoutError.overflow`); a dot outside the canvas MUST be dropped by `put`, and paint order MUST NOT change the result, because dots combine by OR. [just go-check]
- render-cells-60: For a scene with profile `cell`, the dot grid MUST have `2W` columns and `4H` rows for the canvas of `W` by `H` cells, a point `(x, y)` in cells MUST map to dot `(2x, 4y + 2)`, and the Stroke rule MUST use these dots directly in place of `floor_div(v, 256)`. [just go-check]
- render-cells-61: `Braille.cubic` MUST turn a cubic from `P0` with controls `P1`, `P2` to `P3` into 16 straight segments, where point `k`, for `0 <= k <= 16`, is `floor_div((16-k)^3 * P0 + 3 * k * (16-k)^2 * P1 + 3 * k^2 * (16-k) * P2 + k^3 * P3 + 2048, 4096)` on each axis. [just go-check]

## Render and serialisation

- render-cells-62: The render MUST draw each primitive in scene order and then place labels, and it MUST write each row `r` from column 0 to `W-1` by the first rule of this list that matches. [just go-check]

  1. A continuation cell prints nothing.
  2. A cell with `label` prints the cluster text.
  3. A cell with `symbol != 0` prints that code point.
  4. A cell with `mask != 0` prints its glyph.
  5. A cell with `dots != 0` prints its braille glyph.
  6. Any other cell prints U+0020.

- render-cells-63: Each row MUST drop its trailing U+0020 characters and MUST end with U+000A, and the output MUST have no CR and no BOM. [just go-check]
- render-cells-64: A canvas with `H = 0` MUST write zero bytes. [just go-check]
- render-cells-65: Label text MUST print unchanged in both charsets. [just go-check]
- render-cells-66: The order inside a group MUST be the order that `spec/scene.md` fixes. [just go-check]
- render-cells-67: The Lean text renderer MUST cover the cell and braille canvases, the unicode and ascii glyphs including the `dotted` style, cell symbols, sloped strokes, cubic curves, arcs, and ellipses, label placement and alignment, and the bytes of text output, and Go MUST match its bytes for every accepted corpus file; it MUST NOT cover colour escape sequences, SVG, PNG, terminal graphics, `emd view`, or CLI flags other than `--charset`, which the Go and Rust tests cover. [just lean-parity]
- render-cells-68: For every accepted corpus file, `bin/emd-go layout --stage model --profile cell FILE | geomcheck text --charset C` MUST equal `bin/emd-go render -e text --charset C --color never FILE` for `C` in `unicode` and `ascii`, and `parity` MUST carry the same equality from Go to Rust. [just lean-parity]

## Text colour

- render-cells-69: The text colour rules MUST apply to `render -e text` and to the viewer's cell mode when the colour mode is not `None`, and colour MUST NOT change which characters are printed; the Lean text renderer MUST NOT implement these rules. [just go-check: TestTextColour]
- render-cells-70: A status or series token whose `strokeok` value is 0 in the active theme MUST be replaced by `line` before any other rule of this section. [just go-check]
- render-cells-71: The colour tokens MUST be, rank 0 first: `bg`, `fg`, `line`, `accent`, `muted`, `surface`, `border`, `series0` to `series11`, `error`, `warning`, `success`. [just go-check]
- render-cells-72: A `label` cell MUST take the token of its text style: `text` gives `fg`, `text-muted` gives `muted`, `text-inverse` gives `bg`, and `text-on-series` gives `fg` or `bg` from the `seriestext` choice of its theme and series index, so a `plate` choice gives `fg`. [just go-check]
- render-cells-73: A `symbol`, `mask`, or `dots` cell MUST take the fill token of the item that wrote it when the style `cell` of that item is `fill`, and the stroke token of that item otherwise. [just go-check]
- render-cells-74: When two items write one cell, the token with the larger rank MUST win, and a label token MUST always win over a line token. [just go-check]
- render-cells-75: Each row MUST start with current token `fg`, and before a printed character that is not U+0020 the writer MUST write the SGR sequence of the cell's token when it differs from the current token and MUST make it the current token. [just go-check: TestTextColour]
- render-cells-76: Spaces MUST NOT change the colour, and at the end of each row the writer MUST write `ESC [ 39 m` before the line feed when the current token is neither `fg` nor `bg`, then set the current token to `fg`. [just go-check: TestTextColour]
- render-cells-77: Tokens `fg` and `bg` MUST both print the terminal default foreground, `ESC [ 39 m`, in every mode, the background colour MUST never be set, and `bg` MUST count as `fg` for the current-token comparison and the row-end rule. [just go-check: TestTextColour]
- render-cells-78: Truecolor mode MUST write `ESC [ 38 ; 2 ; R ; G ; B m` with decimal channel values and no spaces in the real bytes. [just go-check: TestTextColour]
- render-cells-79: 256-colour mode MUST write `ESC [ 38 ; 5 ; N m` with `N` from the tmux rule (`colour_find_rgb` in tmux `colour.c`), given by the rules of this list. [just go-check: TestTextColour]

  - `q(v) = 0` when `v < 48`; `1` when `v < 114`; else `floor_div(v - 35, 40)`.
  - Cube levels are `0, 95, 135, 175, 215, 255`, at indices 0 to 5.
  - `qr`, `qg`, and `qb` are `q` of the red, green, and blue channels.
  - When all three channels equal their cube level, `N = 16 + 36 * qr + 6 * qg + qb`.
  - Otherwise `avg = floor_div(r + g + b, 3)`, `gi` is 23 when `avg > 238` and `max(0, floor_div(avg - 3, 10))` otherwise, and `grey = 8 + 10 * gi`; then `N = 232 + gi` when the squared distance from `(grey, grey, grey)` to the colour is smaller than the squared distance from the cube colour, else `N = 16 + 36 * qr + 6 * qg + qb`.

- render-cells-80: The 256-colour worked example MUST hold: `#8b8d98` gives `N = 246`, because `q` of 139, 141, and 152 is 2 for each, the cube level 135 is not equal to any channel, `avg` is 144, `gi` is 14, `grey` is 148, the squared distance to `(148, 148, 148)` is 146, the squared distance to `(135, 135, 135)` is 341, and 146 < 341, so `N = 232 + 14 = 246`. [just go-check: TestTextColour]
- render-cells-81: 16-colour mode MUST take the nearest of the 16 xterm default colours by squared distance, with the lowest index winning a tie, MUST write `ESC [ 3X m` for indices 0 to 7, and MUST write `ESC [ 9X m` with `X = index - 8` for indices 8 to 15. [just go-check: TestTextColour]

  |Index|RGB|Index|RGB|
  |---|---|---|---|
  |0|(0,0,0)|8|(127,127,127)|
  |1|(205,0,0)|9|(255,0,0)|
  |2|(0,205,0)|10|(0,255,0)|
  |3|(205,205,0)|11|(255,255,0)|
  |4|(0,0,238)|12|(92,92,255)|
  |5|(205,0,205)|13|(255,0,255)|
  |6|(0,205,205)|14|(0,255,255)|
  |7|(229,229,229)|15|(255,255,255)|

- render-cells-82: The truecolor worked example MUST hold: with `border` at `#8b8d98`, so `R = 139`, `G = 141`, `B = 152`, the row of a `border` `│`, two spaces, the label `Hi` in `fg`, two spaces, and a `border` `│` MUST give these bytes followed by U+000A, where `ESC` is 0x1B. [just go-check: TestTextColour]

  ```
  ESC[38;2;139;141;152m│  ESC[39mHi  ESC[38;2;139;141;152m│ESC[39m
  ```

- render-cells-83: The byte sequence of that example MUST follow from the rules: the first `│` changes the token from `fg` to `border`, so its sequence is written; the two spaces change nothing; the `H` has token `fg`, so `ESC[39m` is written before it; the `i` and the two spaces print with no change; the last `│` changes the token back to `border`, so its sequence is written; and at the row end the current token is `border`, so `ESC[39m` is written before the line feed, where `│` is U+2502 with UTF-8 bytes E2 94 82. [just go-check: TestTextColour]
- render-cells-84: Go `TestTextColour` and Rust `text_colour` MUST render one fixture in each mode and compare with the golden files `internal/cells/testdata/colour/<mode>.txt`, which both languages read, and a second test MUST strip every SGR sequence and compare with the colour-off output. [just go-check: TestTextColour]

## Theorems

- render-cells-85: `canvas_merge_order_independent` MUST hold: `mergeAll l1 = mergeAll l2` for every `l1` that is a `List.Perm` of `l2`, because `mergeCell` is commutative, associative, and idempotent, with `symbol` combined by `max`. [just proofs: canvas_merge_order_independent]
- render-cells-86: `cells_inside_canvas` MUST hold: every cell changed by a rasteriser write satisfies `0 <= c < W` and `0 <= r < H`, because every write goes through `put`, which tests the bounds before it applies `f`. [just proofs: cells_inside_canvas]
- render-cells-87: `putSymbol_changes_symbol_only` MUST hold: for every canvas `g`, every cell `(c, r)` in it, every code point `s`, and every cell position `(c', r')`, if `(c', r') != (c, r)` then `(Canvas.putSymbol g c r s).at c' r' = g.at c' r'`, and `(Canvas.putSymbol g c r s).at c r` has the same `mask`, `style`, `dots`, and `label` as `g.at c r`. [just proofs: putSymbol_changes_symbol_only]
- render-cells-88: `join_glyph_matches_mask` MUST hold: for every `mask` in `0..15` and every unicode style in `{light, heavy, double, rounded, dotted}`, the arms of `glyph style mask` equal `mask`, checked by `decide` over the 16 by 5 table. [just proofs: join_glyph_matches_mask]
- render-cells-89: `place_labels_disjoint` MUST hold: after `placeAll`, no cell holds text from two different labels, by induction over the declaration order. [just proofs: place_labels_disjoint]
- render-cells-90: `label_never_overwrites_border` MUST hold: a cell that holds label text had `mask = 0` and `symbol = 0` before `placeAll`, and `placeAll` leaves every `mask` and `symbol` unchanged. [just proofs: label_never_overwrites_border]
- render-cells-91: `lineStart_inside_rect` MUST hold: for every `align` in `start`, `middle`, `end`, and integers `x`, `w`, `lineW` with `0 <= lineW <= w`, `x <= Place.lineStart(align, x, w, lineW)` and `Place.lineStart(align, x, w, lineW) + lineW <= x + w`. [just proofs: lineStart_inside_rect]
- render-cells-92: `braille_bit_roundtrip` MUST hold: for every `b` in `1..255`, the bits of the glyph U+2800 + `b` equal `b`, and `b = 0` prints U+0020, checked by `decide` over the 256 values. [just proofs: braille_bit_roundtrip]
- render-cells-93: `line_raster_connected` MUST hold: the dots set by the integer line rasteriser contain both endpoints, and consecutive dots differ by at most 1 in x and in y, by induction on the fuel `|dx| + |dy| + 1`. [just proofs: line_raster_connected]
- render-cells-94: `fill_raster_inside` MUST hold: every dot set by the fill of a polygon lies inside the bounding box of the polygon's vertices, because a sample point accepted by the even-odd test lies between the minimum and maximum vertex coordinates. [just proofs: fill_raster_inside]
- render-cells-95: `canvas_size_eq_scene_extent` MUST hold: in the cell profile, `W` equals the scene extent width and `H` equals the scene extent height, because the cell profile uses one scene unit per cell. [just proofs: canvas_size_eq_scene_extent]
- render-cells-96: `text_valid` MUST hold: for every scene `S` that satisfies `HardConstraints` under the cell profile, the rendered canvas has no cell holding text from two labels and no primitive cell outside the canvas. [just proofs: text_valid]
- render-cells-97: Each theorem name of this file MUST be listed in `proofs/theorems.txt`. [just proofs]
