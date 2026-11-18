# SVG back end

This file fixes the structure of the SVG document that the SVG back end writes for a vector scene.

## Inputs and allowed differences

- render-svg-01: The back end MUST read only the scene parts `profile`, `canvas`, and `items`, and MUST NOT read `boxes`, `routes`, or `labels`. [just go-check]
- render-svg-02: A scene given to the back end MUST NOT hold a `SymbolRef`, because a vector back end never receives one. [just go-check]
- render-svg-03: `RenderSVG` and `render_svg` MUST lay out and draw under the vector profile, and they MUST ignore the `Profile` option. [just go-check]
- render-svg-04: The Go and Rust SVG byte streams MAY differ for the same scene. [just parity]
- render-svg-05: The `Background` option MUST become the `.emd-bg` fill when it is a hex colour `#rgb` or `#rrggbb`, and the theme `bg` colour MUST be used otherwise. [just go-check]
- render-svg-06: Every `id` attribute MUST begin with the `IDPrefix` option value, which is `""` for no prefix, so that several diagrams share one page. [just go-check]

## Document order

- render-svg-07: The root element MUST be `<svg>` with the attributes `xmlns`, `viewBox` (`0 0 W H`), `width`, `height`, `font-family`, and the accessibility attributes of this file. [just go-check]
- render-svg-08: `<title id='PREFIXtitle'>` MUST follow the root, with the text that the accessibility rule of this file fixes. [just theme-check: TestCorpusSVGTitles]
- render-svg-09: `<desc id='PREFIXdesc'>` MUST follow the `<title>` only when `accDescr` is not empty. [just go-check]
- render-svg-10: One `<style>` element MUST follow the title and the optional description. [just go-check]
- render-svg-11: The background `<rect class='emd-bg' x='0' y='0' width='W' height='H'/>` MUST follow the `<style>` element. [just go-check]
- render-svg-12: One `<g class='emd-ROLE' id='PREFIXgN'>` MUST follow for each scene group, in item order, where `ROLE` is the group role and `N` is the 0-based group index. [just go-check]
- render-svg-13: Inside a group, elements MUST keep the order that `spec/scene.md` fixes. [just go-check]

## Style block

- render-svg-14: The `<style>` element MUST hold, in this order, `.emd-bg`, one rule for each shape style and each text style that the document uses in the order of the style tables, and the three text role rules `.emd-t-title`, `.emd-t-label`, and `.emd-t-body`. [just go-check]
- render-svg-15: A shape style class MUST be `emd-s-STYLE`, and a series style class MUST be `emd-s-STYLE-N`, where `N` is the series index. [just go-check]
- render-svg-16: A text role rule MUST set `font-weight` only, from the role table of `spec/text-measurement.md`, because a class rule would override the `font-size` attribute. [just go-check]
- render-svg-17: A shape rule MUST set `fill` and `stroke` from its row in the `shape` array of `spec/data/styles.json`: a colour token MUST give its hex colour, `series` MUST give the colour of series `N`, and `none` MUST give `none`. [just go-check]
- render-svg-18: A shape rule MUST NOT set `stroke-width`, because a class rule would override the attribute. A shape rule with a stroke MUST set `stroke-linecap:round` and `stroke-linejoin:round`, to match the raster stroke convention. Text rules and shape rules without a stroke MUST NOT set these properties. [just go-check]
- render-svg-19: A row whose `tint` is `fill` MUST also set `fill-opacity:0.4`, and a row whose `tint` is `stroke` MUST also set `stroke-opacity:0.4`, where 0.4 is `paint.tint_alpha` divided by 255. [just go-check]
- render-svg-20: Every colour in the document MUST be a 6-digit lowercase hex value from the active theme. [just go-check]
- render-svg-21: A text rule MUST set `fill` from its row in the `text` array of `spec/data/styles.json`; the value `on-series` MUST give the `seriestext` choice that `spec/scene.md` defines for the active theme and series `N`, and a series whose choice is `plate` MUST never use that rule. [just go-check]
- render-svg-22: The document MUST NOT use `foreignObject`, `color-mix()`, CSS custom properties, scripts, external resources, or filters. [just go-check]

## Primitive mapping

- render-svg-23: A scene shape primitive MUST give the element of this table. [just go-check]

  |Scene primitive|SVG element|
  |---|---|
  |`Rect`|`<rect>`|
  |`RoundRect`|`<rect>` with `rx` and `ry` set to `r`|
  |`Ellipse`|`<ellipse>`|
  |`Polygon`|`<polygon>`|
  |`Polyline` with `corner` 0|`<polyline>`|
  |`Polyline` with `corner` above 0|`<path>`|

- render-svg-24: A `Polyline` with `corner` above 0 MUST give a `<path>` whose interior corners follow the corner rule of this file, with the `corner` field as the radius limit and a sharp corner when the radius is 0. [just go-check]
- render-svg-25: A `Path` primitive MUST give `<path>`, and its `M`, `L`, `C`, and `Z` commands MUST keep their letters. [just go-check]
- render-svg-26: A scene `A cx cy r a0 sweep` MUST give `A r r 0 LARGE SWEEP x y`, where `x y` is vertex `n` of the Arc rule of `spec/render-cells.md`, `LARGE` is 1 when `|sweep| > 32768` and 0 otherwise, and `SWEEP` is 1 when `sweep > 0` and 0 otherwise. [just go-check]
- render-svg-27: The layout MUST emit an `M` or `L` command to vertex 0 of the Arc rule directly before each `A` command, and `|sweep|` MUST be below 65536. [just go-check]
- render-svg-28: A full circle MUST be an `Ellipse`, never an `A` command of a full turn. [just go-check]
- render-svg-29: A `MarkerRef` MUST give `<polygon>` for a marker whose `paint` is `filled` or `hollow`, and `<polyline>` for a marker whose `paint` is `open`, one element per contour, where the `breaks` of its row in `spec/data/markers.json` list the point indices at which a new contour starts, with the `points` of the row rotated by one of the four right-angle rotations of its `axis` and translated to `at`. [just go-check]
- render-svg-30: A marker MUST NOT use a `transform` attribute, and the document MUST NOT hold an SVG `<marker>` element. [just go-check]
- render-svg-31: A marker element MUST take the class `emd-s-mark` for `filled`, `emd-s-mark-hollow` for `hollow`, and `emd-s-edge` for `open`. [just go-check]
- render-svg-32: A `Text` item MUST give one `<text>` element with one `<tspan>` element per line. [just go-check]

## Shape attributes

- render-svg-33: `class` MUST always appear on a shape. [just go-check]
- render-svg-34: `stroke-width` MUST appear on every shape whose style has a stroke, and it MUST be `1` for `normal`, `2` for `emphasis`, or the integer width in px by the number rule. [just go-check]
- render-svg-35: `stroke-dasharray` MUST be `3 3` for `dotted`, from `paint.dash_dotted_on` and `paint.dash_dotted_off` of 192 units each, and `8 4` for `dashed`, from `paint.dash_dashed_on` and `paint.dash_dashed_off` of 512 and 256 units. [just go-check]
- render-svg-36: `fill='none'` MUST NOT be written, because the class sets the fill. [just go-check]

## Text

- render-svg-37: The class of a text element MUST be `emd-t-ROLE emd-s-STYLE`, and a `Text` whose style is `text-on-series` MUST use `emd-t-ROLE emd-s-text-on-series-N`, where `N` is its series index. [just go-check]
- render-svg-38: A label whose series choice is `plate` MUST follow the `plate` `Rect` that `spec/scene.md` defines. [just go-check]
- render-svg-39: `font-size` MUST always appear on a text element, with the `size` value in px. [just go-check]
- render-svg-40: `x` MUST be `rect.x` with no `text-anchor` for `start`, `rect.x + floor_div(rect.w, 2)` with `text-anchor='middle'` for `middle`, and `rect.x + rect.w` with `text-anchor='end'` for `end`. [just go-check]
- render-svg-41: The baseline of line `k` MUST be `y = rect.y + k * LH + floor_div(LH, 2) + floor_div(S * 35, 100)`, where `LH` is the role line height in units and `S = size * 64`. [just go-check]
- render-svg-42: A bold run MUST be a nested `<tspan font-weight='600'>`, and an italic run MUST be a nested `<tspan font-style='italic'>`. [just go-check]
- render-svg-43: Text content and attribute values MUST be XML-escaped, so that `&`, `<`, `>`, and the quotation mark character are written as entities. [just go-check]
- render-svg-44: `font-family` MUST be `Inter, 'Helvetica Neue', Arial, sans-serif`, unless the `fontFamily` config key sets another value, which MUST be XML-escaped. [just go-check]

## Numbers

- render-svg-45: A length in units MUST be written by this rule, and no other number form is allowed. [just go-check]

  ```
  h = round_half_up(|units| * 100, 64)
  write floor_div(h, 100) as an integer
  when h mod 100 is not 0, write '.' and the two digits of h mod 100, then drop trailing zeros
  prefix '-' when units < 0 and h > 0
  ```

- render-svg-46: The rule MUST give these values. [just go-check]

  |Units|Text|
  |---|---|
  |128|`2`|
  |32|`0.5`|
  |1|`0.02`|
  |-96|`-1.5`|

- render-svg-47: Every number in the document, including `viewBox`, `width`, `height`, and the background rect, MUST be written in px by the number rule. [just go-check]

## Corners

- render-svg-48: At an interior corner `P` of a route, with unit axis directions `u1` (incoming) and `u2` (outgoing) and segment lengths `l1` and `l2`, the radius MUST be `r = min(512, floor_div(min(l1, l2), 2))` units, which is an 8 px cap. [just go-check]
- render-svg-49: When `r` is 0 the corner MUST be sharp; otherwise the path MUST go to `P - r * u1` and then by `A r r 0 0 s` to `P + r * u2`, where `s` is 1 when `u1.x * u2.y - u1.y * u2.x > 0` and 0 otherwise, so that 1 is a clockwise turn on screen. [just go-check]
- render-svg-50: A straight join, where `u1` equals `u2`, MUST have no corner. [just go-check]

## Arrowheads

- render-svg-51: The axis of an arrowhead MUST be the axis of the larger absolute component of the segment vector, with a tie going to x, and a zero-length segment MUST be skipped. [just go-check]
- render-svg-52: The arrowhead MUST sit at the endpoint with the unit direction `u` toward the endpoint, with length 512 units (8 px) and half-width 256 units (4 px): for tip `T`, base centre `B = T - 512 * u`, and normal `n = (-u.y, u.x)`, the filled polygon MUST be `T`, `B + 256 * n`, `B - 256 * n`. [just go-check]
- render-svg-53: This triangle MUST be the marker `point` of `spec/data/markers.json`, held in the scene as a `MarkerRef`. [just go-check]

## Accessibility

- render-svg-54: The root MUST have `role="graphics-document document"` and `aria-roledescription="diagram"`, which is one role description for every kind and a deliberate divergence from upstream, where the role description names the diagram type. [just go-check]
- render-svg-55: `<title>` MUST always be present, its text MUST be the `accTitle` and else `Mermaid <kind> diagram`, and the root MUST point to it with `aria-labelledby`. [just theme-check: TestCorpusSVGTitles]
- render-svg-56: The title rule MUST differ from upstream on purpose: upstream adds `<title>` only when `accTitle` is set. [just theme-check: TestCorpusSVGTitles]
- render-svg-57: `<desc>` and `aria-describedby` MUST exist only for a non-empty `accDescr`, and both MUST be XML-escaped. [just go-check]

## Text as paths

- render-svg-58: `--svg-text paths`, the `TextPaths` option, MUST draw glyph outlines as `<path>` elements instead of `<text>` elements, so that the viewer needs no font. [just go-check]
- render-svg-59: `GlyphOutlines` MUST hold `upem` and, for each weight (400 and 600), a map from codepoint to a command list in font units with the commands `move x y`, `line x y`, `quad cx cy x y`, and `close`, over exactly the codepoints of the `advances` table; a composite glyph MUST expand into its components with integer offsets, and a component with scale or rotation MUST leave that codepoint without an outline. [just go-check]
- render-svg-60: The outlines MUST be built from the embedded TTF files, in Go by `raster.InterOutlines()` with `golang.org/x/image/font/sfnt` and in Rust by `raster::inter_outlines()` under feature `png` with `skrifa` 0.50.0 and no hinting; the root package MUST NOT import `raster`, and the CLI MUST always pass outlines. [just go-check]
- render-svg-61: In paths mode, glyph `i` of a string MUST have its origin at `x0 + round_half_up(prefix_i * size_px * 64, upem)`, where `prefix_i` is the sum of the advances of glyphs `0` to `i - 1` in font units, and its baseline MUST be `y0`. [just go-check]
- render-svg-62: A glyph point `(gx, gy)` MUST map to `(origin_x + round_half_up(gx * size_px * 64, upem), y0 - round_half_up(gy * size_px * 64, upem))`, and a quadratic control point MUST map the same way. [just go-check]
- render-svg-63: A codepoint without an outline MUST draw nothing and MUST keep its measured advance. [just go-check]
- render-svg-64: `paths` with no outlines MUST be `ErrBadConfig` in Go and `RenderError::InvalidConfig { errors: 1 }` in Rust. [just go-check]
- render-svg-65: `x0` of a line MUST be `x` for `start`, `x - floor_div(line_w, 2)` for `middle`, and `x - line_w` for `end`, where `line_w` is the measured line width, and `y0` MUST be the baseline of the text rule of this file. [just go-check]

## Worked example

- render-svg-66: For a scene with one `node` group at index 0 that holds one `RoundRect` with style `node`, `r` 512, and rect (640, 640, 6400, 2560) in units, and one `Text` with role `label`, size 14, `align` `middle`, style `text`, and text `Start`, whose text `rect` is the node rect, the rules of this file MUST give this document, where each colour placeholder names a token and stands for the 6-digit hex of that token, and `W` and `H` are the canvas size in px. [just go-check]

  ```
  <svg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 W H' width='W' height='H' font-family='Inter, &apos;Helvetica Neue&apos;, Arial, sans-serif' role='graphics-document document' aria-roledescription='diagram' aria-labelledby='PREFIXtitle'>
  <title id='PREFIXtitle'>Mermaid KIND diagram</title>
  <style>
  .emd-bg{fill:<bg>}
  .emd-s-node{fill:<surface>;stroke:<border>}
  .emd-s-text{fill:<fg>}
  .emd-t-title{font-weight:600}
  .emd-t-label{font-weight:600}
  .emd-t-body{font-weight:400}
  </style>
  <rect class='emd-bg' x='0' y='0' width='W' height='H'/>
  <g class='emd-node' id='PREFIXg0'>
  <rect class='emd-s-node' x='10' y='10' width='100' height='40' rx='8' ry='8' stroke-width='1'/>
  <text class='emd-t-label emd-s-text' x='60' y='24.89' font-size='14' text-anchor='middle'>Start</text>
  </g>
  </svg>
  ```

- render-svg-67: The arithmetic of the example MUST be: 640 units is 10, 6400 is 100, 2560 is 40, and 512 is 8; the label line height is 20 px, which is 1280 units; the text `x` is `640 + floor_div(6400, 2) = 3840` units, which is 60; and the baseline is `640 + 0 * 1280 + floor_div(1280, 2) + floor_div(14 * 64 * 35, 100) = 640 + 640 + 313 = 1593` units, which is 24.89. [just go-check]
