# PNG back end

This file fixes the raster back end that turns a vector scene into PNG bytes.

## Inputs and output

- render-raster-01: The back end MUST read the vector scene and the theme, and it MUST NOT receive a `SymbolRef`. [just go-check]
- render-raster-02: PNG MUST be the only raster format. [just go-check]
- render-raster-03: The Go implementation MUST be `raster.PNG(s *mermaid.Scene, o Options) ([]byte, error)` with `golang.org/x/image/vector` for fills, and the Rust implementation MUST be `raster::png(scene: &Scene, options: &PngOptions) -> Result<Vec<u8>, RasterError>` with `tiny-skia` 0.12.0 behind feature `png`. [just rust-check: png_kinds]
- render-raster-04: The Go and Rust PNG byte streams MAY differ for the same scene, and the raster test oracle of this file MUST bound the difference. [just go-check: TestPNGKinds]

## Pixel size and limits

- render-raster-05: A pixel side MUST be `px = ceil(units * scale / 64)`, where `units` is the scene canvas side in 1/64 px, which is `(units * scale + 63) div 64` on non-negative values. [just go-check: TestPNGKinds]
- render-raster-06: `Scale` MUST be 1 to 8, and the default MUST be `0` in Go as the zero value and `2` in Rust. [just go-check]
- render-raster-07: A Go `Scale` outside 0 and 1 to 8 MUST be `ErrBadConfig`, and a Rust `scale` outside 1 to 8 MUST be `RasterError::InvalidConfig { errors: 1 }`. [just rust-check]
- render-raster-08: `Background` MUST follow the SVG rule: `""` gives the theme `bg` token, and a hex colour `#rgb` or `#rrggbb` MUST be used as given. [just go-check]
- render-raster-09: A side above 16384 px, or an area above 67 108 864 px (2^26), MUST be `raster.ErrPixelsTooLarge` in Go and `RasterError::PixelsTooLarge { width, height }` in Rust. [just go-check]
- render-raster-10: The error set MUST be `raster.ErrPixelsTooLarge`, `raster.ErrEncode`, and `mermaid.ErrBadConfig` in Go, and `RasterError::PixelsTooLarge`, `Encode`, and `InvalidConfig` in Rust. [just go-check]

## Fill and paint order

- render-raster-11: The fill rule MUST be non-zero for `Polygon` and `Path`. [just go-check]
- render-raster-12: Paint order MUST follow item order, so each item fills and then strokes. [just go-check]
- render-raster-13: A tint style MUST use `paint.tint_alpha`, which is 102 of 255, or 40 percent. [just go-check]
- render-raster-14: A `Rect` in style `plate` MUST be filled with the `bg` colour before the label it precedes. [just go-check]

## Curves

- render-raster-15: A `C` command MUST be flattened by the Cubic rule of `spec/render-cells.md`, and an `A` command MUST be flattened by the Arc rule of `spec/render-cells.md`, both in units and before scaling. [just go-check]
- render-raster-16: An `Ellipse` MUST be the 64-point polygon of the Ellipse rule of `spec/render-cells.md`, computed in units and before scaling. [just go-check]

## Strokes

- render-raster-17: The Go package MUST stroke in-house, because `golang.org/x/image/vector` only fills paths. [just go-check]
- render-raster-18: The stroke width in pixels MUST be `width_units * scale / 64`, where `width_units` is 64 for `normal`, 128 for `emphasis`, or the integer width, and an open marker MUST use `normal`. [just go-check]
- render-raster-19: Each segment MUST become the quadrilateral of width `w` around it, and each vertex MUST get a filled 16-gon of diameter `w`, which gives round joins and caps. [just go-check]
- render-raster-20: A dash pattern MUST split each polyline by arc length before stroking, with dash lengths taken from `paint.dash_*` in units before scaling: 192 on and 192 off for `dotted`, and 512 on and 256 off for `dashed`. [just go-check]
- render-raster-21: Rust MUST use the `tiny-skia` stroker with round joins, round caps, and the same dash pattern. [just rust-check: png_kinds]

## Markers

- render-raster-22: A `MarkerRef` MUST be drawn from its polygon or polyline in `spec/data/markers.json`, rotated and translated as the SVG marker rule states, with fill and stroke from its `paint` style. [just go-check]

## Text

- render-raster-23: Glyph outlines MUST come from `GlyphOutlines`, which MUST fill with the colour that the text style resolves to for the active theme. A codepoint without an Inter outline MUST take the fallback rule of `spec/render-svg.md` (render-svg-63), and the outline commands MUST equal those of SVG drawn as paths for the same text. [just go-check]
- render-raster-24: The origin and baseline of a glyph MUST follow the text rule of `spec/render-svg.md`, and glyph placement MUST follow the `Placement` sub-rule under `SVG text` in `spec/render-svg.md`. [just go-check]
- render-raster-25: Bold and italic runs MUST follow the `Markdown strings` rule of `spec/text-measurement.md`. [just go-check]

## Checks

- render-raster-26: A PNG of each corpus kind's first fixture MUST decode, MUST have width `ceil(W * scale / 64)` and height `ceil(H * scale / 64)` for the scene canvas `W` by `H`, and MUST NOT be a single colour. [just go-check: TestPNGKinds]
- render-raster-27: The raster test oracle MUST render the first fixture in byte-wise path order of `flowchart`, `sequence`, `class`, `pie`, and `sankey` at scale 2, MUST fill the scene's `Rect`, `RoundRect`, `Polygon`, and filled `Path` primitives row by row with the even-odd rule at the same scale, and on each row with no `Text` primitive and no stroked primitive, in a scene rendered with strokes off, MUST require the x positions where the PNG's non-background run starts and stops to agree with the oracle's run edges within 1 px per edge. [just go-check: TestPNGKinds]
