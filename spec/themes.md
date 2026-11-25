# Themes and colour

This file fixes the token model, the built-in themes, the contrast gate, the upstream theme mapping, the integer colour arithmetic, and the `look` variants.

## Token model

- themes-01: A theme MUST hold the colour tokens `bg`, `fg`, `line`, `accent`, `muted`, `surface`, `border`, `series[0]` to `series[11]`, `error`, `warning`, and `success`, plus typography, spacing, stroke, and radius tokens. [just go-check]
- themes-02: Every scene style token MUST resolve through this model, so a back end MUST NOT hold a colour or size literal. [just theme-check]
- themes-03: All geometry and paint constants MUST be generated from `spec/data/`. [just gen-check]
- themes-04: `theme-check` MUST scan every tracked Go and Rust file except generated files (`*_gen.go` and any `gen/` directory), `tools/`, and test files (`*_test.go` files, any `tests/` directory, `tests.rs`, and `*_tests.rs`), for `#` followed by 3, 4, 6, or 8 hexadecimal digits and a word boundary, and MUST fail on a match. [just theme-check]
- themes-05: Typography MUST be the three roles of `spec/text-measurement.md`. [just go-check]
- themes-06: The spacing tokens MUST be 4, 8, 12, 16, 24, 32, and 48 px, which are 256, 512, 768, 1024, 1536, 2048, and 3072 units. [just go-check]
- themes-07: The stroke tokens MUST be `normal` at 64 units (1 px) and `emphasis` at 128 units (2 px). [just go-check]
- themes-08: The radius token MUST be 8 px, which is 512 units, by default. [just go-check]

## Visual direction

- themes-09: The visual direction MUST be medium-high-density technical illustration, and vector spacing MUST use only the spacing tokens. [just go-check]
- themes-10: The built-in themes MUST NOT use gradients, shadows, `system-ui`, pure red, pure green, pure blue, pure purple, pure black, or pure white. [just theme-check]

## Built-in themes and palettes

- themes-11: The nine built-in themes MUST be `elegant-light` and `elegant-dark` from Radix Colors 3.0.0 (MIT), `github-light` and `github-dark` from Primer primitives 11.10.0 (MIT), `catppuccin-latte` and `catppuccin-mocha` from `@catppuccin/palette` 1.8.0 (MIT), `nord` (MIT), and `solarized-light` and `solarized-dark` (MIT). [just gen-check]
- themes-12: Every colour MUST come from a published palette, held in one file per palette at `spec/data/palettes/<palette>.json` (`radix`, `primer`, `catppuccin`, `nord`, `solarized`, `colorbrewer-paired`), with its source URL and SHA-256 in `spec/data/SOURCES.json`. [just gen-check]
- themes-13: The series colours MUST be ColorBrewer `Paired` 12 (Apache-2.0), in this order: `#a6cee3 #1f78b4 #b2df8a #33a02c #fb9a99 #e31a1c #fdbf6f #ff7f00 #cab2d6 #6a3d9a #ffff99 #b15928`. [just gen-check]
- themes-14: The default theme MUST be `elegant-light`. [just go-check]
- themes-15: For text output the default theme MUST be `elegant-dark` when `COLORFGBG` parses and its background field is 0 to 6 or 8; which default wins over a given `-t` is fixed in `spec/cli.md`. [just go-check]

## The two elegant themes

- themes-16: `elegant-light` and `elegant-dark` MUST map the tokens to these Radix steps. [just gen-check]

  |Token|`elegant-light`|`elegant-dark`|
  |---|---|---|
  |`bg`|`slate1`|`slateDark1`|
  |`surface`|`slate2`|`slateDark2`|
  |`fg`|`slate12`|`slateDark12`|
  |`muted`|`slate11`|`slateDark11`|
  |`border`|`slate9`|`slateDark9`|
  |`line`|`slate10`|`slateDark10`|
  |`accent`|`blue9`|`blueDark9`|
  |`error`|`ruby11`|`rubyDark11`|
  |`warning`|`amber11`|`amberDark11`|
  |`success`|`grass11`|`grassDark11`|
  |`series[0..11]`|ColorBrewer `Paired` 1 to 12|the same colours|

- themes-17: In `elegant-light` and `elegant-dark`, the status tokens `error`, `warning`, and `success` MUST use Radix step 11, and step 9 MUST NOT be used for a status token. [just theme-check]
- themes-18: The scene MUST draw a status colour as a stroke and never as text, so the gate for a status token MUST be 3:1. [just theme-check]
- themes-19: The status ratios below MUST hold, computed by the integer rule of this file as `(Yhi + 3277) / (Ylo + 3277)`, rounded down to one decimal, on `slate1` and `slate2` for `elegant-light` and on `slateDark1` and `slateDark2` for `elegant-dark`. [just theme-check: TestBuiltInThemeContrast]

  |Token|Light step (hex)|Dark step (hex)|`elegant-light` on `slate1`|on `slate2`|`elegant-dark` on `slateDark1`|on `slateDark2`|
  |---|---|---|---|---|---|---|
  |`error`|`ruby11` (`#ca244d`)|`rubyDark11` (`#ff949d`)|5.2|5.1|8.9|8.3|
  |`warning`|`amber11` (`#ab6400`)|`amberDark11` (`#ffca16`)|4.4|4.3|12.3|11.4|
  |`success`|`grass11` (`#2a7e3b`)|`grassDark11` (`#71d083`)|4.9|4.8|9.9|9.2|

## The other built-in themes

- themes-20: The seven other built-in themes MUST map the tokens to these palette names, in the palette file named in the table header. [just gen-check]

  |Token|`github-light` and `github-dark` (Primer)|`catppuccin-latte` and `catppuccin-mocha`|`nord`|`solarized-light`|`solarized-dark`|
  |---|---|---|---|---|---|
  |`bg`|`--bgColor-default`|`base`|`nord0`|`base3`|`base03`|
  |`surface`|`--bgColor-muted`|`mantle`|`nord1`|`base3`|`base02`|
  |`fg`|`--fgColor-default`|`text`|`nord6`|`base02`|`base2`|
  |`muted`|`--fgColor-muted`|`subtext1`|`nord4`|`base01`|`base1`|
  |`border`|`--borderColor-emphasis`|`overlay2`|`nord4`|`base00`|`base0`|
  |`line`|`--fgColor-muted`|`subtext0`|`nord5`|`base01`|`base0`|
  |`accent`|`--fgColor-accent`|`blue`|`nord8`|`blue`|`blue`|
  |`error`|`--fgColor-danger`|`red`|`nord11`|`red`|`red`|
  |`warning`|`--fgColor-attention`|`yellow`|`nord12`|`orange`|`orange`|
  |`success`|`--fgColor-success`|`green`|`nord14`|`green`|`green`|

- themes-21: The Primer names MUST be CSS variables of `@primer/primitives` 11.10.0 in `dist/css/functional/themes/light.css` and `dark.css`, and each MUST exist in both files. [just gen-check]
- themes-22: The Catppuccin names MUST exist in `@catppuccin/palette` 1.8.0 `css/catppuccin.css`, as `--ctp-latte-<name>` and `--ctp-mocha-<name>`, and the Solarized and Nord names MUST be the published palette names. [just gen-check]
- themes-23: `solarized-light` MUST use `base3` as `surface`, because no Solarized tone gives `muted` 4.5:1 on `base2`. [just theme-check]

## Contrast of the mapped tokens

- themes-24: The contrast pairs below MUST hold, measured as `on bg, on surface` and rounded down to two decimals: `fg` and `muted` need 4.5, and `line`, `border`, and `accent` need 3.0. [just theme-check: TestBuiltInThemeContrast]

  |Theme|`fg`|`muted`|`line`|`border`|`accent`|
  |---|---|---|---|---|---|
  |`elegant-light`|15.98, 15.58|5.79, 5.64|3.69, 3.59|3.21, 3.13|3.18, 3.10|
  |`elegant-dark`|16.24, 15.15|9.05, 8.44|4.44, 4.14|3.68, 3.43|5.77, 5.38|
  |`github-light`|15.79, 14.83|6.11, 5.74|6.11, 5.74|3.45, 3.24|5.19, 4.87|
  |`github-dark`|17.38, 15.90|6.49, 5.94|6.49, 5.94|3.56, 3.26|6.10, 5.58|
  |`catppuccin-latte`|7.06, 6.56|5.52, 5.14|4.36, 4.06|3.49, 3.24|4.34, 4.03|
  |`catppuccin-mocha`|11.34, 12.13|9.26, 9.91|7.36, 7.88|5.81, 6.21|7.78, 8.33|
  |`nord`|10.83, 8.72|9.24, 7.44|10.25, 8.26|9.24, 7.44|6.24, 5.02|
  |`solarized-light`|12.05, 12.05|4.98, 4.98|4.98, 4.98|4.12, 4.12|3.41, 3.41|
  |`solarized-dark`|12.25, 10.60|5.61, 4.86|4.74, 4.11|4.74, 4.11|4.07, 3.53|

- themes-25: `theme-check` MUST repeat the contrast check with the integer rule, and a failure there MUST be treated as a defect in the palette data or the generator, never as a reason to change a step. [just theme-check]

## Status and series strokes

- themes-26: `tools/specgen` MUST write the generated table `strokeok` with one row per theme name, in all 20 names, and per token `error`, `warning`, `success`, and `series0` to `series11`, keyed and sorted by `(theme, token)` bytewise. [just gen-check]
- themes-27: `ok` MUST be 1 when the colour reaches 3:1 against both `bg` and `surface` of the theme by the integer rule, and 0 otherwise. [just gen-check]
- themes-28: Where a style strokes with a token whose `ok` is 0, which are `error`, `warning`, `success`, `series-line`, and `series-flow`, every back end MUST stroke with `line` instead, and the cell back end MUST colour those cells as `line`. [just theme-check]
- themes-29: A series fill MUST keep its colour, because its outline is `line` already. [just go-check]
- themes-30: The `ok` value MUST be 0 for these tokens of these themes, and this list is the result of the check on 2026-11-12 with the pinned palettes. [just theme-check]

  - `warning` and `success` in `catppuccin-latte`.
  - `error` in `nord`.
  - `success` in `solarized-light`.
  - `error` and `warning` in `solarized-dark`.
  - Series 0, 2, 4, 6, 7, 8, 10 in `elegant-light`, `github-light`, and `solarized-light`.
  - Series 0, 2, 3, 4, 6, 7, 8, 10 in `catppuccin-latte`.
  - Series 9 in `elegant-dark`, `github-dark`, and `catppuccin-mocha`.
  - Series 1, 3, 5, 9, 11 in `nord`.
  - Series 1, 5, 9, 11 in `solarized-dark`.

- themes-31: Meaning MUST never rest on a series or status colour alone: each such element MUST also carry its label, and series lines MUST differ by dash pattern. [just go-check]

## Upstream themes

- themes-32: The eleven upstream theme names MUST stay valid: `base`, `dark`, `default`, `forest`, `neutral`, `neo`, `neo-dark`, `redux`, `redux-dark`, `redux-color`, and `redux-dark-color`. [just go-check]
- themes-33: `tools/upstream-oracle/themes.mjs` MUST evaluate the eleven upstream theme classes and write their computed variables into `spec/data/themes.json`. [just gen-check]
- themes-34: A `theme` config value outside the 20 names, which are the nine built-in plus the eleven upstream names, MUST raise `config/malformed` (error); the exit code of `-t` with an unknown name is fixed in `spec/cli.md`. [just go-check]
- themes-35: An upstream theme MUST be drawn with these variables mapped unchanged to tokens. [just go-check]

  |Upstream variable|Token|
  |---|---|
  |`background`|`bg`|
  |`mainBkg`|`surface`|
  |`primaryTextColor`|`fg`|
  |`secondaryTextColor`|`muted`|
  |`primaryBorderColor`|`border`|
  |`lineColor`|`line`|
  |`secondaryBorderColor`|`accent`|
  |`errorBkgColor`|`error`|
  |`noteBkgColor`|`warning`|
  |`tertiaryColor`|`success`|
  |`pie1` to `pie12`|`series[0]` to `series[11]`|
  |`cScale12`, for the upstream theme `dark` only, which defines no `pie12`|`series[11]`|

- themes-36: The contrast gate MUST cover the nine built-in themes only and MUST NOT run on the eleven upstream themes. [just theme-check]

## Integer colour arithmetic for the `base` derivation

- themes-37: `base` with user `themeVariables` MUST port the derivation of the `base` theme with the colour operations `adjust`, `darken`, `lighten`, `invert`, and `isDark`, and `rgba` MUST NOT be used. [just go-check]
- themes-38: RGB to HSL MUST be computed on channels 0 to 255 as follows, with `M` the maximum channel, `m` the minimum, `d = M - m`, and `sum = M + m`. [just go-check]

  ```
  l = floor_div(100 * sum + 255, 510)
  d = 0  -> h = 0, s = 0
  else   -> D = 255 - |sum - 255|
            s = floor_div(200 * d + D, 2 * D)
            n = 60 * (G - B)                  when M is R
            n = 60 * (B - R) + 120 * d        when M is G
            n = 60 * (R - G) + 240 * d        when M is B
            h = floor_mod(floor_div(2 * n + d, 2 * d), 360)
  ```

- themes-39: The RGB to HSL output MUST be `h` in 0 to 359 and `s` and `l` in 0 to 100. [just go-check]
- themes-40: HSL to RGB MUST be computed as follows. [just go-check]

  ```
  C  = floor_div((100 - |2l - 100|) * s * 255 + 5000, 10000)
  hp = floor_mod(h, 120)
  X  = floor_div(C * (60 - |hp - 60|) + 30, 60)
  m  = floor_div(255 * l + 50, 100) - floor_div(C, 2)
  sector = floor_div(h, 60):  0 -> (C, X, 0)   1 -> (X, C, 0)   2 -> (0, C, X)
                              3 -> (0, X, C)   4 -> (X, 0, C)   5 -> (C, 0, X)
  each channel = component + m, clamped to 0 to 255
  ```

- themes-41: `adjust(c, {h, s, l})` MUST convert to HSL, add the deltas, set `h` to `floor_mod(h, 360)`, clamp `s` and `l` to 0 to 100, and convert back. [just go-check]
- themes-42: `darken(c, a)` MUST be `adjust(c, {l: -a})`, and `lighten(c, a)` MUST be `adjust(c, {l: +a})`. [just go-check]
- themes-43: `invert(c)` MUST be `255 - channel` for each channel, at the default weight of the upstream call, which passes no weight. [just go-check]
- themes-44: `isDark(c)` MUST be `!isLight(c)`, where `isLight(c)` is `luminance(c) >= 0.5` and `luminance(c)` takes 0.2126, 0.7152, and 0.0722 of the linear channels, so `isDark(c)` means a relative luminance below 0.5 and not an HSL lightness below 50. [just go-check]
- themes-45: The integer form of `isDark` MUST be `S < 327675000`, where `S = 2126 * R + 7152 * G + 722 * B` on the `lin16` values. [just go-check]
- themes-46: `mkBorder(c, dark)` MUST be `adjust(c, {s: -40, l: +10})` in dark mode and `adjust(c, {s: -40, l: -10})` otherwise. [just go-check]
- themes-47: The upstream `adjust` reduces the hue with a truncating remainder, and its hue conversion adds one turn to a negative phase once, so the two rules give the same colour for every hue above -240; the upstream themes use no hue delta below -160, so the result is above -240 for every derivation. [just go-check]
- themes-48: The oracle MUST check 200 random inputs to within 1 per channel, and Go and Rust MUST agree byte for byte with the integer rules of this section, not with the oracle. [just parity]

## Contrast gate

- themes-49: The `lin16` table MUST be generated by `tools/specgen` as `round_half_up(65535 * f(c8 / 255), 1)`, where `f(u) = u / 12.92` for `u <= 0.04045` and `f(u) = ((u + 0.055) / 1.055)^2.4` otherwise, computed in 40-digit decimal arithmetic. [just gen-check]
- themes-50: Relative luminance MUST be `Y = floor_div(2126 * R + 7152 * G + 722 * B, 10000)` on the linear values, with `R`, `G`, and `B` the `lin16` values of the three channels. [just theme-check: TestBuiltInThemeContrast]
- themes-51: A pair with luminances `Yhi >= Ylo` MUST reach ratio `T` exactly when `10 * (Yhi + 3277) >= T10 * (Ylo + 3277)`, where `T10` is 45 for 4.5:1 and 30 for 3:1, and 3277 is the fixed integer form of 0.05 on the 65535 scale. [just theme-check: TestBuiltInThemeContrast]
- themes-52: `fg` and `muted` MUST reach 4.5:1 on `bg` and on `surface`. [just theme-check: TestBuiltInThemeContrast]
- themes-53: `line`, `border`, and `accent` MUST reach 3:1 on `bg` and on `surface`. [just theme-check: TestBuiltInThemeContrast]
- themes-54: A status token or a series colour that strokes a shape MUST reach 3:1 on `bg` and on `surface`, or the `strokeok` table MUST replace it by `line`. [just theme-check: TestBuiltInThemeContrast]
- themes-55: Each series shape (bar, slice, area, node fill) MUST have a 1 px (`normal`, 64 units) stroke in `line`, and the 3:1 gate MUST test that stroke against the surface it touches, not the fill. [just theme-check: TestBuiltInThemeContrast]
- themes-56: A series fill MUST have no contrast requirement against its surface. [just theme-check]
- themes-57: A label on a series fill MUST take `fg` or `bg`, whichever has the higher contrast with that fill, and that pair MUST reach 4.5:1; if neither reaches 4.5:1, the label MUST keep its place and MUST get a `plate`, which is a `Rect` of its text box in style `plate` with fill `bg`, and the text MUST take `fg`. [just theme-check: TestBuiltInThemeContrast]
- themes-58: A label on any other fill MUST reach 4.5:1 against that fill. [just theme-check: TestBuiltInThemeContrast]
- themes-59: `tools/specgen` MUST compute the `text-on-series` choice from `spec/data/themes.json` with the integer contrast rule, and MUST write the `seriestext` table with one row per theme name (all 20) and per series index, keyed and sorted by `(theme, series)`. [just gen-check]

## Look variants

- themes-60: `look: handDrawn` in the vector profile MUST redraw each stroked straight segment as two bowed passes, and the cell profile MUST ignore it. [just go-check: TestLookHandDrawnSeed]
- themes-61: The generator MUST be xorshift32 (`x ^= x << 13; x ^= x >> 17; x ^= x << 5`, all in uint32 wrap-around). [just go-check: TestLookHandDrawnSeed]
- themes-62: For the stroked primitive at index `i`, 0-based over every scene primitive in draw order with the groups flattened, the seed MUST be `s = uint32(handDrawnSeed) XOR (uint32(i + 1) * 2654435761)`, and `s` MUST be 1 when that is 0. [just go-check: TestLookHandDrawnSeed]
- themes-63: The config key `handDrawnSeed` MUST be an integer from 0 to 4294967295, its default MUST be 0 when the key is absent, and any other value MUST raise `config/malformed` (error). [just go-check]
- themes-64: Two renders with seed 0 MUST be identical, because `uint32(i + 1) * 2654435761` is 0 only when `i + 1` is a multiple of 2^32, so the `s = 1` rule never applies at seed 0. [just go-check: TestLookHandDrawnSeed]
- themes-65: For any other seed `S`, exactly one value of `i + 1` in 1 to 4294967295 MUST make the XOR 0, because multiplication by the odd constant 2654435761 is a bijection modulo 2^32, so the `s = 1` rule applies to that primitive only. [just go-check]
- themes-66: Each stroked straight segment MUST consume 10 draws in this order: pass 1 bow, start x, start y, end x, end y; then pass 2 the same five. [just go-check: TestLookHandDrawnSeed]
- themes-67: A draw `r` MUST give the offset `(r mod 129) - 64` in units, a pass MUST use the endpoints `p1` plus the start offsets and `p2` plus the end offsets, and the `bow` of a pass MUST be that offset of the pass's first draw, not the raw generator word. [just go-check: TestLookHandDrawnSeed]
- themes-68: The control point of a pass MUST be `m + (round_half_up(bow * (-dy), L), round_half_up(bow * dx, L))`, where `m` is the midpoint of the pass endpoints with `floor_div` per coordinate, `(dx, dy)` is the pass vector, and `L = max(|dx|, |dy|)`, and a pass with `L = 0` MUST have its control point at `m`. [just go-check: TestLookHandDrawnSeed]
- themes-69: Each pass MUST be drawn as `M p1 Q c p2` with the primitive's stroke width, and a curved primitive MUST NOT be redrawn. [just go-check: TestLookHandDrawnSeed]
- themes-70: `look: neo` MUST be a token variant that keeps the colours, sets the stroke to `emphasis` (2 px), and sets the radius to 12 px (768 units). [just go-check]
- themes-71: `look` MUST change no style row, and in a cell scene it MUST have no effect: `width` keeps the value the element styles give without `look`, and `r` is 0. [just go-check]
