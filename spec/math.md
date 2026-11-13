# Math and Markdown strings

This file fixes the styled Markdown runs inside labels and the TeX subset that a label can contain.

## Markdown runs

- math-01: Bold, italic, and line breaks in a label MUST become styled runs, and everything outside the accepted subset MUST stay literal text. [just parity]
- math-02: Italic MUST be a synthetic oblique with shear 13/64 and upright advances: a point at height `h` above the baseline, in units, moves right by `floor_div(13 * h, 64)`. [just parity]
- math-03: `**text**` MUST be a bold run with the weight 600 advances. [just parity]
- math-04: `*text*` and `_text_` MUST be italic runs with the weight 400 advances. [just parity]
- math-05: `<br>`, `<br/>`, and `<br />`, compared case-insensitively, MUST force a line break. [just parity]
- math-06: A backslash before an ASCII punctuation character MUST stand for that character, as in `\*`, `\_`, `\\`, and `\$`. [just parity]
- math-07: Emphasis MUST NOT nest; an opener MUST close at the next identical delimiter on the same line; an unclosed opener MUST stay literal; and a `_` between two letters or digits MUST stay literal. [just parity]
- math-08: Code spans, links, images, headings, list markers, other HTML tags, and entities MUST stay literal text, and entities MUST NOT be decoded. [just parity]

## Math spans

- math-09: A math span MUST be `$$`, then the formula, then `$$`, on one label; quotes in the source MUST NOT hide a span, so spans are recognised in quoted and unquoted labels alike. [just parity]
- math-10: An unmatched `$$` and a single `$` MUST be literal text. [just parity]
- math-11: `\$` MUST be a literal dollar outside math and inside math. [just parity]
- math-12: The math subset MUST be exactly these constructs: groups, `\frac`, `^`, `_`, `\sqrt[n]{}`, the Greek names of the font mapping, `\sum \prod \int \lim \infty \pm \times \div \cdot \le \ge \ne \approx \to \leftarrow \Rightarrow \Leftrightarrow`, `\left` and `\right` delimiters, `\text`, `\mathbf`, `\mathit`, `\mathrm`, and the spaces `\, \; \quad`; any other command MUST raise `math/unsupported-command` (warning, summary `unsupported math command COMMAND`, help `The source text is shown as written.`), and the source text MUST be shown as written. [just parity]
- math-13: Box layout MUST use integer units, scripts MUST be at 70 percent size, and radicals and tall delimiters MUST be paths. [just parity]

## Font mapping

- math-14: `\mathbf` MUST use the weight 600 table, `\mathit` MUST use the weight 400 table with the italic shear, and `\mathrm` and `\text` MUST use the weight 400 table upright. [just parity]
- math-15: Without a font command, Latin letters MUST use the `\mathit` style, digits and symbols MUST use the `\mathrm` style, and Greek letters MUST be upright. [just parity]
- math-16: The Greek names MUST form this closed list, each name MUST map to one code point, and `\omicron`, `\varpi`, `\varrho`, and `\varsigma` MUST NOT be in the list. [just parity]

    Lower case, 26 names:

    |Name|Code point|
    |---|---|
    |`\alpha`|U+03B1|
    |`\beta`|U+03B2|
    |`\gamma`|U+03B3|
    |`\delta`|U+03B4|
    |`\epsilon`|U+03F5|
    |`\varepsilon`|U+03B5|
    |`\zeta`|U+03B6|
    |`\eta`|U+03B7|
    |`\theta`|U+03B8|
    |`\vartheta`|U+03D1|
    |`\iota`|U+03B9|
    |`\kappa`|U+03BA|
    |`\lambda`|U+03BB|
    |`\mu`|U+03BC|
    |`\nu`|U+03BD|
    |`\xi`|U+03BE|
    |`\pi`|U+03C0|
    |`\rho`|U+03C1|
    |`\sigma`|U+03C3|
    |`\tau`|U+03C4|
    |`\upsilon`|U+03C5|
    |`\phi`|U+03D5|
    |`\varphi`|U+03C6|
    |`\chi`|U+03C7|
    |`\psi`|U+03C8|
    |`\omega`|U+03C9|

    Upper case, 11 names:

    |Name|Code point|
    |---|---|
    |`\Gamma`|U+0393|
    |`\Delta`|U+0394|
    |`\Theta`|U+0398|
    |`\Lambda`|U+039B|
    |`\Xi`|U+039E|
    |`\Pi`|U+03A0|
    |`\Sigma`|U+03A3|
    |`\Upsilon`|U+03A5|
    |`\Phi`|U+03A6|
    |`\Psi`|U+03A8|
    |`\Omega`|U+03A9|

- math-17: `tools/specgen` MUST check each Greek code point against the `cmap` of `Inter-Regular.ttf`; when Inter lacks U+03F5, U+03D1, or U+03D5, the name MUST map to U+03B5, U+03B8, or U+03C6 instead, and the generated table MUST record the code point in use. [just gen-check]
- math-18: `tools/specgen` MUST fail when Inter lacks a glyph that the math subset needs. [just gen-check]

## Script characters

- math-19: The cell profile MUST convert scripts with the `scripts` table; `spec/data/scripts.json` MUST hold one object per row with keys `base`, `sup`, and `sub`, each value a JSON string `U+` followed by four uppercase hex digits, where `U+0000` means that the form does not exist; the rows MUST be the characters `(`, `)`, `+`, `-`, the digits, `=`, the ASCII letters that have a form in the block Superscripts and Subscripts (U+2070 to U+209F), and the letter U+0259, whose subscript is U+2094; no other code point MUST have a row; and the generated table MUST sort the rows by `base`. [just gen-check]

    |Char|`base`|`sup`|`sub`|
    |---|---|---|---|
    |(|`U+0028`|`U+207D`|`U+208D`|
    |)|`U+0029`|`U+207E`|`U+208E`|
    |+|`U+002B`|`U+207A`|`U+208A`|
    |-|`U+002D`|`U+207B`|`U+208B`|
    |0|`U+0030`|`U+2070`|`U+2080`|
    |1|`U+0031`|`U+00B9`|`U+2081`|
    |2|`U+0032`|`U+00B2`|`U+2082`|
    |3|`U+0033`|`U+00B3`|`U+2083`|
    |4|`U+0034`|`U+2074`|`U+2084`|
    |5|`U+0035`|`U+2075`|`U+2085`|
    |6|`U+0036`|`U+2076`|`U+2086`|
    |7|`U+0037`|`U+2077`|`U+2087`|
    |8|`U+0038`|`U+2078`|`U+2088`|
    |9|`U+0039`|`U+2079`|`U+2089`|
    |=|`U+003D`|`U+207C`|`U+208C`|
    |a|`U+0061`|`U+0000`|`U+2090`|
    |e|`U+0065`|`U+0000`|`U+2091`|
    |h|`U+0068`|`U+0000`|`U+2095`|
    |i|`U+0069`|`U+2071`|`U+0000`|
    |k|`U+006B`|`U+0000`|`U+2096`|
    |l|`U+006C`|`U+0000`|`U+2097`|
    |m|`U+006D`|`U+0000`|`U+2098`|
    |n|`U+006E`|`U+207F`|`U+2099`|
    |o|`U+006F`|`U+0000`|`U+2092`|
    |p|`U+0070`|`U+0000`|`U+209A`|
    |s|`U+0073`|`U+0000`|`U+209B`|
    |t|`U+0074`|`U+0000`|`U+209C`|
    |w|`U+0077`|`U+0000`|`U+209D`|
    |x|`U+0078`|`U+0000`|`U+2093`|
    |y|`U+0079`|`U+0000`|`U+209E`|
    |z|`U+007A`|`U+0000`|`U+209F`|
    |ə|`U+0259`|`U+0000`|`U+2094`|

## Box model and constants

- math-20: Each box MUST have integer `w` (width), `a` (ascent above the baseline), and `d` (descent below it), and a list of leaves: glyphs (codepoint, weight, size, shear flag), rules (rectangles), and paths (flattened point lists); a label's formula box MUST be the box of the whole formula. [just parity]
- math-21: Every constant of this table except `script_scale` and `bigop_scale` MUST be a length in units, `round_half_up(v * em, 1000)`, where `em = size_px * 64` for the formula's base size, 14 px for body and label and 16 px for title, and `v` is the constant's per-1000-em value. `script_scale` and `bigop_scale` MUST be dimensionless per-1000 factors. A script MUST have size `round_half_up(script_scale * parent_size, 1000)` units, where `script_scale` is stored as 700 and `parent_size` is the parent element's size in units. A big-operator glyph MUST have size `round_half_up(bigop_scale * em, 1000)` units, where `em` is the formula's base em. Every constant MUST live in this file and in the generated Go and Rust constants. [just gen-check]

    |Constant|Value (per 1000 em unless stated)|Use|
    |---|---|---|
    |`rule`|50, at least 1 unit|fraction bar, radical overbar, delimiter stroke|
    |`axis`|250|fraction bar centre above the baseline|
    |`frac_gap`|60|gap between a fraction bar and its numerator or denominator|
    |`sup_shift`|360|superscript baseline above the base baseline|
    |`sub_shift`|150|subscript baseline below the base baseline|
    |`script_gap`|30|space before a script; also each side of a fraction bar beyond the wider of numerator and denominator|
    |`script_scale`|700, dimensionless per-1000|script size = `round_half_up(script_scale * parent_size, 1000)`|
    |`rad_gap`|60|gap between the radicand box and the overbar|
    |`rad_sign_w`|600|width of the radical sign box|
    |`delim_w`|250|width of a delimiter box|
    |`bigop_scale`|1400, dimensionless per-1000|size of the `\sum`, `\prod`, and `\int` glyphs relative to the body size|
    |`bigop_gap`|100|gap between a big operator and its limits|
    |`binop_space`|222|space on each side of `\pm \times \div \cdot`|
    |`relop_space`|278|space on each side of `=` and of the relation commands|
    |`\,`|167|thin space|
    |`\;`|278|medium space|
    |`\quad`|1000|one em|

## Layout rules

- math-22: `{a b}` MUST be horizontal concatenation with no space added. [just parity]
- math-23: `\frac{n}{d}` MUST centre the bar at `axis` with thickness `rule`; the bar width MUST be the wider of `n` and `d` plus `2 * script_gap`; `n` MUST be centred above the bar with its bottom at the bar's top minus `frac_gap`; and `d` MUST be centred below the bar with its top at the bar's bottom plus `frac_gap`. [just parity]
- math-24: `x^{s}` and `x_{s}` MUST set the script at `script_scale`, placed after `x` with `script_gap` before it; a superscript baseline MUST be `sup_shift` above the base baseline and a subscript baseline MUST be `sub_shift` below it; and when both are present they MUST share one x position, where the wider one sets the width. [just parity]
- math-25: `\sum` and `\prod` MUST take limits above and below, centred, at `bigop_gap` from the glyph; `\int` MUST take its scripts to the right, as in an ordinary script; and `\lim` MUST be upright body text with limits below. [just parity]
- math-26: `\sqrt[n]{x}` MUST draw the sign as the polyline `(0, 600)`, `(250, 480)`, `(450, 1000)`, then the overbar to `(1000, 1000)`, in per-1000 units of (sign width, box height), stroked with `rule`; the overbar MUST lie `rad_gap` above the radicand box; and the index MUST be set at `script_scale`, with its baseline `sup_shift` above the sign baseline, placed before the sign. [just parity]
- math-27: A `\left` and `\right` delimiter box MUST have height `max(enclosed height, em)` and width `delim_w`; in a box of width `w` and height `H`, stroked with `rule`, the shapes MUST be: [just parity]

    - `(` is a quadratic from `(w, 0)` through `(0, H/2)` to `(w, H)`; `)` mirrors it.
    - `[` is the polyline `(w,0),(0,0),(0,H),(w,H)`; `]` mirrors it.
    - `\{` is the polyline `(w,0),(w/2,0),(w/2,H/2),(0,H/2),(w/2,H/2),(w/2,H),(w,H)`; `\}` mirrors it.
    - `|` is the line `(w/2,0)` to `(w/2,H)`.
    - `.` draws nothing and has width 0.

- math-28: Spacing MUST be `binop_space` on each side of `\pm \times \div \cdot`, `relop_space` on each side of `=` and of the relation commands, and the three space commands MUST use their table values. [just parity]

## Errors

- math-29: `math/syntax` (error, summary `invalid math syntax: REASON`, help `The source text is shown as written.`) MUST cover unbalanced braces, a missing argument to `\frac`, `\sqrt`, `^`, or `_`, and a `\left` without its `\right` or the reverse. [just parity]
- math-30: The fallback display of `math/syntax` and `math/unsupported-command` MUST be the source span as literal text, with the diagnostic on the span. [just parity]

## Cell profile form

- math-31: In the cell profile, each construct MUST print the linear form of this table; the cell profile MUST ignore fonts and weights; and the ASCII charset MUST NOT use Unicode superscripts or subscripts. [just parity]

    |Construct|Unicode form|ASCII form|
    |---|---|---|
    |`{a}`|the forms of its content, in order|same|
    |`\frac{a}{b}`|`(a)/(b)`|`(a)/(b)`|
    |`x^{s}`|`x`, then `s` as superscript characters when every character of `s` has a non-zero `sup` in the `scripts` table; else `^(s)`|`x^(s)`|
    |`x_{s}`|`x`, then `s` as subscript characters when every character of `s` has a non-zero `sub` in the `scripts` table; else `_(s)`|`x_(s)`|
    |`\sqrt{x}`|`√(x)`|`sqrt(x)`|
    |`\sqrt[n]{x}`|the superscript form of `n` followed by `√(x)` when every character of `n` has a non-zero `sup` in the `scripts` table; else `[n]√(x)`|`[n]sqrt(x)`|
    |`\sum \prod \int \lim`|`∑ ∏ ∫ lim`; scripts follow the `x^{}` and `x_{}` rules|`sum prod int lim`|
    |`\infty`|`∞`|`inf`|
    |Greek letters|the letter|the command name without the backslash, for example `alpha`|
    |`\pm \times \div \cdot`|`± × ÷ ⋅`|`+- x / .`|
    |`= \le \ge \ne \approx \to \leftarrow \Rightarrow \Leftrightarrow`|`= ≤ ≥ ≠ ≈ → ← ⇒ ⇔`|`= <= >= != ~= -> <- => <=>`|
    |`\left` `\right` delimiters|the delimiter character `( ) [ ] { } \|`; `.` prints nothing|same|
    |`\text{t}`, `\mathbf{}`, `\mathit{}`, `\mathrm{}`|the characters of the argument|same|
    |`\,` `\;` `\quad`|nothing, one space, two spaces|same|

## Property test

- math-32: Go `TestMathLeafBoxes` MUST test, over random well-formed subset terms, that the leaf boxes (glyphs, rules, and paths) of a formula are pairwise disjoint and that each lies inside the formula box; containers (fraction bars around their parts, radical signs around their radicands) MUST NOT be tested for disjointness. [just go-check: TestMathLeafBoxes]
- math-33: Rust `math_leaf_boxes` MUST test the same property, driven by a seeded xorshift32 generator over seeds 1 to 500, so it adds no crate. [just rust-check: math_leaf_boxes]
