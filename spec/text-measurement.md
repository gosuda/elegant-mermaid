# Text measurement

Text measurement gives every string a width and every label its wrapped lines, with the same integers in Go, Rust, and Lean.

## Units and helpers

- text-measurement-01: `round_half_up(a, b)` MUST equal `floor_div(2a + b, 2b)` for `b > 0`, and `ceil_div(a, b)` MUST equal `floor_div(a + b - 1, b)` for `b > 0`; `floor_div` and `floor_mod` are the kernel helpers of `spec/geometry-kernel.md`. [just lean-parity]
- text-measurement-02: A vector measurement MUST be in units of 1/64 px, so 1 px is 64 units, and a cell measurement MUST be in cells. [just lean-parity]
- text-measurement-03: Every measurement formula MUST use integer arithmetic and MUST give the same result in Go, Rust, and Lean; intermediate values MUST be int64; a result outside the int32 range MUST be the kernel overflow error, the same error in all three implementations; and rounding MUST be `floor_div` unless a rule states otherwise. [just lean-parity]

## Roles

- text-measurement-04: Each text item MUST have exactly one role, `body`, `label`, or `title`; the element type MUST set the role by this table; an element type that the table does not list MUST be `body`; and the size and weight of the role MUST be the values of this table. [just lean-parity]

    |Role|Size on line height|Weight|Element types|
    |---|---|---|---|
    |`title`|16 px on 24 px|600|the diagram title|
    |`label`|14 px on 20 px|600|node, edge, group, cluster, actor, axis, and legend text|
    |`body`|14 px on 20 px|400|note and message text, and any text with no other role|

- text-measurement-05: Class and ER members, requirement text, and Markdown paragraphs MUST be `body`. [just lean-parity]

## Vector widths

- text-measurement-06: The vector profile MUST measure with Inter 4.1 from `spec/data/fonts/`: weight 400 MUST read `Inter-Regular.ttf` and weight 600 MUST read `Inter-SemiBold.ttf`, and kerning MUST be ignored. [just gen-check]
- text-measurement-07: The generated `advances` table MUST map each `(weight, codepoint)` to the `hmtx` advance, in font units, of the glyph that the font's `cmap` maps the codepoint to; its rows MUST be `Advance{weight u8, cp u32, units u16}` with weight 0 for Regular and 1 for SemiBold, keyed and sorted by `(weight, cp)`; and each weight MUST also emit its `upem`, the `unitsPerEm` of the `head` table of the same font. [just gen-check]
- text-measurement-08: A codepoint with no table entry MUST have advance `upem` when its East Asian Width is `W` or `F` or when it has `Emoji_Presentation=Yes`, and MUST otherwise have advance `floor_div(6 * upem + 5, 10)`, which is 0.6 em rounded half up; the fallback properties MUST come from `EastAsianWidth.txt` and `emoji-data.txt`. [just lean-parity]
- text-measurement-09: The vector width of a string MUST be `w = ceil_div(sum * size_px * 64, upem)`, where `sum` is the sum of the advances of the string's codepoints in order and `size_px` is the size of its role; the empty string MUST have width 0. [just lean-parity]
- text-measurement-10: In the vector profile, when the config key `fontFamily` is non-empty, the width MUST become `w = floor_div(w * 108, 100)`. [just lean-parity]
- text-measurement-11: Bold runs MUST use the weight 600 advances and italic runs MUST use the weight 400 advances, and the oblique shear MUST NOT change widths; the run syntax is in `spec/math.md`. [just parity]

## Cell widths

- text-measurement-12: The cell profile MUST compute the width of a grapheme cluster from the generated Unicode 18.0.0 tables, and East Asian Ambiguous MUST have width 1. [just lean-parity]
- text-measurement-13: The cluster width rule MUST be: [just lean-parity]

    - 0 when the first scalar has `Grapheme_Cluster_Break` `Extend` or `ZWJ`
    - 2 when the first scalar has East Asian Width `W` or `F` or `Emoji_Presentation=Yes`, when the cluster contains U+FE0F after an `Extended_Pictographic` scalar, or when it contains U+20E3
    - otherwise 1

- text-measurement-14: Output MUST iterate grapheme clusters and MUST never split a cluster; a label cluster that does not fit its row MUST NOT be written and MUST be counted; a count above 0 MUST fail the `no label is truncated` hard constraint of `spec/quality-metrics.md`; and the label placement rule is in `spec/lean-reference.md`. [just quality]
- text-measurement-15: The cell width of a list of clusters MUST be the sum of the cell widths of its clusters, and the cell width of a string MUST be the cell width of `segment s`. [just lean-parity]
- text-measurement-16: Cell width MUST be additive over a concatenation of cluster lists and MUST NOT be assumed additive over scalar strings, because `segment` can merge the last cluster of one part with the first cluster of the next: U+2639 followed by U+FE0F has width 2, while the parts have widths 1 and 0. [just lean-parity]

## Grapheme segmentation

- text-measurement-17: `segment` MUST implement the UAX #29 extended grapheme cluster rules at Unicode 18.0.0, GB1 to GB999, including GB11 (`Extended_Pictographic Extend* ZWJ` before `Extended_Pictographic`), GB12 and GB13 (regional indicator pairs), and GB9c (Indic conjunct break, property `InCB`); no language MUST write its own break rule. [just lean-parity]
- text-measurement-18: GB9c MUST forbid a break when the scalars immediately before the break are one `InCB=Linker` followed by zero or more `InCB=Extend` scalars and the scalar after the break has `InCB=Consonant`; UAX #29 revision 49 writes it as `\p{InCB=Linker} \p{InCB=Extend}* × \p{InCB=Consonant}`. [just lean-parity]
- text-measurement-19: The segmentation inputs MUST be `auxiliary/GraphemeBreakProperty.txt` (GCB), `emoji/emoji-data.txt` (`Emoji_Presentation`, `Extended_Pictographic`), and `DerivedCoreProperties.txt` (`InCB`), held under `spec/data/unicode/`, and `spec/data/SOURCES.json` MUST record the URL and SHA-256 of each file. [just gen-check]
- text-measurement-20: `segment` MUST be one left-to-right pass that keeps the state that GB9c, GB11, GB12, and GB13 need. [just lean-parity]

## Wrapping

- text-measurement-21: The wrapper MUST break at spaces, after hyphens, and between CJK ideographs, and MUST NOT break inside a grapheme cluster. [just lean-parity]
- text-measurement-22: A break opportunity MUST be a space (U+0020), the position after U+002D when the next scalar is an ASCII letter or digit, or the position between two scalars that both have the `Ideographic` property; `Ideographic` MUST be read from `PropList.txt`. [just lean-parity]
- text-measurement-23: Spaces at a break MUST stay on the line before it and MUST be removed from the end of the line. [just lean-parity]
- text-measurement-24: `<br>` MUST force a new line before wrapping starts. [just parity]
- text-measurement-25: The default wrap width MUST be 200 px in the vector profile, which is 12800 units, and 32 cells in the cell profile. [just lean-parity]
- text-measurement-26: Lines MUST fill greedily: a line ends at the last break opportunity that keeps it within the wrap width; when no opportunity fits, the line ends at a cluster boundary; and a single cluster wider than the wrap width MUST be one line that exceeds it. [just lean-parity]

## Wrap classes

- text-measurement-27: A cluster MUST be `space` when it equals U+0020. [just lean-parity]
- text-measurement-28: For clusters `c_0` to `c_(n-1)`, a break opportunity at boundary `i`, between `c_(i-1)` and `c_i`, MUST be one of: [just lean-parity]

    - `S`: a maximal run `c_s` to `c_(t-1)` of `space` clusters with `s > 0` and `t < n`; its end is `e = s`, its next start is `t`, and its separator is the run.
    - `H`: a hyphen break at boundary `i` under the U+002D rule; `e = t = i`, and the separator is empty.
    - `I`: an ideographic break at boundary `i` under the `Ideographic` rule; `e = t = i`, and the separator is empty.

    A maximal run of spaces that ends the input (`t = n`) MUST NOT be an opportunity; it is the separator of the last line.

## The wrap algorithm

- text-measurement-29: The wrap target `L` of a text item MUST be the wrap target that its kind's section states, when the section states one; otherwise `L` MUST be `LayoutOptions.MaxWidth`, in the unit of the profile, when it is non-zero; otherwise `L` MUST be the default wrap width. [just lean-parity]
- text-measurement-30: Each line MUST be measured with the item's role and weight, and `W(i, j)` MUST be the width of clusters `c_i` to `c_(j-1)`. [just lean-parity]
- text-measurement-31: `wrap` MUST repeat these steps, with fuel equal to the cluster count `n`: [just lean-parity]

    1. Let `i` be the start of the current line, starting at 0. Let `j` be the largest index in `i+1 .. n` with `W(i, j) <= L`. If none exists, `j = i+1`.
    2. If `j = n`, emit the line `c_i` to `c_(n-1)`. If that line ends in a `space` run that starts after `i`, that run is the line's separator instead. Stop.
    3. Otherwise, let `e` be the largest opportunity end with `i < e <= j`. If one exists, emit `c_i` to `c_(e-1)` with that opportunity's separator and set `i = t`. If none exists, emit `c_i` to `c_(j-1)` with an empty separator and set `i = j`.

- text-measurement-32: The model stage MUST write the unwrapped text and an empty `lines`, and the measure step MUST fill `lines` with the wrapped texts and their widths; the dump fields are in `spec/model-dump.md`. [just lean-parity]
